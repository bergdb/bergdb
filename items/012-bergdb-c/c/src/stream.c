/* stream: the memory stream and the directory stream; see stream.h. */
#include "stream.h"
#include <stdio.h>
#include <string.h>
#include "plat.h"

#define SUFFIX ".bergdb"
#define SUFFIX_LEN 7
#define MEMORY_ARRAY_SIZE INT64_C(1000000)     /* MemoryStream.ARRAY_SIZE */
#define BAD_DIR "BadDirStateException"

/* FileStream.FILE_SIZES: x5-x4-x5, each a multiple of 100,000. */
static const int64_t FILE_SIZES[STREAM_FILE_SIZES] = {
    INT64_C(200000), INT64_C(1000000), INT64_C(5000000), INT64_C(20000000),
    INT64_C(100000000), INT64_C(500000000), INT64_C(2000000000), INT64_C(10000000000),
    INT64_C(50000000000), INT64_C(200000000000)
};

/* FileStream.LOCK_TEXT, written once, when the lock file is made. */
static const char LOCK_TEXT[] =
        "This directory contains a BergDB database. BergDB locks this file\n"
        "while a database has the directory open. The lock is held by the\n"
        "operating system and ends with the process. Do not delete this file\n"
        "while a database is open.\n";

void stream_open_memory(struct stream *s, struct mem *m) {
    memset(s, 0, sizeof *s);
    s->kind = STREAM_MEMORY;
    s->mem = m;
    s->lock_fd = -1;
}

int64_t stream_first_pos(const struct stream *s) {
    return s->first;
}

int64_t stream_length(const struct stream *s) {
    return s->length;
}

/* FileStream.stringToIndex: leading zeros stripped (one kept if all are),
 * then Long.parseLong of the rest, from 0 to Long.MAX_VALUE / 100,000.
 * Long.parseLong takes an optional '+' or '-' and decimal digits, at least
 * one; it refuses a value out of the long's range. */
static bool string_to_index(const char *s, size_t len, int64_t *out) {
    size_t zeros = 0;
    while (zeros < len && s[zeros] == '0') {
        zeros++;
    }
    if (zeros == len && len > 0) {
        zeros--;
    }
    s += zeros;
    len -= zeros;

    bool negative = false;
    size_t i = 0;
    if (len > 0 && (s[0] == '+' || s[0] == '-')) {
        negative = s[0] == '-';
        i = 1;
    }
    if (i == len) {
        return false;           /* "", "+" or "-": NumberFormatException */
    }
    /* Accumulated negatively, as Long.parseLong does, so that MIN fits. */
    int64_t result = 0;
    for (; i < len; i++) {
        if (s[i] < '0' || s[i] > '9') {
            return false;
        }
        int64_t digit = s[i] - '0';
        if (result < INT64_MIN / 10 || result * 10 < INT64_MIN + digit) {
            return false;       /* out of range */
        }
        result = result * 10 - digit;
    }
    if (!negative) {
        if (result == INT64_MIN) {
            return false;
        }
        result = -result;
    }
    if (result < 0 || result > INT64_MAX / STREAM_INDEX_UNIT) {
        return false;
    }
    *out = result;
    return true;
}

static void close_files(struct stream *s) {
    for (int32_t i = 0; i < s->nfiles; i++) {
        plat_close(s->files[i].fd);
    }
    mem_free(s->mem, s->files, (size_t) s->files_cap * sizeof *s->files, MEM_BUFFER);
    s->files = NULL;
    s->nfiles = 0;
    s->files_cap = 0;
}

/* FileStream.determineFileSizeIndexFromFiles: the smallest capacity at or
 * above the larger of the last two files' lengths. */
static int32_t size_index_from_files(const int64_t *lengths, int32_t n) {
    if (n == 0) {
        return 0;
    }
    int64_t fileSize = lengths[n - 1];
    if (n > 1) {
        fileSize = fileSize > lengths[n - 2] ? fileSize : lengths[n - 2];
    }
    int32_t index = STREAM_FILE_SIZES - 1;     /* max */
    for (int32_t i = STREAM_FILE_SIZES - 1; i >= 0; i--) {
        if (FILE_SIZES[i] < fileSize) {
            break;
        }
        index = i;
    }
    return index;
}

/* FileStream.determineFileSizeIndex, without the test setting max2G. */
static int32_t size_index(int32_t currentFileSizeIndex, int64_t streamLength,
        int64_t streamSize) {
    int64_t currentSize = FILE_SIZES[currentFileSizeIndex];
    int64_t size = streamSize / 4;
    int64_t foundSize = FILE_SIZES[0];
    int32_t foundIndex = 0;
    int32_t result = currentFileSizeIndex;

    for (int32_t i = 1; i < STREAM_FILE_SIZES; i++) {
        int64_t x = FILE_SIZES[i];
        if (x <= size) {
            foundSize = x;
            foundIndex = i;
        } else {
            break;
        }
    }

    if (foundIndex != currentFileSizeIndex) {
        if (foundSize > currentSize) {
            bool isMaxIndex = currentFileSizeIndex == STREAM_FILE_SIZES - 1;
            if (!isMaxIndex) {
                int64_t oneUpSize = FILE_SIZES[currentFileSizeIndex + 1];
                if (streamLength % oneUpSize == 0) {
                    result = foundIndex;
                }
            }
        } else {
            result = foundIndex;
        }
    }
    return result;
}

static enum err_code fail(struct stream *s, enum err_code rc) {
    s->failed = true;
    return rc;
}

/* FileStream.newFile: the next file, at the stream's length in the files,
 * a multiple of 100,000. */
static enum err_code new_file(struct stream *s, struct err *e) {
    char path[4096];
    int fd;
    int64_t length;
    enum err_code rc;

    if (s->fileLength % STREAM_INDEX_UNIT != 0) {
        return fail(s, err_set(e, ERR_IO, "Bug", "Illegal state, length = %lld",
                (long long) s->fileLength));
    }
    int64_t index = s->fileLength / STREAM_INDEX_UNIT;
    snprintf(path, sizeof path, "%s/%014lld%s", s->dir, (long long) index, SUFFIX);

    /* applyFileSizeChangeRules. */
    s->fileSizeIndex = size_index(s->fileSizeIndex, s->fileLength, s->fileLength - s->first);

    if (s->nfiles == s->files_cap) {
        int32_t c2 = s->files_cap == 0 ? 8 : 2 * s->files_cap;
        struct stream_file *f2 = mem_realloc(s->mem, s->files,
                (size_t) s->files_cap * sizeof *f2, (size_t) c2 * sizeof *f2, MEM_BUFFER);
        if (f2 == NULL) {
            return fail(s, err_set(e, ERR_NOMEM, "OutOfMemoryError", "a new file"));
        }
        s->files = f2;
        s->files_cap = c2;
    }
    rc = plat_open_rw(path, &fd, e);
    if (rc != ERR_OK) {
        return fail(s, rc);
    }
    /* To make sure no-one just created the file and wrote to it. */
    rc = plat_fd_length(fd, &length, e);
    if (rc == ERR_OK && length != 0) {
        rc = err_set(e, ERR_IO, "IOException", "File %s already exists and has length %lld.",
                path, (long long) length);
    }
    if (rc != ERR_OK) {
        plat_close(fd);
        return fail(s, rc);
    }
    if (s->nfiles == 0) {
        s->first = s->fileLength;
    }
    s->files[s->nfiles].start = s->fileLength;
    s->files[s->nfiles].length = 0;
    s->files[s->nfiles].fd = fd;
    if (s->unforced > s->nfiles) {
        s->unforced = s->nfiles;
    }
    s->nfiles++;
    s->maxSize = FILE_SIZES[s->fileSizeIndex];
    s->dir_unforced = true;
    return ERR_OK;
}

/* FileStream.append: n bytes to the files, each filled to its capacity,
 * then a new one. */
static enum err_code write_files(struct stream *s, const uint8_t *src, int64_t len,
        struct err *e) {
    enum err_code rc;
    while (true) {
        struct stream_file *k = &s->files[s->nfiles - 1];
        /* DbFile.append. */
        int64_t available = s->maxSize - k->length;
        if (available < 0) {
            return fail(s, err_set(e, ERR_IO, "Bug", "maxSize: %lld, fileLength: %lld",
                    (long long) s->maxSize, (long long) k->length));
        }
        int64_t toAppend = len > available ? available : len;
        /* 130818 Frans: detects another user appending to this file. */
        int64_t rfileLength;
        rc = plat_fd_length(k->fd, &rfileLength, e);
        if (rc == ERR_OK && rfileLength != k->length) {
            rc = err_set(e, ERR_IO, "IOException", "A file of %s is not of expected length "
                    "(%lld), but %lld bytes. Was is modified by someone else?", s->dir,
                    (long long) k->length, (long long) rfileLength);
        }
        if (rc == ERR_OK && toAppend > 0) {
            rc = plat_pwrite(k->fd, k->length, src, toAppend, e);
            if (s->unforced > s->nfiles - 1) {
                s->unforced = s->nfiles - 1;
            }
        }
        if (rc != ERR_OK) {
            return fail(s, rc);
        }
        k->length += toAppend;
        s->fileLength += toAppend;
        len -= toAppend;
        src += toAppend;
        if (len == 0) {
            return ERR_OK;
        }
        rc = new_file(s, e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
}

static enum err_code open_dir(struct stream *s, const char *dir, bool rw, int32_t buffer_capacity,
        struct mem *m, struct err *e) {
    struct plat_entry *all = NULL;
    int32_t nall = 0;
    int32_t n = 0;
    char path[4096];
    enum err_code rc;

    memset(s, 0, sizeof *s);
    s->kind = STREAM_DIR;
    s->mem = m;
    s->lock_fd = -1;
    s->rw = rw;
    if (rw) {
        size_t dlen = strlen(dir);
        s->buf_cap = buffer_capacity == 0 ? STREAM_BUFFER_SIZE : buffer_capacity;
        if (s->buf_cap < 100) {
            return err_set(e, ERR_ARG, "IllegalArgumentException",
                    "bufferCapacity too small, %d.", (int) s->buf_cap);
        }
        if (dlen + 32 >= sizeof path) {
            return err_set(e, ERR_IO, "IOException", "Directory path too long: %s", dir);
        }
        /* createDirIfNeeded, lockDir. */
        rc = plat_mkdirs(dir, e);
        if (rc != ERR_OK) {
            return rc;
        }
        s->dir_size = (int64_t) dlen + 1;
        s->dir = mem_alloc(m, (size_t) s->dir_size, MEM_STATE);
        if (s->dir == NULL) {
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "opening %s", dir);
        }
        memcpy(s->dir, dir, dlen + 1);
        rc = plat_lock(dir, STREAM_LOCK_NAME, LOCK_TEXT, STREAM_LOCK_POS, &s->lock_fd, e);
        if (rc != ERR_OK) {
            stream_close(s);
            return rc;
        }
    }

    /* getSortedDbFiles: the entries whose names end with ".bergdb", by name. */
    rc = plat_list_dir(dir, m, &all, &nall, e);
    if (rc != ERR_OK) {
        if (rw) {
            stream_close(s);
        }
        return rc;
    }
    for (int32_t i = 0; i < nall; i++) {
        size_t len = strlen(all[i].name);
        if (len >= SUFFIX_LEN && strcmp(all[i].name + len - SUFFIX_LEN, SUFFIX) == 0) {
            all[n++] = all[i];
        }
    }

    /* checkDbFiles. */
    int64_t current = 0;
    for (int32_t i = 0; i < n; i++) {
        const char *name = all[i].name;
        size_t len = strlen(name);
        int64_t index;
        if (!(len > SUFFIX_LEN) || !string_to_index(name, len - SUFFIX_LEN, &index)) {
            rc = err_set(e, ERR_FORMAT, BAD_DIR, "Bad name of bergdb file: %s/%s.", dir, name);
            goto fail;
        }
        int64_t fileSpos = index * STREAM_INDEX_UNIT;
        if (i == 0) {
            current = fileSpos;
        } else if (current != fileSpos) {
            rc = err_set(e, ERR_FORMAT, BAD_DIR, "Existing files in dir %s are not in a correct"
                    " state. File %s/%s has a filename with an index value that does not match"
                    " the previous file sizes. currentSpos: %lld, fileSpos: %lld", dir, dir, name,
                    (long long) current, (long long) fileSpos);
            goto fail;
        }
        int64_t fLength = all[i].size;
        if (i != n - 1 && fLength % STREAM_INDEX_UNIT != 0) {
            rc = err_set(e, ERR_FORMAT, BAD_DIR, "Bad size of file %s/%s, should have been a"
                    " multiple of 100000, but was %lld.", dir, name, (long long) fLength);
            goto fail;
        }
        current += fLength;
    }

    /* determineFileSizeIndexFromFiles, from the lengths of the listing
     * (File.length()). */
    if (rw) {
        int64_t lengths[2] = { 0, 0 };
        int32_t k = 0;
        for (int32_t i = n >= 2 ? n - 2 : 0; i < n; i++) {
            lengths[k++] = all[i].size;
        }
        s->fileSizeIndex = size_index_from_files(lengths, k);
    }

    /* createDbFileObjects; read-only, no file is created for an empty
     * directory. */
    if (n > 0) {
        s->files = mem_zalloc(m, (size_t) n * sizeof *s->files, MEM_BUFFER);
        if (s->files == NULL) {
            rc = err_set(e, ERR_NOMEM, "OutOfMemoryError", "opening %s", dir);
            goto fail;
        }
        s->files_cap = n;
        for (int32_t i = 0; i < n; i++) {
            s->files[i].fd = -1;
        }
        s->nfiles = n;
        int64_t start = 0;
        for (int32_t i = 0; i < n; i++) {
            const char *name = all[i].name;
            if (i == 0) {
                int64_t index = 0;
                string_to_index(name, strlen(name) - SUFFIX_LEN, &index);
                start = index * STREAM_INDEX_UNIT;
                s->first = start;
            }
            snprintf(path, sizeof path, "%s/%s", dir, name);
            if (rw && i == n - 1) {
                /* openForRw: the last file takes appends up to the capacity. */
                rc = plat_open_rw(path, &s->files[i].fd, e);
                if (rc == ERR_OK) {
                    rc = plat_fd_length(s->files[i].fd, &s->files[i].length, e);
                }
                s->maxSize = FILE_SIZES[s->fileSizeIndex];
            } else {
                rc = plat_open_read(path, &s->files[i].fd, e);
                s->files[i].length = plat_file_length(path);
            }
            if (rc != ERR_OK) {
                goto fail;
            }
            s->files[i].start = start;
            start += s->files[i].length;
        }
        s->length = start;
    }
    plat_free_entries(m, all, nall);
    all = NULL;
    nall = 0;
    s->fileLength = s->length;
    s->durable = s->length;
    s->unforced = s->nfiles;
    if (rw && n == 0) {
        /* Special case, no bergdb files: one is made. */
        rc = new_file(s, e);
        if (rc != ERR_OK) {
            goto fail;
        }
    }
    return ERR_OK;

fail:
    plat_free_entries(m, all, nall);
    if (rw) {
        stream_close(s);
    } else {
        close_files(s);
    }
    s->first = 0;
    s->length = 0;
    return rc;
}

enum err_code stream_open_dir(struct stream *s, const char *dir, struct mem *m, struct err *e) {
    return open_dir(s, dir, false, 0, m, e);
}

int32_t stream_file_size_index(int32_t current, int64_t streamLength, int64_t streamSize) {
    return size_index(current, streamLength, streamSize);
}

enum err_code stream_open_dir_rw(struct stream *s, const char *dir, int32_t buffer_capacity,
        struct mem *m, struct err *e) {
    return open_dir(s, dir, true, buffer_capacity, m, e);
}

enum err_code stream_append(struct stream *s, const uint8_t *src, int64_t n, struct err *e) {
    if (s->kind == STREAM_MEMORY) {
        return stream_append_memory(s, src, n, e);
    }
    if (!s->rw) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "The stream is read-only.");
    }
    if (s->failed) {
        return err_set(e, ERR_IO, "IOException", "The stream has failed: no more writes.");
    }
    if (s->buf == NULL && n > 0) {
        s->buf = mem_alloc(s->mem, (size_t) s->buf_cap, MEM_BUFFER);
        if (s->buf == NULL) {
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a write buffer of %d bytes",
                    (int) s->buf_cap);
        }
    }
    while (n > 0) {
        int64_t room = s->buf_cap - s->buf_len;
        int64_t k = n < room ? n : room;
        memcpy(s->buf + s->buf_len, src, (size_t) k);
        s->buf_len += (int32_t) k;
        s->length += k;
        src += k;
        n -= k;
        if (s->buf_len == s->buf_cap) {
            enum err_code rc = stream_flush(s, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }
    }
    return ERR_OK;
}

enum err_code stream_flush(struct stream *s, struct err *e) {
    if (s->kind != STREAM_DIR || !s->rw || s->buf_len == 0) {
        return ERR_OK;
    }
    if (s->failed) {
        return err_set(e, ERR_IO, "IOException", "The stream has failed: no more writes.");
    }
    enum err_code rc = write_files(s, s->buf, s->buf_len, e);
    if (rc != ERR_OK) {
        return rc;
    }
    s->buf_len = 0;
    return ERR_OK;
}

enum err_code stream_sync(struct stream *s, struct err *e) {
    if (s->kind != STREAM_DIR || !s->rw) {
        return ERR_OK;
    }
    enum err_code rc = stream_flush(s, e);
    if (rc != ERR_OK) {
        return rc;
    }
    for (int32_t i = s->unforced; i < s->nfiles; i++) {
        rc = plat_force(s->files[i].fd, e);
        if (rc != ERR_OK) {
            return fail(s, rc);
        }
    }
    s->unforced = s->nfiles;
    if (s->dir_unforced) {
        rc = plat_force_dir(s->dir, e);
        if (rc != ERR_OK) {
            return fail(s, rc);
        }
        s->dir_unforced = false;
    }
    s->durable = s->length;
    return ERR_OK;
}

int64_t stream_durable_length(const struct stream *s) {
    return s->kind == STREAM_DIR && s->rw ? s->durable : s->length;
}

enum err_code stream_finish(struct stream *s, struct err *e) {
    enum err_code rc = stream_sync(s, e);
    stream_close(s);
    return rc;
}

void stream_close(struct stream *s) {
    if (s->kind == STREAM_DIR) {
        close_files(s);
        if (s->rw) {
            plat_close(s->lock_fd);
            s->lock_fd = -1;
            mem_free(s->mem, s->buf, (size_t) s->buf_cap, MEM_BUFFER);
            s->buf = NULL;
            s->buf_len = 0;
            mem_free(s->mem, s->dir, (size_t) s->dir_size, MEM_STATE);
            s->dir = NULL;
            s->rw = false;
        }
    } else {
        mem_free(s->mem, s->bytes, (size_t) s->cap, MEM_BUFFER);
        s->bytes = NULL;
        s->cap = 0;
    }
    s->length = 0;
    s->first = 0;
}

enum err_code stream_read(struct stream *s, int64_t pos, uint8_t *buf, int32_t n,
        struct err *e) {
    if (s->kind == STREAM_MEMORY) {
        /* MemoryStream.read, its checks in order. */
        if (pos < 0) {
            return err_set(e, ERR_ARG, "IllegalArgumentException",
                    "Negative position not allowed, %lld.", (long long) pos);
        }
        if (n == 0) {
            return ERR_OK;
        }
        if (pos < s->first) {
            return err_set(e, ERR_NOT_AVAILABLE, "ReadBelowFirstPosException",
                    "Cannot read from position %lld, first valid position is %lld.",
                    (long long) pos, (long long) s->first);
        }
        if (pos > s->length - n) {     /* Java's pos + len > size, without its overflow */
            return err_set(e, ERR_IO, "EOFException", "Not enough bytes left in the stream, "
                    "position is %lld, length to read is %d and stream size is %lld.",
                    (long long) pos, (int) n, (long long) s->length);
        }
        memcpy(buf, s->bytes + pos, (size_t) n);
        return ERR_OK;
    }

    /* The bytes still in the write buffer (BufferedStream.readFromBuffer). */
    if (s->buf_len > 0 && pos + n > s->fileLength && pos >= s->first) {
        if (pos > s->length - n) {
            return err_set(e, ERR_IO, "EOFException", "Cannot read %d bytes at spos %lld, the"
                    " end of the stream.", (int) n, (long long) pos);
        }
        int64_t from = pos > s->fileLength ? pos : s->fileLength;
        memcpy(buf + (from - pos), s->buf + (from - s->fileLength), (size_t) (pos + n - from));
        n = (int32_t) (from - pos);
        if (n == 0) {
            return ERR_OK;
        }
    }

    /* FileStream.read: the file with the largest start at or before pos, then on. */
    while (true) {
        int32_t k = -1;
        for (int32_t i = 0; i < s->nfiles; i++) {
            if (s->files[i].start <= pos) {
                k = i;
            } else {
                break;
            }
        }
        if (k < 0) {
            if (pos < s->first) {
                return err_set(e, ERR_NOT_AVAILABLE, "ReadBelowFirstPosException",
                        "Cannot read at spos %lld, below the first position, %lld.",
                        (long long) pos, (long long) s->first);
            }
            return err_set(e, ERR_IO, "IOException", "No file found for reading at spos %lld.",
                    (long long) pos);
        }
        struct stream_file *f = &s->files[k];
        /* DbFile.read. */
        if (pos > f->start + f->length) {
            return err_set(e, ERR_IO, "EOFException", "Cannot read at spos %lld, past the end "
                    "of a file at %lld.", (long long) pos, (long long) (f->start + f->length));
        }
        int64_t fileOffset = pos - f->start;
        int64_t actual = n > f->length - fileOffset ? f->length - fileOffset : n;
        if (actual == 0 && n > 0) {
            return err_set(e, ERR_IO, "EOFException", "Cannot read %d bytes at spos %lld, the"
                    " end of the stream.", (int) n, (long long) pos);
        }
        if (actual > 0) {
            enum err_code rc = plat_pread(f->fd, fileOffset, buf, (int32_t) actual, e);
            if (rc != ERR_OK) {
                return rc;
            }
        }
        if (actual == n) {
            return ERR_OK;
        }
        pos += actual;
        buf += actual;
        n -= (int32_t) actual;
    }
}

enum err_code stream_append_memory(struct stream *s, const uint8_t *buf, int64_t n,
        struct err *e) {
    if (s->length + n > s->cap) {
        int64_t c2 = s->cap == 0 ? 4096 : s->cap;
        while (c2 < s->length + n) {
            c2 *= 2;
        }
        uint8_t *b2 = mem_realloc(s->mem, s->bytes, (size_t) s->cap, (size_t) c2, MEM_BUFFER);
        if (b2 == NULL) {
            return err_set(e, ERR_NOMEM, "OutOfMemoryError", "a memory stream of %lld bytes",
                    (long long) c2);
        }
        s->bytes = b2;
        s->cap = c2;
    }
    if (n > 0) {
        memcpy(s->bytes + s->length, buf, (size_t) n);
    }
    s->length += n;
    return ERR_OK;
}

enum err_code stream_pretruncate_memory(struct stream *s, int64_t pos, struct err *e) {
    if (pos < 0) {
        return err_set(e, ERR_ARG, "IllegalArgumentException",
                "Bad spos, cannot be neg, was %lld.", (long long) pos);
    }
    if (pos > s->length) {
        return err_set(e, ERR_ARG, "IllegalArgumentException",
                "spos > length of stream, %lld > %lld.", (long long) pos, (long long) s->length);
    }
    int64_t first = pos / MEMORY_ARRAY_SIZE * MEMORY_ARRAY_SIZE;
    if (first > s->first) {
        s->first = first;
    }
    return ERR_OK;
}

enum err_code stream_truncate_memory(struct stream *s, int64_t length, struct err *e) {
    if (length > s->length) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "newLength larger than current "
                "length, %lld > %lld.", (long long) length, (long long) s->length);
    }
    s->length = length;
    return ERR_OK;
}
