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

/* FileStream's DbFile.forceWritten: forces the files written since the
 * last force, for the reason 'why', and nothing if none was. With the
 * switch force (new_file), only the last file can hold such bytes. A
 * failure is the stream's. */
static enum err_code force_written(struct stream *s, enum plat_force_why why, struct err *e) {
    for (int32_t i = s->unforced; i < s->nfiles; i++) {
        enum err_code rc = plat_force(s->files[i].fd, why, e);
        if (rc != ERR_OK) {
            return fail(s, rc);
        }
    }
    s->unforced = s->nfiles;
    return ERR_OK;
}

/* FileStream.checkDirectory (bergdb 021-20, as Java's since release
 * 2026.4): the stream fails if the directory at its path is no longer the
 * one that it took at the open, by its identity (Java's file key): it was
 * deleted, moved or replaced while the stream had it. A file is made and
 * deleted by its name in the directory's path, so a stream whose directory
 * was deleted made its next file in a new database's directory at the
 * path, and broke it, or deleted that database's files at a cut.
 *
 * Called right before each of these steps, with nothing that waits in
 * between, and again after it (bergdb 021-24, as Java's): new_file checked
 * before the switch force, which can take long, so a directory replaced
 * during it got the new file. Left: a replacement in the short window
 * between the check and the step (usually microseconds, longer if the
 * process is paused), as the step opens or deletes the file by its path;
 * the check after it fails the stream before a byte is written there, but
 * the step is done: an empty stream file in the replacement, or, at a
 * cut, the replacement's file of that name deleted. An open there is
 * refused until the empty file is removed, with an error that depends on
 * what else is in the directory, as Java's (021-24's wording, 03ce6ec):
 * BadDirStateException beside stream files of its own; in a directory
 * without others, as a stream without a valid meta block. A directory replaced and put
 * back between the two checks is not seen. The check relies on the stream
 * holding bergdb.lock open from the open until stream_close, which closes
 * it after the files (Java's invariant, bergdb 020-23, V5-1): the old
 * directory's inode is then not reused for a new directory at the path. */
static enum err_code check_directory(struct stream *s, struct err *e) {
    struct plat_dir_key now;
    if (!plat_dir_key(s->dir, &now) || now.dev != s->dir_dev || now.ino != s->dir_ino) {
        return fail(s, err_set(e, ERR_IO, "IOException", "Directory %s is no longer the "
                "database's directory: it was deleted, moved or replaced while the database "
                "had it open. Nothing more is written there.", s->dir));
    }
    return ERR_OK;
}

/* FileStream.newFile: the next file, at the stream's length in the files,
 * a multiple of 100,000; it and then the directory forced before it takes
 * a byte. */
static enum err_code new_file(struct stream *s, struct err *e) {
    char path[4096];
    int fd;
    int64_t length;
    enum err_code rc;

    if (s->fileLength % STREAM_INDEX_UNIT != 0) {
        return fail(s, err_set(e, ERR_IO, "Bug", "Illegal state, length = %lld",
                (long long) s->fileLength));
    }
    /* The old last file forced before the new file's name exists (bergdb
     * 005-47, FileStream.newFile's SWITCH force): a new name may be durable
     * at once, before any force of the directory, and a power loss must
     * not leave a short file before a newer one, which an open refuses
     * (BadDirStateException). So every file before the last is whole and
     * forced. */
    rc = force_written(s, PLAT_FORCE_SWITCH, e);
    if (rc != ERR_OK) {
        return rc;
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
    /* The directory checked right before the file is made, after the switch
     * force, and again after the file's and the directory's forces (bergdb
     * 021-20, 021-24: openForRw's checks). */
    rc = check_directory(s, e);
    if (rc != ERR_OK) {
        return rc;
    }
    rc = plat_open_rw(path, &fd, e);
    if (rc != ERR_OK) {
        return fail(s, rc);
    }
    /* The new file and then the directory forced before the file takes a
     * byte, as Java's openForRw (OPEN), with per-append forcing on or off
     * (bergdb 022-02, D7): else one write of the buffer could make several
     * files with no force of the directory between them, and a file system
     * that made a later name durable before an earlier one would leave a
     * gap in the files, which an open refuses (BadDirStateException). So
     * the name of every file that holds a byte is durable. */
    rc = plat_force(fd, PLAT_FORCE_OPEN, e);
    if (rc == ERR_OK) {
        rc = plat_force_dir(s->dir, e);
    }
    if (rc == ERR_OK) {
        rc = check_directory(s, e);
    }
    /* To make sure no-one just created the file and wrote to it. */
    if (rc == ERR_OK) {
        rc = plat_fd_length(fd, &length, e);
    }
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
    s->nfiles++;
    s->unforced = s->nfiles;    /* the old files by the switch, the new one by its OPEN */
    s->maxSize = FILE_SIZES[s->fileSizeIndex];
    return ERR_OK;
}

/* FileStream.append: n bytes (at least one) to the files, each filled to
 * its capacity, then a new one. */
static enum err_code write_files(struct stream *s, const uint8_t *src, int64_t len,
        struct err *e) {
    enum err_code rc;
    if (s->nfiles == 0) {
        /* The stream's first file, made by its first write, not at the
         * open (bergdb 015-06). */
        rc = new_file(s, e);
        if (rc != ERR_OK) {
            return rc;
        }
    }
    while (true) {
        struct stream_file *k = &s->files[s->nfiles - 1];
        /* DbFile.append. */
        int64_t available = s->maxSize - k->length;
        if (available < 0) {
            return fail(s, err_set(e, ERR_IO, "Bug", "maxSize: %lld, fileLength: %lld",
                    (long long) s->maxSize, (long long) k->length));
        }
        int64_t toAppend = len > available ? available : len;
        /* 130818 Frans: detects another user appending to this file. Java's
         * text, which names the file, with its words as release 2026.4 fixed
         * them (bergdb 020-24-08, U8-9); C's own text named the directory. */
        int64_t rfileLength;
        rc = plat_fd_length(k->fd, &rfileLength, e);
        if (rc == ERR_OK && rfileLength != k->length) {
            rc = err_set(e, ERR_IO, "IOException", "File %s/%014lld%s is not of expected "
                    "length (%lld), but %lld bytes. Was it modified by someone else?", s->dir,
                    (long long) (k->start / STREAM_INDEX_UNIT), SUFFIX,
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
        /* The directory's identity, Java's dirKey, taken before the lock as
         * lockDir takes lockKey(dir) (bergdb 021-20; check_directory). */
        struct plat_dir_key key;
        if (!plat_dir_key(dir, &key)) {
            stream_close(s);
            return err_set(e, ERR_IO, "NoSuchFileException", "%s", dir);
        }
        s->dir_dev = key.dev;
        s->dir_ino = key.ino;
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
                /* openForRw: the last file takes appends up to the capacity.
                 * It and the directory are forced first (OPEN), so that what
                 * a process before wrote and did not force, one that died,
                 * is durable before this one counts it durable or cuts the
                 * files before it (bergdb 005-47; stream_pretruncate). */
                /* The directory checked right before and again after, as
                 * every file that Java's openForRw opens (bergdb 021-24). */
                rc = check_directory(s, e);
                if (rc == ERR_OK) {
                    rc = plat_open_rw(path, &s->files[i].fd, e);
                }
                if (rc == ERR_OK) {
                    rc = plat_force(s->files[i].fd, PLAT_FORCE_OPEN, e);
                }
                if (rc == ERR_OK) {
                    rc = plat_force_dir(dir, e);
                }
                if (rc == ERR_OK) {
                    rc = check_directory(s, e);
                }
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
    /* No bergdb files: none is made here; the first write makes the first
     * (bergdb 015-06), so that a refused creation leaves only the lock
     * file. */
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
    if (s->kind != STREAM_DIR || !s->rw) {
        return ERR_OK;
    }
    /* Also with nothing buffered: a failed stream takes no write and no
     * force, so a sync or a close after a failed force, or a failed delete,
     * gives the failure, as Java's checkIOException, and does not force
     * again and count the stream durable (bergdb 022-05). */
    if (s->failed) {
        return err_set(e, ERR_IO, "IOException", "The stream has failed: no more writes.");
    }
    if (s->buf_len == 0) {
        return ERR_OK;
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
    rc = force_written(s, PLAT_FORCE_SYNC, e);
    if (rc != ERR_OK) {
        return rc;
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

void stream_as_storage(struct stream *s) {
    s->storage = true;
}

enum err_code stream_read(struct stream *s, int64_t pos, uint8_t *buf, int32_t n,
        struct err *e) {
    if (s->storage) {
        /* BufferedStream.read under Db's StorageManager: refused if position
         * > totalLength - length, without the sum (bergdb 021-14, as Java's
         * since release 2026.4): Java's position + length - 1 wrapped for a
         * position within n of Long.MAX_VALUE, and its read went on into the
         * ring buffer's bytes, where C refused it as past the end; and a
         * read of 0 bytes returns after the check, at any position below it
         * (Long.MIN_VALUE's wrapped sum refused it). */
        if (pos > s->length - n) {
            return err_set(e, ERR_IO, "EOFException", "Cannot read %d bytes at position %lld, "
                    "stream size is %lld.", (int) n, (long long) pos, (long long) s->length);
        }
        if (n == 0) {
            return ERR_OK;
        }
    }
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
        if (pos > s->length - n) {     /* without the sum, as Java's since 021-14 */
            return err_set(e, ERR_IO, "EOFException", "Not enough bytes left in the stream, "
                    "position is %lld, length to read is %d and stream size is %lld.",
                    (long long) pos, (int) n, (long long) s->length);
        }
        memcpy(buf, s->bytes + (pos - s->base), (size_t) n);
        return ERR_OK;
    }

    /* The bytes still in the write buffer (BufferedStream.readFromBuffer);
     * pos + n > fileLength without the sum, which wraps near Long.MAX_VALUE
     * (bergdb 021-14): such a read went on to the files and was refused
     * there. */
    if (s->buf_len > 0 && pos > s->fileLength - n && pos >= s->first) {
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

    if (s->nfiles == 0 && pos >= s->first) {
        /* FileStream.read of a stream with no file (bergdb 015-06): empty; 0
         * bytes at 0, and any other read past the end. */
        if (pos == 0 && n == 0) {
            return ERR_OK;
        }
        return err_set(e, ERR_IO, "EOFException", "Cannot read %d bytes at spos %lld, the"
                " stream is empty.", (int) n, (long long) pos);
    }

    /* FileStream.read: the file with the largest start at or before pos, then on. */
    s->file_reads++;
    s->file_read_bytes += n;
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
    const int64_t used = s->length - s->base;
    if (used + n > s->cap) {
        int64_t c2 = s->cap == 0 ? 4096 : s->cap;
        while (c2 < used + n) {
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
        memcpy(s->bytes + used, buf, (size_t) n);
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
    if (length < s->base) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "truncate to %lld, before the "
                "bytes kept at the last cut, %lld", (long long) length, (long long) s->base);
    }
    s->length = length;
    return ERR_OK;
}

/* AppendOnlyStream.pretruncate, reclaim's cut (012-11; 012-02, 9.4). */
enum err_code stream_pretruncate(struct stream *s, int64_t pos, struct err *e) {
    if (s->kind == STREAM_MEMORY) {
        /* CutStream.pretruncate: the first position is pos exactly. */
        if (pos < s->first) {
            return err_set(e, ERR_IO, "IOException", "CutStream: pretruncate to %lld, below "
                    "the earlier cut at %lld", (long long) pos, (long long) s->first);
        }
        if (pos > s->length) {
            return err_set(e, ERR_IO, "IOException", "CutStream: pretruncate to %lld, beyond "
                    "the length %lld", (long long) pos, (long long) s->length);
        }
        s->first = pos;
        /* MemoryStream's arrays: the bytes below the cut's 1,000,000-byte
         * boundary are dropped, and the room is the next appends'. Before
         * (bergdb 022-05), C kept every byte, and a database in memory grew
         * by all it wrote, whatever reclaim cut. */
        const int64_t base = pos / MEMORY_ARRAY_SIZE * MEMORY_ARRAY_SIZE;
        if (base > s->base) {
            memmove(s->bytes, s->bytes + (base - s->base), (size_t) (s->length - base));
            s->base = base;
        }
        return ERR_OK;
    }
    if (!s->rw) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "a stream opened read-only");
    }
    /* FileStream.pretruncate: checkIOException, then the files that end
     * before pos taken off the stream. */
    if (s->failed) {
        return err_set(e, ERR_IO, "IOException", "The stream has failed: no more writes.");
    }
    const int64_t len = s->fileLength;
    if (pos > len) {
        return err_set(e, ERR_ARG, "IllegalArgumentException", "pos > length of stream (%lld).",
                (long long) len);
    }
    /* The last file is kept, as a file that the cut ends in is (bergdb
     * 015-31): a cut at the length took every file and failed the stream
     * with a "Bug". */
    int32_t index = -1;      /* index of last file to delete */
    for (int32_t i = 0; i < s->nfiles - 1; i++) {
        if (s->files[i].start + s->files[i].length - 1 < pos) {
            index = i;
        } else {
            break;
        }
    }
    if (index == -1) {
        return ERR_OK;
    }
    const int32_t newSize = s->nfiles - (index + 1);
    /* Before the deletes, the stream forced up to its length in the files
     * (bergdb 005-47, FileStream.runCuts' CUT force; every name is durable
     * since its file was made, D7): the cut's decision durable before the
     * files it replaces are gone. Nothing to force after
     * reclaim's own force for the cut (cut_if_durable), or after the open's
     * for a start's cut. Then the files are taken off at once (the first
     * position moves now) and deleted, oldest first, the directory forced
     * after each (runCuts, 005-46), in this call: C has no thread of its
     * own. A failure stops the deletes; the files left are before the first
     * position, and the next start cuts again. */
    enum err_code rc = force_written(s, PLAT_FORCE_CUT, e);
    for (int32_t i = 0; i <= index; i++) {
        plat_close(s->files[i].fd);
        if (rc == ERR_OK) {
            /* Right before the delete, after the file's close, and again
             * after it (bergdb 021-20, 021-24: DbFile.delete's). */
            rc = check_directory(s, e);
        }
        if (rc == ERR_OK) {
            char path[4096];
            snprintf(path, sizeof path, "%s/%014lld%s", s->dir,
                    (long long) (s->files[i].start / STREAM_INDEX_UNIT), SUFFIX);
            rc = plat_unlink(path, e);
            if (rc == ERR_OK) {
                rc = check_directory(s, e);
            }
            if (rc == ERR_OK) {
                rc = plat_force_dir(s->dir, e);
            }
        }
    }
    memmove(s->files, s->files + (index + 1), (size_t) newSize * sizeof *s->files);
    s->nfiles = newSize;
    s->unforced = s->unforced > index + 1 ? s->unforced - (index + 1) : 0;
    s->first = s->files[0].start;
    if (rc != ERR_OK) {
        return fail(s, rc);
    }
    return ERR_OK;
}
