/* stream: the memory stream and the directory stream; see stream.h. */
#include "stream.h"
#include <stdio.h>
#include <string.h>
#include "plat.h"

#define SUFFIX ".bergdb"
#define SUFFIX_LEN 7
#define MEMORY_ARRAY_SIZE INT64_C(1000000)     /* MemoryStream.ARRAY_SIZE */
#define BAD_DIR "BadDirStateException"

void stream_open_memory(struct stream *s, struct mem *m) {
    memset(s, 0, sizeof *s);
    s->kind = STREAM_MEMORY;
    s->mem = m;
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
    mem_free(s->mem, s->files, (size_t) s->nfiles * sizeof *s->files, MEM_BUFFER);
    s->files = NULL;
    s->nfiles = 0;
}

enum err_code stream_open_dir(struct stream *s, const char *dir, struct mem *m, struct err *e) {
    struct plat_entry *all = NULL;
    int32_t nall = 0;
    int32_t n = 0;
    char path[4096];
    enum err_code rc;

    memset(s, 0, sizeof *s);
    s->kind = STREAM_DIR;
    s->mem = m;

    /* getSortedDbFiles: the entries whose names end with ".bergdb", by name. */
    rc = plat_list_dir(dir, m, &all, &nall, e);
    if (rc != ERR_OK) {
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

    /* createDbFileObjects, read-only: no file is created for an empty directory. */
    if (n > 0) {
        s->files = mem_zalloc(m, (size_t) n * sizeof *s->files, MEM_BUFFER);
        if (s->files == NULL) {
            rc = err_set(e, ERR_NOMEM, "OutOfMemoryError", "opening %s", dir);
            goto fail;
        }
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
            rc = plat_open_read(path, &s->files[i].fd, e);
            if (rc != ERR_OK) {
                goto fail;
            }
            s->files[i].start = start;
            s->files[i].length = plat_file_length(path);
            start += s->files[i].length;
        }
        s->length = start;
    }
    plat_free_entries(m, all, nall);
    return ERR_OK;

fail:
    plat_free_entries(m, all, nall);
    close_files(s);
    s->first = 0;
    s->length = 0;
    return rc;
}

void stream_close(struct stream *s) {
    if (s->kind == STREAM_DIR) {
        close_files(s);
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
