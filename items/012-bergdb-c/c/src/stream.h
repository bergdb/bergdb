/*
 * stream: an append-only stream, Java's bergdb.stream.AppendOnlyStream, in
 * two implementations behind one header (bergdb 012-06): a memory stream,
 * Java's MemoryStream, for tests; and a database directory, Java's
 * FileStream: the .bergdb files found, checked and ordered as Java does,
 * and reads at any position, across files. Prefix stream_.
 *
 * Read-only in 012-06: a directory is opened as it is, with no lock, and
 * an empty one is an empty stream (Java's FileStream creates its first file
 * and the directory; 012-09 writes). Appends to files come in 012-09,
 * cuts (pretruncate) in 012-11. The memory stream takes raw appends and a
 * pretruncate already, which the tests use to make streams.
 *
 * One caller at a time (012-01, 4.2), so none of Java's synchronization.
 */
#ifndef BERGDB_STREAM_H
#define BERGDB_STREAM_H

#include <stdint.h>
#include "err.h"
#include "mem.h"

/* FileStream's BYTES_PER_INDEX_UNIT: a file's name is its first position
 * divided by it. */
#define STREAM_INDEX_UNIT INT64_C(100000)

enum stream_kind { STREAM_MEMORY, STREAM_DIR };

/* A .bergdb file of a directory: its first position, its length (at the
 * open, as File.length()) and its descriptor. */
struct stream_file {
    int64_t start;
    int64_t length;
    int fd;
};

struct stream {
    enum stream_kind kind;
    struct mem *mem;
    int64_t first;          /* getFirstPos() */
    int64_t length;         /* getLength() */
    /* STREAM_MEMORY: the bytes from position 0 to length. */
    uint8_t *bytes;
    int64_t cap;
    /* STREAM_DIR: the files, by their first positions. */
    struct stream_file *files;
    int32_t nfiles;
};

/* An empty memory stream. Nothing is allocated until an append. */
void stream_open_memory(struct stream *s, struct mem *m);

/* Opens directory 'dir' as Java's FileStream reads it
 * (FileStream.handleExistingFiles, checkDbFiles, getSortedDbFiles,
 * createDbFileObjects): every entry whose name ends with ".bergdb", sorted
 * by name; each name, without the suffix, must be a number from 0 to
 * Long.MAX_VALUE / 100,000 (FileStream.stringToIndex: leading zeros
 * stripped, then Long.parseLong, which takes a sign), and its file's first
 * position is that number times 100,000; the first file's is the stream's
 * first position; each next file must start where the one before it ends;
 * every file but the last must have a length that is a multiple of
 * 100,000. Refused as Java refuses, with ERR_FORMAT and
 * "BadDirStateException": "Bad name of bergdb file", "are not in a correct
 * state", "Bad size of file". ERR_IO if the directory or a file cannot be
 * read (a missing directory too: Java creates it, 012-09). Java's
 * Long.parseLong also takes non-ASCII decimal digits in a name; C does not
 * (a name Java never writes). On a failure nothing stays open. */
enum err_code stream_open_dir(struct stream *s, const char *dir, struct mem *m, struct err *e);

/* Closes the files and frees what the stream holds. */
void stream_close(struct stream *s);

int64_t stream_first_pos(const struct stream *s);
int64_t stream_length(const struct stream *s);

/* Reads n bytes at position pos into buf (AppendOnlyStream.read), as
 * Java's implementations refuse: a negative position (MemoryStream:
 * ERR_ARG, "IllegalArgumentException"), one below the first position
 * (ERR_NOT_AVAILABLE, "ReadBelowFirstPosException"), and bytes past the
 * end (ERR_IO, "EOFException"). n may be 0. */
enum err_code stream_read(struct stream *s, int64_t pos, uint8_t *buf, int32_t n,
        struct err *e);

/* Appends n bytes to a memory stream (MemoryStream.append). ERR_NOMEM. */
enum err_code stream_append_memory(struct stream *s, const uint8_t *buf, int64_t n,
        struct err *e);

/* MemoryStream.pretruncate: positions before 'pos' are no longer read. As
 * Java's, the first position moves to 'pos' rounded down to a multiple of
 * 1,000,000 (its arrays' size), if that is after it. ERR_ARG for a negative
 * position or one past the length. */
enum err_code stream_pretruncate_memory(struct stream *s, int64_t pos, struct err *e);

/* Cuts a memory stream to 'length' bytes (MemoryStream.truncate), for
 * crash tests. ERR_ARG if it is longer than the stream. */
enum err_code stream_truncate_memory(struct stream *s, int64_t length, struct err *e);

#endif
