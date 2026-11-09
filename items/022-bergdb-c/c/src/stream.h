/*
 * stream: an append-only stream, Java's bergdb.stream.AppendOnlyStream, in
 * two implementations behind one header (bergdb 012-06): a memory stream,
 * Java's MemoryStream, for tests; and a database directory, Java's
 * FileStream: the .bergdb files found, checked and ordered as Java does,
 * and reads at any position, across files. Prefix stream_.
 *
 * A directory is opened read-only (stream_open_dir, 012-06: as it is, with
 * no lock, and an empty one is an empty stream) or for writing
 * (stream_open_dir_rw, 012-09: as Java's FileStream opens it, the
 * directory made if missing, its lock taken, no file made in an empty one
 * until the first write (015-06), and the last file taking appends up to
 * the capacity that the open rule gives it). Reclaim's cut is
 * stream_pretruncate (012-11). The memory
 * stream takes raw appends and a pretruncate, which the tests use to make
 * streams.
 *
 * The write buffer (012-01, 4.3): what Java's BufferedStream and its
 * thread do, without a thread. An append goes to the buffer; the buffer is
 * written to the files (FileStream.append: each file filled to its
 * capacity, then a new file) when it is full, at stream_flush and at
 * stream_sync, which then forces the files written since the last force,
 * with F_FULLFSYNC (plat). Reads see
 * the buffered bytes. The bytes and the files are Java's; only when they
 * reach the disk differs. A close writes nothing: stream_sync first
 * (stream_finish does both), as Java's close writes and forces what the
 * buffer holds. The other forces are those of Java's FileStream with
 * per-append forcing off (bergdb 005-47), so that a power loss leaves a
 * prefix of the stream across its files: the last file and the directory
 * at an open for writing (OPEN), the last file before a new file (SWITCH),
 * each new file and the directory before the file takes a byte (OPEN, as
 * Java's; bergdb 022-02, D7), and the files written since the last force
 * before a cut's deletes (CUT).
 *
 * One caller at a time (012-01, 4.2), so none of Java's synchronization.
 */
#ifndef BERGDB_STREAM_H
#define BERGDB_STREAM_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"

/* FileStream's BYTES_PER_INDEX_UNIT: a file's name is its first position
 * divided by it. */
#define STREAM_INDEX_UNIT INT64_C(100000)

enum stream_kind { STREAM_MEMORY, STREAM_DIR };

/* A .bergdb file of a directory: its first position, its length (at the
 * open, as File.length(), and as written since) and its descriptor (read
 * and write for the last file of a stream opened for writing). */
struct stream_file {
    int64_t start;
    int64_t length;
    int fd;
};

/* FileStream.FILE_SIZES: the capacities of new files, 200 kB to 200 GB. */
#define STREAM_FILE_SIZES 10

/* StorageManager.DEFAULT_BUFFER_SIZE: the write buffer's default size. */
#define STREAM_BUFFER_SIZE 10000000

/* The lock file and the locked byte (FileStream.LOCK_NAME, LOCK_POS). */
#define STREAM_LOCK_NAME "bergdb.lock"
#define STREAM_LOCK_POS (INT64_C(1) << 62)

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
    /* STREAM_DIR opened for writing (stream_open_dir_rw). */
    bool rw;
    int32_t files_cap;      /* the files array's capacity */
    char *dir;              /* the directory's path, for new files */
    int64_t dir_size;       /* its allocation */
    int lock_fd;            /* holds the directory's lock */
    int32_t fileSizeIndex;  /* FileStream.fileSizeIndex: the last file's capacity */
    int64_t maxSize;        /* the last file's capacity, FILE_SIZES[fileSizeIndex] at its
                               making or the open */
    int64_t fileLength;     /* FileStream.length: the bytes in the files */
    uint8_t *buf;           /* the write buffer: the bytes from fileLength on */
    int32_t buf_cap;
    int32_t buf_len;
    int32_t unforced;       /* the first file written since the last force; nfiles if none */
    int64_t durable;        /* the length at the last force */
    bool failed;            /* an I/O error: FileStream's ioException, every write refused */
    /* The reads of a directory's files (012-10: what a start reads), as a stream
     * below Java's BufferedStream counts them: the calls that reach the files
     * (a read served by the write buffer alone is not one) and their bytes. */
    int64_t file_reads;
    int64_t file_read_bytes;
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

/* Opens directory 'dir' for writing, as Java's FileStream(dir) does:
 *
 *   - createDirIfNeeded: made with its missing ancestors if it does not
 *     exist (each forced), else its parent forced (plat_mkdirs);
 *   - lockDir: bergdb.lock made with FileStream.LOCK_TEXT if missing, and
 *     its byte at 2^62 locked (plat_lock; ERR_IN_USE,
 *     "DirectoryInUseException", if another process holds it);
 *   - handleExistingFiles: the files checked as stream_open_dir checks
 *     them; the capacity index from the larger of the last two files'
 *     lengths, the smallest of FILE_SIZES at or above it
 *     (determineFileSizeIndexFromFiles: so a restart can change the layout
 *     from there on, 012-02, 9.3, C1); the last file opened for writing up
 *     to that capacity, and forced, then the directory (openForRw's OPEN
 *     force, 005-47: what a process that died wrote is durable before this
 *     one counts it); in an empty directory no file, and the index 0: the
 *     first write makes 00000000000000.bergdb (015-06), so that an open
 *     closed before one leaves only bergdb.lock.
 *
 * buffer_capacity: the write buffer's size, at least 100
 * (BufferedStream's minimum); 0 for STREAM_BUFFER_SIZE. It is allocated
 * at the first append. On a failure nothing stays open. */
enum err_code stream_open_dir_rw(struct stream *s, const char *dir, int32_t buffer_capacity,
        struct mem *m, struct err *e);

/* Appends n bytes (AppendOnlyStream.append): to a memory stream as
 * stream_append_memory; to a directory opened for writing, into the write
 * buffer, which is written to the files each time it is full. ERR_ARG for
 * a read-only directory; ERR_IO after an I/O error, which every later
 * write gives too (FileStream.checkIOException); ERR_NOMEM. */
enum err_code stream_append(struct stream *s, const uint8_t *buf, int64_t n, struct err *e);

/* Writes the buffer to the files (FileStream.append): the first file made
 * if there is none (015-06), each file filled to its capacity, then a new
 * file (FileStream.newFile: named by its first position over 100,000, 14
 * digits; its capacity by applyFileSizeChangeRules; refused if it exists
 * with bytes). No force, but at a new file: the old last file's before
 * the new file is made (the switch force, 005-47: no file before the last
 * is ever short on the disk), then the new file's and the directory's
 * before it takes a byte (OPEN, D7: no name durable without the names
 * before it). Nothing to do for a memory stream or a read-only directory. */
enum err_code stream_flush(struct stream *s, struct err *e);

/* stream_flush, then forces the files written since the last force
 * (F_FULLFSYNC); the directory was forced at each new file. */
enum err_code stream_sync(struct stream *s, struct err *e);

/* The length that the last stream_sync made durable (the whole length of
 * a memory stream). */
int64_t stream_durable_length(const struct stream *s);

/* FileStream.determineFileSizeIndex (without the test setting max2G), for
 * the tests: the index of a new file's capacity, from the current index,
 * the stream's length and its size (the length less the first position). */
int32_t stream_file_size_index(int32_t current, int64_t streamLength, int64_t streamSize);

/* stream_sync, then stream_close: Java's close of a stream that it writes.
 * The stream is closed also when the sync fails, and the sync's error
 * returned. */
enum err_code stream_finish(struct stream *s, struct err *e);

/* Closes the files and the lock and frees what the stream holds. Writes
 * nothing: what the buffer holds is dropped (after a failure; a close
 * syncs first, stream_finish). */
void stream_close(struct stream *s);

int64_t stream_first_pos(const struct stream *s);
int64_t stream_length(const struct stream *s);

/* Reads n bytes at position pos into buf (AppendOnlyStream.read), as
 * Java's implementations refuse: a negative position (MemoryStream:
 * ERR_ARG, "IllegalArgumentException"), one below the first position
 * (ERR_NOT_AVAILABLE, "ReadBelowFirstPosException"), and bytes past the
 * end (ERR_IO, "EOFException"; of a directory with no file, "the stream
 * is empty", but 0 bytes at 0, 015-06). n may be 0. */
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

/* AppendOnlyStream.pretruncate(pos), reclaim's cut (012-11; 012-02, 9.4):
 *
 *   - a directory opened for writing: FileStream.pretruncate, every file
 *     but the last that ends before pos (start + length - 1 < pos) taken
 *     off the stream (the last file is kept, so a cut at the length is
 *     one within it, 015-31), the first position then the first remaining
 *     file's start (a file boundary at or before pos); then, as FileStream's
 *     cut thread does, the files written since the last force forced
 *     (005-47's CUT force: the cut's decision durable first), and each
 *     file deleted, oldest first, and the directory forced after each
 *     (005-46), here in the call. ERR_IO (the
 *     stream's failure, as Java's) if a delete or a force fails, or the
 *     stream failed before; ERR_ARG if pos is past the bytes in the files;
 *   - a memory stream: CutStream.pretruncate, the first position pos
 *     exactly, so that a read just below the cut is refused (Java's
 *     MemoryStream drops whole 1 MB arrays); ERR_IO, "IOException", for a
 *     pos below the earlier cut or past the length.
 *
 * Reads below the first position give ERR_NOT_AVAILABLE,
 * "ReadBelowFirstPosException" (stream_read). */
enum err_code stream_pretruncate(struct stream *s, int64_t pos, struct err *e);

/* Cuts a memory stream to 'length' bytes (MemoryStream.truncate), for
 * crash tests. ERR_ARG if it is longer than the stream. */
enum err_code stream_truncate_memory(struct stream *s, int64_t length, struct err *e);

#endif
