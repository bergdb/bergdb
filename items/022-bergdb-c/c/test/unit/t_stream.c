/*
 * Unit tests of stream (bergdb 012-06): the memory stream's reads and
 * refusals (MemoryStream), and a directory read as Java's FileStream reads
 * it: the files found, checked and ordered, reads across them, and the
 * refusals of BadDirStateException.
 */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"
#include "stream.h"
#include "plat.h"

TEST(stream_memory) {
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[16];
    static uint8_t big[2500000];
    mem_init(&m);
    stream_open_memory(&s, &m);
    CHECK_EQ(stream_length(&s), 0);
    CHECK_EQ(stream_read(&s, 0, b, 0, &e), ERR_OK);
    CHECK_EQ(stream_read(&s, 0, b, 1, &e), ERR_IO);
    CHECK(strcmp(e.java, "EOFException") == 0);
    for (int i = 0; i < (int) sizeof big; i++) {
        big[i] = (uint8_t) (i * 31);
    }
    CHECK_EQ(stream_append_memory(&s, big, sizeof big, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), (int64_t) sizeof big);
    CHECK_EQ(stream_read(&s, 1999990, b, 16, &e), ERR_OK);
    CHECK(memcmp(b, big + 1999990, 16) == 0);
    CHECK_EQ(stream_read(&s, -1, b, 1, &e), ERR_ARG);
    CHECK_EQ(stream_read(&s, (int64_t) sizeof big - 15, b, 16, &e), ERR_IO);
    CHECK_EQ(stream_read(&s, INT64_MAX - 3, b, 16, &e), ERR_IO);
    /* pretruncate: to a multiple of 1,000,000, as MemoryStream's arrays. */
    CHECK_EQ(stream_pretruncate_memory(&s, 1999999, &e), ERR_OK);
    CHECK_EQ(stream_first_pos(&s), 1000000);
    CHECK_EQ(stream_read(&s, 999999, b, 1, &e), ERR_NOT_AVAILABLE);
    CHECK(strcmp(e.java, "ReadBelowFirstPosException") == 0);
    CHECK_EQ(stream_read(&s, 1000000, b, 1, &e), ERR_OK);
    CHECK_EQ(stream_pretruncate_memory(&s, 10, &e), ERR_OK);
    CHECK_EQ(stream_first_pos(&s), 1000000);
    CHECK_EQ(stream_pretruncate_memory(&s, -1, &e), ERR_ARG);
    CHECK_EQ(stream_pretruncate_memory(&s, (int64_t) sizeof big + 1, &e), ERR_ARG);
    CHECK_EQ(stream_truncate_memory(&s, (int64_t) sizeof big + 1, &e), ERR_ARG);
    CHECK_EQ(stream_truncate_memory(&s, 1500000, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), 1500000);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

static char tdir[256];

static void write_file(const char *name, int64_t size, uint8_t seed) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", tdir, name);
    FILE *f = fopen(path, "wb");
    for (int64_t i = 0; i < size; i++) {
        fputc((uint8_t) (seed + i), f);
    }
    fclose(f);
}

static void remove_file(const char *name) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", tdir, name);
    unlink(path);
}

static enum err_code open_dir(struct stream *s, struct mem *m, struct err *e) {
    return stream_open_dir(s, tdir, m, e);
}

TEST(stream_dir) {
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[16];
    const char *tmp = getenv("TMPDIR");
    mem_init(&m);
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_stream-XXXXXX", tmp != NULL ? tmp : "/tmp");
    REQUIRE(mkdtemp(tdir) != NULL);

    /* Empty: an empty stream, nothing created. */
    CHECK_EQ(open_dir(&s, &m, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), 0);
    CHECK_EQ(stream_read(&s, 0, b, 1, &e), ERR_IO);
    stream_close(&s);

    /* Two files from 400,000, and other files. */
    write_file("00000000000004.bergdb", 200000, 1);
    write_file("00000000000006.bergdb", 1234, 2);
    write_file("bergdb.lock", 225, 0);
    write_file("created.txt", 3, 0);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_OK);
    CHECK_EQ(stream_first_pos(&s), 400000);
    CHECK_EQ(stream_length(&s), 601234);
    CHECK_EQ(stream_read(&s, 599995, b, 10, &e), ERR_OK);
    CHECK_EQ(b[0], (uint8_t) (1 + 199995));
    CHECK_EQ(b[5], 2);
    CHECK_EQ(b[9], 6);
    CHECK_EQ(stream_read(&s, 399999, b, 1, &e), ERR_NOT_AVAILABLE);
    CHECK_EQ(stream_read(&s, 601230, b, 5, &e), ERR_IO);
    CHECK_EQ(stream_read(&s, 601234, b, 0, &e), ERR_OK);
    stream_close(&s);

    /* Names: Java's stringToIndex strips the zeros and takes a sign. */
    remove_file("00000000000006.bergdb");
    write_file("+6.bergdb", 10, 3);
    /* "+6" (600,000) sorts first, and is not the last: its size, checked before the gap */
    CHECK_EQ(open_dir(&s, &m, &e), ERR_FORMAT);
    CHECK(strstr(e.text, "Bad size") != NULL);
    remove_file("+6.bergdb");
    write_file("6.bergdb", 10, 3);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), 600010);
    stream_close(&s);
    write_file("x.bergdb", 10, 3);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "BadDirStateException") == 0);
    remove_file("x.bergdb");
    write_file("-1.bergdb", 10, 3);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_FORMAT);
    remove_file("-1.bergdb");
    write_file("99999999999999999999.bergdb", 10, 3);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_FORMAT);
    remove_file("99999999999999999999.bergdb");
    write_file(".bergdb", 10, 3);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_FORMAT);
    remove_file(".bergdb");

    /* A gap, and a size before the last that is not a multiple of 100,000. */
    remove_file("6.bergdb");
    write_file("00000000000008.bergdb", 10, 3);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_FORMAT);
    CHECK(strstr(e.text, "not in a correct state") != NULL);
    remove_file("00000000000008.bergdb");
    write_file("00000000000004.bergdb", 199999, 1);
    write_file("00000000000005.bergdb", 10, 3);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_FORMAT);
    CHECK(strstr(e.text, "Bad size") != NULL);
    remove_file("00000000000005.bergdb");
    remove_file("00000000000004.bergdb");
    remove_file("bergdb.lock");
    remove_file("created.txt");
    rmdir(tdir);
    CHECK_EQ(open_dir(&s, &m, &e), ERR_IO);     /* a missing directory */
    CHECK_MEM_ZERO(&m);
}

/* A database's stream (stream_as_storage; bergdb 022-02, D6) is read as
 * Java's Db reads it, through StorageManager and a BufferedStream, whose
 * read refuses first, whatever the position, a read whose last byte is at
 * or past the end, with its EOFException and text (the reads of
 * BufferedStream.testReadOneBytePastEnd); the stream's own refusals come
 * after it, as before. A read far past the last file, as the corrupt-stream
 * set's damaged pointers make, gave C's text of DbFile.read (022-01, step
 * 4; Java names the file's path there). */
TEST(stream_storage) {
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[32];
    const uint8_t ten[10] = { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    const char *tmp = getenv("TMPDIR");
    mem_init(&m);
    stream_open_memory(&s, &m);
    REQUIRE(stream_append_memory(&s, ten, 10, &e) == ERR_OK);
    CHECK_EQ(stream_read(&s, 9, b, 2, &e), ERR_IO);            /* MemoryStream's own */
    CHECK(strcmp(e.text, "Not enough bytes left in the stream, position is 9, length to read "
            "is 2 and stream size is 10.") == 0);
    stream_as_storage(&s);
    CHECK_EQ(stream_read(&s, 8, b, 2, &e), ERR_OK);
    CHECK_EQ(b[1], 10);
    CHECK_EQ(stream_read(&s, 9, b, 2, &e), ERR_IO);
    CHECK(strcmp(e.java, "EOFException") == 0);
    CHECK(strcmp(e.text, "Cannot read 2 bytes at position 9, stream size is 10.") == 0);
    CHECK_EQ(stream_read(&s, 10, b, 1, &e), ERR_IO);
    CHECK(strcmp(e.text, "Cannot read 1 bytes at position 10, stream size is 10.") == 0);
    CHECK_EQ(stream_read(&s, 10, b, 0, &e), ERR_OK);           /* its last byte 9 */
    CHECK_EQ(stream_read(&s, 11, b, 0, &e), ERR_IO);
    CHECK(strcmp(e.text, "Cannot read 0 bytes at position 11, stream size is 10.") == 0);
    CHECK_EQ(stream_read(&s, -1, b, 0, &e), ERR_OK);           /* nothing read, as Java's */
    CHECK_EQ(stream_read(&s, -1, b, 1, &e), ERR_ARG);          /* MemoryStream's, below it */
    CHECK(strcmp(e.java, "IllegalArgumentException") == 0);
    /* Java's sum wrapped here until 021-14 (its read took the ring buffer's
     * bytes), where C refused it as past the end, as both do now. */
    CHECK_EQ(stream_read(&s, INT64_MAX - 1, b, 4, &e), ERR_IO);
    CHECK(strcmp(e.text, "Cannot read 4 bytes at position 9223372036854775806, stream size "
            "is 10.") == 0);
    CHECK_EQ(stream_read(&s, INT64_MIN, b, 0, &e), ERR_OK);   /* nothing read (021-14) */
    stream_close(&s);

    /* A directory of two files, from 400,000 to 601,234. */
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_stream-XXXXXX", tmp != NULL ? tmp : "/tmp");
    REQUIRE(mkdtemp(tdir) != NULL);
    write_file("00000000000004.bergdb", 200000, 1);
    write_file("00000000000006.bergdb", 1234, 2);
    REQUIRE(open_dir(&s, &m, &e) == ERR_OK);
    CHECK_EQ(stream_read(&s, INT64_C(2147483808), b, 32, &e), ERR_IO);
    CHECK(strcmp(e.java, "EOFException") == 0);
    CHECK(strcmp(e.text, "Cannot read at spos 2147483808, past the end of a file at "
            "601234.") == 0);
    stream_as_storage(&s);
    CHECK_EQ(stream_read(&s, INT64_C(2147483808), b, 32, &e), ERR_IO);
    CHECK(strcmp(e.java, "EOFException") == 0);
    CHECK(strcmp(e.text, "Cannot read 32 bytes at position 2147483808, stream size is "
            "601234.") == 0);
    CHECK_EQ(stream_read(&s, 601230, b, 5, &e), ERR_IO);
    CHECK(strcmp(e.text, "Cannot read 5 bytes at position 601230, stream size is 601234.")
            == 0);
    CHECK_EQ(stream_read(&s, 601230, b, 4, &e), ERR_OK);
    CHECK_EQ(b[3], (uint8_t) (2 + 1233));
    CHECK_EQ(stream_read(&s, 399999, b, 2, &e), ERR_NOT_AVAILABLE);   /* FileStream's */
    CHECK(strcmp(e.java, "ReadBelowFirstPosException") == 0);
    CHECK(strcmp(e.text, "Cannot read at spos 399999, below the first position, 400000.")
            == 0);
    stream_close(&s);
    remove_file("00000000000004.bergdb");
    remove_file("00000000000006.bergdb");
    rmdir(tdir);
    CHECK_MEM_ZERO(&m);
}

/* BufferedStream.testReadPastEndNearMaxValue and StreamContract's reads past
 * the end of 1 byte at Long.MAX_VALUE and 4 at Long.MAX_VALUE - 2 (bergdb
 * 021-14, as Java's since release 2026.4): a read whose end, position +
 * length, overflows a long is a read past the end, EOFException, and the
 * stream is as it was. Java's sum wrapped and its check passed:
 * BufferedStream's read took bytes of its ring buffer or threw
 * IndexOutOfBoundsException, MemoryStream's returned with the array as it
 * was. C refused each read already, and the test passes on C before
 * 021-14: a database's stream by 022-02, D6's check, a memory stream by
 * its check without the sum, a directory as past its last file; one read
 * for writing, with bytes in its write buffer, wrapped its sum (-fwrapv)
 * and refused the read as past its files ("the stream is empty"), now as
 * past the end of its buffer. On each stream, alone and as a database's
 * storage, with 10 bytes: a memory stream, a directory for writing with
 * the bytes in its buffer (of 100 and of 1,024 bytes), and one read only
 * with them in its file; every length of 1, 4, 32 and 1,000 at every
 * position from Long.MAX_VALUE - length up. */
TEST(stream_read_past_end_near_max_value) {
    struct mem m;
    struct err e;
    struct stream s;
    static uint8_t b[1000];
    const uint8_t ten[10] = { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    const int32_t lengths[] = { 1, 4, 32, 1000 };
    const char *tmp = getenv("TMPDIR");
    mem_init(&m);
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_stream-XXXXXX", tmp != NULL ? tmp : "/tmp");
    REQUIRE(mkdtemp(tdir) != NULL);
    char lock[300];
    snprintf(lock, sizeof lock, "%s/bergdb.lock", tdir);
    int64_t refused = 0;
    for (int32_t kind = 0; kind < 4; kind++) {
        for (int32_t storage = 0; storage < 2; storage++) {
            if (kind == 0) {
                stream_open_memory(&s, &m);
                REQUIRE(stream_append_memory(&s, ten, 10, &e) == ERR_OK);
            } else if (kind < 3) {
                REQUIRE(stream_open_dir_rw(&s, tdir, kind == 1 ? 100 : 1024, &m, &e) == ERR_OK);
                REQUIRE(stream_append(&s, ten, 10, &e) == ERR_OK);
            } else {
                REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
                REQUIRE(stream_append(&s, ten, 10, &e) == ERR_OK);
                REQUIRE(stream_finish(&s, &e) == ERR_OK);
                REQUIRE(stream_open_dir(&s, tdir, &m, &e) == ERR_OK);
            }
            if (storage) {
                stream_as_storage(&s);
            }
            for (size_t l = 0; l < sizeof lengths / sizeof lengths[0]; l++) {
                const int32_t n = lengths[l];
                for (int64_t k = 0; k <= n; k++) {
                    const int64_t pos = INT64_MAX - k;
                    enum err_code rc = stream_read(&s, pos, b, n, &e);
                    CHECK_EQ(rc, ERR_IO);
                    CHECK(strcmp(e.java, "EOFException") == 0);
                    char text[100];
                    snprintf(text, sizeof text, "Cannot read %d bytes at position %lld, stream "
                            "size is 10.", (int) n, (long long) pos);
                    if (storage && (rc != ERR_IO || strcmp(e.text, text) != 0)) {
                        printf("    kind %d: %s\n", (int) kind, e.text);
                        CHECK(false);
                    }
                    refused++;
                }
            }
            memset(b, 0, 10);
            CHECK_EQ(stream_read(&s, 0, b, 10, &e), ERR_OK);
            CHECK(memcmp(b, ten, 10) == 0);
            if (kind == 1 || kind == 2) {
                CHECK_EQ(s.buf_len, 10);        /* still in the buffer */
                REQUIRE(stream_finish(&s, &e) == ERR_OK);
            } else {
                stream_close(&s);
            }
            remove_file("00000000000000.bergdb");
        }
    }
    CHECK_EQ(refused, 8 * (2 + 5 + 33 + 1001));
    unlink(lock);
    rmdir(tdir);
    CHECK_MEM_ZERO(&m);
}

#ifdef BERGDB_TEST
/* A counting seam over the real calls (012-14, 6.5). */
static int64_t seam_counts[6];
static enum err_code seam_open_rw(const char *path, int *fd, struct err *e) {
    seam_counts[0]++;
    return plat_io_real()->open_rw(path, fd, e);
}
static enum err_code seam_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n,
        struct err *e) {
    seam_counts[1] += n;
    return plat_io_real()->pwrite(fd, off, buf, n, e);
}
static enum err_code seam_force(int fd, enum plat_force_why why, struct err *e) {
    seam_counts[2]++;
    return plat_io_real()->force(fd, why, e);
}
static enum err_code seam_force_dir(const char *dir, struct err *e) {
    seam_counts[3]++;
    return plat_io_real()->force_dir(dir, e);
}
static enum err_code seam_unlink(const char *path, struct err *e) {
    seam_counts[4]++;
    return plat_io_real()->unlink(path, e);
}
static void seam_close(int fd) {
    seam_counts[5]++;
    plat_io_real()->close(fd);
}
static const struct plat_io SEAM = {
    seam_open_rw, seam_pwrite, seam_force, seam_force_dir, seam_unlink, seam_close
};
#endif

/* The I/O seam of the test build (012-14, 6.5): the stream's writes, forces,
 * opens, deletes and closes go through it, and the default is the real
 * calls; the release build has none. */
TEST(stream_seam) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    static uint8_t data[250000];
    uint8_t b[4];
    const char *tmp = getenv("TMPDIR");
    mem_init(&m);
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_seam-XXXXXX", tmp != NULL ? tmp : "/tmp");
    REQUIRE(mkdtemp(tdir) != NULL);
    for (int32_t i = 0; i < (int32_t) sizeof data; i++) {
        data[i] = (uint8_t) i;
    }
    plat_io_set(&SEAM);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK_EQ(seam_counts[0], 0);            /* no file yet (015-06) */
    CHECK_EQ(stream_append(&s, data, (int64_t) sizeof data, &e), ERR_OK);
    CHECK_EQ(seam_counts[1], 225);          /* the lock file's text only; the rest buffered */
    CHECK_EQ(stream_sync(&s, &e), ERR_OK);
    CHECK_EQ(seam_counts[0], 2);            /* the first file, and a second at 200,000 */
    CHECK_EQ(seam_counts[1], 225 + 250000);
    CHECK_EQ(seam_counts[2], 4);            /* each made and forced (OPEN), then written */
    CHECK(seam_counts[3] >= 2);             /* and forced: the first at the switch, the
                                               second at the sync; the directory after each
                                               new file */
    int64_t dirs = seam_counts[3];
    CHECK_EQ(stream_pretruncate(&s, 200000, &e), ERR_OK);
    CHECK_EQ(seam_counts[4], 1);            /* the first file deleted */
    CHECK_EQ(seam_counts[3], dirs + 1);     /* the directory forced after it */
    CHECK_EQ(stream_read(&s, 249996, b, 4, &e), ERR_OK);
    CHECK_EQ(b[3], (uint8_t) 249999);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    CHECK(seam_counts[5] >= 3);             /* two files and the lock */
    plat_io_set(NULL);
    /* The default again: the real calls, not counted. */
    int64_t writes = seam_counts[1];
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK_EQ(stream_append(&s, data, 10, &e), ERR_OK);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    CHECK_EQ(seam_counts[1], writes);
    char path[300];
    snprintf(path, sizeof path, "%s/00000000000002.bergdb", tdir);
    CHECK_EQ(plat_file_length(path), 50010);
    remove_file("00000000000002.bergdb");
    remove_file("bergdb.lock");
    rmdir(tdir);
    CHECK_MEM_ZERO(&m);
#endif
}

#ifdef BERGDB_TEST
/* A seam that logs, in order, the opens of stream files, the writes, the
 * file forces with their reasons, the directory forces and the deletes, by
 * the file's index ("open 2", "write 2", "SWITCH 0", "dir", "delete 0"),
 * as Java's ForceLogIo (bergdb 005-47); it passes each call on. */
static char flog[2048];
static int flog_fd_index[256];      /* a stream file's index + 1, 0 for other files */
static void flog_add(const char *entry) {
    size_t at = strlen(flog);
    snprintf(flog + at, sizeof flog - at, "%s%s", at > 0 ? " " : "", entry);
}
static int flog_index(const char *path) {
    const char *slash = strrchr(path, '/');
    const char *name = slash != NULL ? slash + 1 : path;
    size_t n = strlen(name);
    return n == 21 && strcmp(name + 14, ".bergdb") == 0 ? atoi(name) : -1;
}
static enum err_code flog_open_rw(const char *path, int *fd, struct err *e) {
    enum err_code rc = plat_io_real()->open_rw(path, fd, e);
    int i = flog_index(path);
    if (rc == ERR_OK && *fd >= 0 && *fd < 256) {
        flog_fd_index[*fd] = i + 1;
    }
    if (rc == ERR_OK && i >= 0) {
        char entry[32];
        snprintf(entry, sizeof entry, "open %d", i);
        flog_add(entry);
    }
    return rc;
}
static enum err_code flog_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n,
        struct err *e) {
    int i = fd >= 0 && fd < 256 ? flog_fd_index[fd] - 1 : -1;
    if (i >= 0) {
        char entry[32];
        snprintf(entry, sizeof entry, "write %d", i);
        flog_add(entry);
    }
    return seam_pwrite(fd, off, buf, n, e);
}
static enum err_code flog_force(int fd, enum plat_force_why why, struct err *e) {
    static const char *const WHY[] = { "SYNC", "OPEN", "SWITCH", "CUT" };
    char entry[32];
    int i = fd >= 0 && fd < 256 ? flog_fd_index[fd] - 1 : -1;
    snprintf(entry, sizeof entry, "%s %d", WHY[why], i);
    flog_add(entry);
    return plat_io_real()->force(fd, why, e);
}
static enum err_code flog_force_dir(const char *dir, struct err *e) {
    if (strcmp(dir, tdir) == 0) {
        flog_add("dir");
    }
    return plat_io_real()->force_dir(dir, e);
}
static enum err_code flog_unlink(const char *path, struct err *e) {
    char entry[32];
    snprintf(entry, sizeof entry, "delete %d", flog_index(path));
    flog_add(entry);
    return plat_io_real()->unlink(path, e);
}
static const struct plat_io FLOG = {
    flog_open_rw, flog_pwrite, flog_force, flog_force_dir, flog_unlink, seam_close
};
#endif

/* The forces that keep a power loss's image a prefix of the stream across
 * its files (bergdb 005-47, FileStream's forces with per-append forcing
 * off; 022-01, step 3), in order: the old last file before a new file's
 * name exists (SWITCH: else a power loss can leave a short file before a
 * newer one, which an open refuses), once per file and never again; each
 * new file and then the directory before the file takes a byte (OPEN, as
 * Java's openForRw; 022-02, D7: no name durable without the names before
 * it); the files written since the last force before a cut's deletes (CUT:
 * the cut's decision durable before the files it replaces are gone), and
 * nothing when a sync forced them; the last file and the directory at an
 * open for writing (OPEN: what a process that died wrote, durable before
 * this one counts it or cuts). */
TEST(stream_forces) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    static uint8_t data[650000];
    const char *tmp = getenv("TMPDIR");
    mem_init(&m);
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_forces-XXXXXX", tmp != NULL ? tmp : "/tmp");
    REQUIRE(mkdtemp(tdir) != NULL);
    for (int32_t i = 0; i < (int32_t) sizeof data; i++) {
        data[i] = (uint8_t) (i * 13);
    }
    flog[0] = '\0';
    plat_io_set(&FLOG);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK(strcmp(flog, "") == 0);
    /* Four files: 0, 2 and 4 full (200,000 bytes each), 6 with 50,000. */
    CHECK_EQ(stream_append(&s, data, 650000, &e), ERR_OK);
    CHECK_EQ(stream_flush(&s, &e), ERR_OK);
    CHECK(strcmp(flog, "open 0 OPEN 0 dir write 0 SWITCH 0 open 2 OPEN 2 dir write 2 "
            "SWITCH 2 open 4 OPEN 4 dir write 4 SWITCH 4 open 6 OPEN 6 dir write 6") == 0);
    printf("    forces at four new files: %s\n", flog);

    /* A cut at 400,000 with file 6 unforced: it first; the names are. */
    flog[0] = '\0';
    CHECK_EQ(stream_pretruncate(&s, 400000, &e), ERR_OK);
    CHECK(strcmp(flog, "CUT 6 delete 0 dir delete 2 dir") == 0);
    printf("    a cut after them: %s\n", flog);
    CHECK_EQ(stream_first_pos(&s), 400000);

    /* After a sync, a cut forces nothing before its delete. */
    CHECK_EQ(stream_append(&s, data, 160000, &e), ERR_OK);     /* to 810,000: file 8 */
    flog[0] = '\0';
    CHECK_EQ(stream_sync(&s, &e), ERR_OK);
    CHECK(strcmp(flog, "write 6 SWITCH 6 open 8 OPEN 8 dir write 8 SYNC 8") == 0);
    flog[0] = '\0';
    CHECK_EQ(stream_pretruncate(&s, 600000, &e), ERR_OK);
    CHECK(strcmp(flog, "delete 4 dir") == 0);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);

    /* An open for writing forces its last file, then the directory. */
    flog[0] = '\0';
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK(strstr(flog, "open 8 OPEN 8 dir") != NULL);
    CHECK_EQ(stream_length(&s), 810000);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    plat_io_set(NULL);
    remove_file("00000000000006.bergdb");
    remove_file("00000000000008.bergdb");
    remove_file("bergdb.lock");
    rmdir(tdir);
    CHECK_MEM_ZERO(&m);
#endif
}

#ifdef BERGDB_TEST
/* The number of entries of flog that are 'entry' or start with it and a
 * space. */
static int flog_count(const char *entry) {
    int n = 0;
    size_t k = strlen(entry);
    for (const char *p = flog; *p != '\0'; ) {
        if (strncmp(p, entry, k) == 0 && (p[k] == ' ' || p[k] == '\0')
                && (p == flog || p[-1] == ' ')) {
            n++;
        }
        p++;
    }
    return n;
}
#endif

/* Each new file forced, and then the directory, before the file takes a
 * byte (bergdb 022-02, D7; Java's openForRw: OPEN, then the directory,
 * with per-append forcing on or off): one write of the buffer that makes
 * six files forces the directory six times, each after a file is made and
 * before its first byte, so that no name is durable without the names
 * before it; the sync after forces the last file only. Before D7, C forced
 * a new file and the directory at the next sync, close or cut: here once,
 * after the six. FileStream's testForcingOffWritesAppends (the first
 * file's OPEN force, at length 0) and the six files of
 * testForcingOffForcesBeforeACutDeletes. */
TEST(stream_new_file_forces) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    static uint8_t data[1000100];
    char expected[512] = "";
    const char *tmp = getenv("TMPDIR");
    mem_init(&m);
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_newfile-XXXXXX", tmp != NULL ? tmp : "/tmp");
    REQUIRE(mkdtemp(tdir) != NULL);
    flog[0] = '\0';
    plat_io_set(&FLOG);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    /* Five files of 200,000 bytes, and a sixth at 1,000,000, in one write. */
    CHECK_EQ(stream_append(&s, data, (int64_t) sizeof data, &e), ERR_OK);
    CHECK_EQ(stream_flush(&s, &e), ERR_OK);
    for (int i = 0; i <= 10; i += 2) {
        size_t at = strlen(expected);
        if (i > 0) {
            snprintf(expected + at, sizeof expected - at, " SWITCH %d ", i - 2);
            at = strlen(expected);
        }
        snprintf(expected + at, sizeof expected - at, "open %d OPEN %d dir write %d", i, i, i);
    }
    CHECK(strcmp(flog, expected) == 0);
    CHECK_EQ(flog_count("open"), 6);
    CHECK_EQ(flog_count("OPEN"), 6);
    CHECK_EQ(flog_count("dir"), 6);
    CHECK_EQ(flog_count("SWITCH"), 5);
    printf("    one write, six files: %d OPEN, %d dir, %d SWITCH\n", flog_count("OPEN"),
            flog_count("dir"), flog_count("SWITCH"));
    flog[0] = '\0';
    CHECK_EQ(stream_sync(&s, &e), ERR_OK);
    CHECK(strcmp(flog, "SYNC 10") == 0);
    CHECK_EQ(stream_durable_length(&s), 1000100);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    plat_io_set(NULL);
    for (int i = 0; i <= 10; i += 2) {
        char name[32];
        snprintf(name, sizeof name, "%014d.bergdb", i);
        remove_file(name);
    }
    remove_file("bergdb.lock");
    rmdir(tdir);
    CHECK_MEM_ZERO(&m);
#endif
}

/* ======== Java's tests of the stream classes (bergdb 022-05) ======== */

/* A new temporary directory, made, in tdir. */
static bool new_tdir(const char *what) {
    const char *tmp = getenv("TMPDIR");
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_%s-XXXXXX", tmp != NULL ? tmp : "/tmp", what);
    return mkdtemp(tdir) != NULL;
}

/* Removes tdir's entries (files only) and tdir. */
static void remove_tdir(void) {
    struct dirent **list;
    int n = scandir(tdir, &list, NULL, alphasort);
    for (int i = 0; i < n; i++) {
        if (list[i]->d_name[0] != '.') {
            remove_file(list[i]->d_name);
        }
        free(list[i]);
    }
    if (n >= 0) {
        free(list);
    }
    rmdir(tdir);
}

/* Whether the file 'name' of tdir exists. */
static bool tdir_has(const char *name) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", tdir, name);
    return access(path, F_OK) == 0;
}


/* StreamContract.at: the byte at stream position pos, in the tests below. */
static uint8_t at(int64_t pos) {
    return (uint8_t) (pos * 31 + 7);
}

/* Appends n bytes of at() from the stream's length (StreamContract.append). */
static enum err_code append_at(struct stream *s, int64_t n, struct err *e) {
    static uint8_t b[100000];
    const int64_t from = stream_length(s);
    enum err_code rc = ERR_OK;
    for (int64_t done = 0; done < n && rc == ERR_OK; ) {
        int64_t k = n - done < (int64_t) sizeof b ? n - done : (int64_t) sizeof b;
        uint8_t x = at(from + done);
        for (int64_t i = 0; i < k; i++, x = (uint8_t) (x + 31)) {
            b[i] = x;
        }
        rc = stream_append(s, b, k, e);
        done += k;
    }
    return rc;
}

/* Reads n bytes at pos and compares them with at() (StreamContract.readAndCompare): true
 * if the read succeeds with those bytes. */
static bool read_at(struct stream *s, int64_t pos, int32_t n) {
    static uint8_t b[1000000];
    struct err e;
    if (n > (int32_t) sizeof b) {
        return false;
    }
    if (stream_read(s, pos, b, n, &e) != ERR_OK) {
        printf("    read(%lld, %d): %s: %s\n", (long long) pos, (int) n, e.java, e.text);
        return false;
    }
    uint8_t x = at(pos);
    for (int32_t i = 0; i < n; i++, x = (uint8_t) (x + 31)) {
        if (b[i] != x) {
            printf("    read(%lld, %d): byte %d at %lld, where %d was appended\n",
                    (long long) pos, (int) n, b[i], (long long) (pos + i), at(pos + i));
            return false;
        }
    }
    return true;
}

#ifdef BERGDB_TEST
/* The file descriptors open in this process, below 256. */
static int open_fds(void) {
    int n = 0;
    for (int fd = 0; fd < 256; fd++) {
        n += fcntl(fd, F_GETFD) != -1;
    }
    return n;
}

/* A seam that fails one call with ERR_IO, "IOException", "injected": the inj_at-th call of
 * the kind inj_kind (an open of a stream file, a write, a force for the reason inj_why, a
 * force of the directory tdir, a delete); every other call passes on. */
enum inj_kind { INJ_NONE, INJ_OPEN, INJ_WRITE, INJ_FORCE, INJ_DIR, INJ_DELETE };
static enum inj_kind inj_kind;
static enum plat_force_why inj_why;
static int inj_at, inj_calls, inj_failed;

static void inj_set(enum inj_kind kind, enum plat_force_why why, int at_call) {
    inj_kind = kind;
    inj_why = why;
    inj_at = at_call;
    inj_calls = 0;
    inj_failed = 0;
}
static bool inj_now(enum inj_kind kind) {
    if (inj_kind != kind || ++inj_calls != inj_at) {
        return false;
    }
    inj_failed++;
    return true;
}
static enum err_code inj_open_rw(const char *path, int *fd, struct err *e) {
    if (flog_index(path) >= 0 && inj_now(INJ_OPEN)) {
        *fd = -1;
        return err_set(e, ERR_IO, "IOException", "injected");
    }
    return plat_io_real()->open_rw(path, fd, e);
}
static enum err_code inj_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n,
        struct err *e) {
    if (inj_now(INJ_WRITE)) {
        return err_set(e, ERR_IO, "IOException", "injected");
    }
    return plat_io_real()->pwrite(fd, off, buf, n, e);
}
static enum err_code inj_force(int fd, enum plat_force_why why, struct err *e) {
    if (why == inj_why && inj_now(INJ_FORCE)) {
        return err_set(e, ERR_IO, "IOException", "injected");
    }
    return plat_io_real()->force(fd, why, e);
}
static enum err_code inj_force_dir(const char *dir, struct err *e) {
    if (strcmp(dir, tdir) == 0 && inj_now(INJ_DIR)) {
        return err_set(e, ERR_IO, "IOException", "injected");
    }
    return plat_io_real()->force_dir(dir, e);
}
static enum err_code inj_unlink(const char *path, struct err *e) {
    if (inj_now(INJ_DELETE)) {
        return err_set(e, ERR_IO, "IOException", "injected");
    }
    return plat_io_real()->unlink(path, e);
}
static void inj_close(int fd) {
    plat_io_real()->close(fd);
}
static const struct plat_io INJ = {
    inj_open_rw, inj_pwrite, inj_force, inj_force_dir, inj_unlink, inj_close
};

/* Writes and no forces, as Java's StreamContract.NoForceIo: durability is not the subject
 * of the contract and the workload, and forces are slow. */
static enum err_code noforce_force(int fd, enum plat_force_why why, struct err *e) {
    (void) fd;
    (void) why;
    (void) e;
    return ERR_OK;
}
static enum err_code noforce_force_dir(const char *dir, struct err *e) {
    (void) dir;
    (void) e;
    return ERR_OK;
}
static const struct plat_io NOFORCE = {
    inj_open_rw, inj_pwrite, noforce_force, noforce_force_dir, inj_unlink, inj_close
};
#endif

/* FileStream.testFailedOpenClosesFileAndUnlocks (bergdb 015-32): an open for writing whose
 * open of its last file, or that file's OPEN force, or the directory's force after it,
 * fails gives the failure and leaves nothing open: no file, no lock (each descriptor
 * closed), no memory; the next open opens the directory with its byte. */
TEST(stream_failed_open) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[1] = { 7 };
    mem_init(&m);
    REQUIRE(new_tdir("failopen"));
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    REQUIRE(stream_append(&s, b, 1, &e) == ERR_OK);
    REQUIRE(stream_finish(&s, &e) == ERR_OK);
    const enum inj_kind kinds[3] = { INJ_OPEN, INJ_FORCE, INJ_DIR };
    plat_io_set(&INJ);
    for (int k = 0; k < 3; k++) {
        const int fds = open_fds();
        inj_set(kinds[k], PLAT_FORCE_OPEN, 1);
        CHECK_EQ(stream_open_dir_rw(&s, tdir, 0, &m, &e), ERR_IO);
        CHECK(strcmp(e.text, "injected") == 0);
        CHECK_EQ(inj_failed, 1);
        CHECK_EQ(open_fds(), fds);
        CHECK_MEM_ZERO(&m);
        inj_set(INJ_NONE, PLAT_FORCE_OPEN, 0);
        REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
        b[0] = 0;
        CHECK_EQ(stream_read(&s, 0, b, 1, &e), ERR_OK);
        CHECK_EQ(b[0], 7);
        CHECK_EQ(stream_finish(&s, &e), ERR_OK);
        CHECK_EQ(open_fds(), fds);
    }
    plat_io_set(NULL);
    remove_tdir();
    CHECK_MEM_ZERO(&m);
#endif
}

/* A stream that an I/O failure failed takes nothing more: no write, no force, no cut, and
 * its close gives the failure (Java's FileStream.checkIOException; c/readme.md, section 9,
 * point 8). FileStream.testFailedDeleteOfACut (005-46: the second delete of a cut fails;
 * the first file is gone, the second and those after it are not) and
 * BufferedStream.testCloseAfterFailedFlush (the close gives the flush's failure and frees
 * everything), with a failed write, force at a sync and switch force too. The switch
 * force's failure makes no new file (005-47: no name after a file that is not forced).
 * Before, a sync after a failed force, or after a failed delete, found its buffer empty,
 * forced the file again or nothing, and gave ERR_OK with the durable length the stream's,
 * and so did the close (stream_failed_force_fails_the_database). */
TEST(stream_failure_refuses_writes) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[1] = { 1 };
    mem_init(&m);
    const char *const names[4] = { "a write", "the sync's force", "the switch force",
        "a cut's second delete" };
    for (int k = 0; k < 4; k++) {
        REQUIRE(new_tdir("failwrites"));
        const int fds = open_fds();
        plat_io_set(&INJ);
        inj_set(INJ_NONE, PLAT_FORCE_SYNC, 0);
        REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
        int64_t durable = 0;
        if (k == 0) {
            REQUIRE(append_at(&s, 300, &e) == ERR_OK);
            inj_set(INJ_WRITE, PLAT_FORCE_SYNC, 1);
            CHECK_EQ(stream_sync(&s, &e), ERR_IO);
        } else if (k == 1) {
            REQUIRE(append_at(&s, 300, &e) == ERR_OK);
            inj_set(INJ_FORCE, PLAT_FORCE_SYNC, 1);
            CHECK_EQ(stream_sync(&s, &e), ERR_IO);
        } else if (k == 2) {
            REQUIRE(append_at(&s, 250000, &e) == ERR_OK);
            inj_set(INJ_FORCE, PLAT_FORCE_SWITCH, 1);
            CHECK_EQ(stream_flush(&s, &e), ERR_IO);
            CHECK(tdir_has("00000000000000.bergdb"));
            CHECK(!tdir_has("00000000000002.bergdb"));      /* no new file */
        } else {
            REQUIRE(append_at(&s, 1000000, &e) == ERR_OK);
            REQUIRE(stream_sync(&s, &e) == ERR_OK);
            durable = 1000000;
            inj_set(INJ_DELETE, PLAT_FORCE_SYNC, 2);
            CHECK_EQ(stream_pretruncate(&s, 800000, &e), ERR_IO);
            CHECK(!tdir_has("00000000000000.bergdb"));      /* the first deleted */
            CHECK(tdir_has("00000000000002.bergdb"));       /* the second not, nor later ones */
            CHECK(tdir_has("00000000000004.bergdb"));
            CHECK(tdir_has("00000000000006.bergdb"));
            CHECK_EQ(stream_first_pos(&s), 800000);
        }
        CHECK(strcmp(e.text, "injected") == 0);
        CHECK_EQ(inj_failed, 1);
        inj_set(INJ_NONE, PLAT_FORCE_SYNC, 0);
        bool ok[7];
        ok[0] = stream_durable_length(&s) == durable;
        ok[1] = stream_sync(&s, &e) == ERR_IO;                /* no force after the failure */
        ok[2] = stream_durable_length(&s) == durable;
        ok[3] = stream_flush(&s, &e) == ERR_IO;
        ok[4] = stream_append(&s, b, 1, &e) == ERR_IO;
        ok[5] = stream_pretruncate(&s, stream_first_pos(&s), &e) == ERR_IO;
        ok[6] = stream_finish(&s, &e) == ERR_IO;              /* the close gives the failure */
        for (int i = 0; i < 7; i++) {
            if (!ok[i]) {
                printf("    after %s: check %d failed\n", names[k], i);
                CHECK(ok[i]);
            }
        }
        CHECK_MEM_ZERO(&m);
        CHECK_EQ(open_fds(), fds);
        plat_io_set(NULL);
        /* What a start finds: a stream that opens, with the bytes written. */
        REQUIRE(stream_open_dir(&s, tdir, &m, &e) == ERR_OK);
        const int64_t first[4] = { 0, 0, 0, 200000 };
        const int64_t length[4] = { 0, 300, 200000, 1000000 };
        CHECK_EQ(stream_first_pos(&s), first[k]);
        CHECK_EQ(stream_length(&s), length[k]);
        CHECK(read_at(&s, first[k], (int32_t) (length[k] - first[k])));
        stream_close(&s);
        remove_tdir();
    }
    CHECK_MEM_ZERO(&m);
#endif
}

/* The failure of the force at a sync, through bergdb.h: the sync gives BERGDB_FAILED, and
 * so does every later sync and transaction; the close gives BERGDB_IO and frees everything
 * (c/readme.md, section 9, point 8). Before, the second sync forced the file again and gave
 * BERGDB_OK, and so did the close. */
TEST(stream_failed_force_fails_the_database) {
#ifdef BERGDB_TEST
    struct bergdb_mem bm = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_executed ex;
    bergdb_db *db;
    bergdb_trans *t;
    uint8_t key[16];
    REQUIRE(new_tdir("failforce"));
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.mem = &bm;
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(tdir, &o, &db, NULL, NULL) == BERGDB_OK);
    REQUIRE(bergdb_ikey_to_bkey((const uint8_t *) "/a", 2, key) == BERGDB_OK);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    REQUIRE(bergdb_trans_put(t, key, 2, (const uint8_t *) "x", 1) == BERGDB_OK);
    REQUIRE(bergdb_execute(db, t, &ex) == BERGDB_OK);
    bergdb_trans_free(t);
    plat_io_set(&INJ);
    inj_set(INJ_FORCE, PLAT_FORCE_SYNC, 1);
    CHECK_EQ(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY), BERGDB_FAILED);
    CHECK_EQ(inj_failed, 1);
    inj_set(INJ_NONE, PLAT_FORCE_SYNC, 0);
    CHECK_EQ(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY), BERGDB_FAILED);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    REQUIRE(bergdb_trans_put(t, key, 2, (const uint8_t *) "y", 1) == BERGDB_OK);
    CHECK_EQ(bergdb_execute(db, t, &ex), BERGDB_FAILED);
    bergdb_trans_free(t);
    CHECK_EQ(bergdb_close(db), BERGDB_IO);
    CHECK_EQ(bm.live_total, 0);
    plat_io_set(NULL);
    remove_tdir();
#endif
}

/* FileStream.testReadBelowFirstPosDoesNotBreakStream and
 * StorageManagerTester.testReadBelowFirstPosIsNotAStreamError (bergdb 011-04, W1): a read
 * below the first position after a cut fails alone, ReadBelowFirstPosException; the stream
 * has not failed: it reads above the cut, appends, reads the new bytes, syncs. On a
 * directory (with a buffer of 1,000 bytes; and as a database's storage) and on a memory
 * stream, whose cut is exact (CutStream's, a database in memory). In the test build with
 * writes and no forces (Java's NoForceIo), here and in stream_read_past_end. */
TEST(stream_read_below_first_pos) {
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[10];
    mem_init(&m);
#ifdef BERGDB_TEST
    inj_set(INJ_NONE, PLAT_FORCE_SYNC, 0);
    plat_io_set(&NOFORCE);
#endif
    for (int kind = 0; kind < 3; kind++) {
        int64_t cut;
        if (kind < 2) {
            REQUIRE(new_tdir("below"));
            REQUIRE(stream_open_dir_rw(&s, tdir, 1000, &m, &e) == ERR_OK);
            REQUIRE(append_at(&s, 500000, &e) == ERR_OK);
            REQUIRE(stream_sync(&s, &e) == ERR_OK);
            if (kind == 1) {
                stream_as_storage(&s);
            }
            cut = 400000;
        } else {
            stream_open_memory(&s, &m);
            REQUIRE(append_at(&s, 1000, &e) == ERR_OK);
            cut = 600;
        }
        CHECK_EQ(stream_pretruncate(&s, cut, &e), ERR_OK);
        CHECK_EQ(stream_first_pos(&s), cut);
        CHECK_EQ(stream_read(&s, 100, b, 10, &e), ERR_NOT_AVAILABLE);
        CHECK(strcmp(e.java, "ReadBelowFirstPosException") == 0);
        CHECK_EQ(stream_read(&s, cut - 1, b, 10, &e), ERR_NOT_AVAILABLE);
        CHECK(!s.failed);
        const int64_t length = stream_length(&s);
        CHECK(read_at(&s, cut + 50, 10));
        CHECK_EQ(append_at(&s, 1000, &e), ERR_OK);
        CHECK(read_at(&s, length, 10));
        CHECK(read_at(&s, cut, (int32_t) (length + 1000 - cut)));
        if (kind < 2) {
            CHECK_EQ(stream_finish(&s, &e), ERR_OK);
            REQUIRE(stream_open_dir(&s, tdir, &m, &e) == ERR_OK);
            CHECK_EQ(stream_first_pos(&s), cut);
            CHECK_EQ(stream_length(&s), length + 1000);
            CHECK(read_at(&s, cut, (int32_t) (length + 1000 - cut)));
            stream_close(&s);
            remove_tdir();
        } else {
            stream_close(&s);
        }
    }
#ifdef BERGDB_TEST
    plat_io_set(NULL);
#endif
    CHECK_MEM_ZERO(&m);
}

/* FileStream.testReadPastEnd (bergdb 005-24): reads at the end, across it and past it, of
 * two files (300,000 bytes), give EOFException, and the stream stays usable: it reads,
 * appends and reads the new bytes. With the bytes in the files (a buffer of 1,000 bytes),
 * in the write buffer (its default size), and in the files after a sync. */
TEST(stream_read_past_end) {
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[10];
    mem_init(&m);
#ifdef BERGDB_TEST
    inj_set(INJ_NONE, PLAT_FORCE_SYNC, 0);
    plat_io_set(&NOFORCE);
#endif
    for (int kind = 0; kind < 3; kind++) {
        REQUIRE(new_tdir("pastend"));
        REQUIRE(stream_open_dir_rw(&s, tdir, kind == 0 ? 1000 : 0, &m, &e) == ERR_OK);
        REQUIRE(append_at(&s, 300000, &e) == ERR_OK);
        if (kind == 2) {
            REQUIRE(stream_sync(&s, &e) == ERR_OK);
        }
        CHECK_EQ(s.buf_len, kind == 1 ? 300000 : 0);
        const int64_t positions[3] = { 300000, 300000 - 5, 300000 + 1 };
        for (int i = 0; i < 3; i++) {
            CHECK_EQ(stream_read(&s, positions[i], b, 10, &e), ERR_IO);
            CHECK(strcmp(e.java, "EOFException") == 0);
        }
        CHECK(!s.failed);
        CHECK(read_at(&s, 300000 - 10, 10));
        CHECK_EQ(append_at(&s, 10, &e), ERR_OK);
        CHECK(read_at(&s, 300000, 10));
        CHECK_EQ(stream_read(&s, 300010, b, 1, &e), ERR_IO);
        CHECK_EQ(stream_finish(&s, &e), ERR_OK);
        remove_tdir();
    }
#ifdef BERGDB_TEST
    plat_io_set(NULL);
#endif
    CHECK_MEM_ZERO(&m);
}

/* BufferedStream.testReadFromBufferOfNonEmptyStream: on a stream that has bytes in its
 * files, a read of bytes in the write buffer, and one across the files and the buffer, give
 * the bytes appended. */
TEST(stream_read_from_buffer_nonempty) {
    struct mem m;
    struct err e;
    struct stream s;
    mem_init(&m);
    REQUIRE(new_tdir("nonempty"));
    REQUIRE(stream_open_dir_rw(&s, tdir, 100, &m, &e) == ERR_OK);
    REQUIRE(append_at(&s, 150, &e) == ERR_OK);
    REQUIRE(stream_finish(&s, &e) == ERR_OK);
    REQUIRE(stream_open_dir_rw(&s, tdir, 100, &m, &e) == ERR_OK);
    CHECK_EQ(stream_length(&s), 150);
    REQUIRE(append_at(&s, 10, &e) == ERR_OK);
    CHECK_EQ(s.buf_len, 10);
    CHECK(read_at(&s, 150, 10));
    CHECK(read_at(&s, 148, 12));
    CHECK(read_at(&s, 0, 160));
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    remove_tdir();
    CHECK_MEM_ZERO(&m);
}

/* The stream contract (bergdb 018-02, StreamContract's checks; StreamContractTester's
 * testFileStream, testMemoryStream and testCutStream; StorageContractTester's
 * testBufferedStream and testStorageManager, C's write buffer being both), on C's streams:
 * a memory stream (a database in memory; its cut exact, as CutStream's), alone and as a
 * database's storage (stream_as_storage, Java's BufferedStream's reads); and in the test
 * build, with writes and no forces (Java's NoForceIo), a directory for writing with a
 * buffer of 10,000 bytes (StorageContractTester's), alone and as storage, and with the
 * default buffer. Each check on a new stream: an empty stream; length 0; appends and reads;
 * reads past the end, also where position + length overflows a long; a read below the first
 * position after a cut; cuts within the length; cuts at the length, of an empty stream and
 * of one with bytes; a cut beyond the length, refused; the close. As C's callers do, a cut
 * of a directory follows a sync (reclaim's cut_if_durable): C cuts only the bytes in its
 * files (ERR_ARG past them), where Java's BufferedStream holds a cut beyond the flushed
 * bytes until they are written (testPretruncateBeyondFlushed). Not ported: the checks of a
 * negative or long append or read, as C's stream takes no caller's ranges (012-18, 3.3). */
#define CONTRACT_KINDS 5
static const char *const CONTRACT_KIND[CONTRACT_KINDS] = { "memory", "memory as storage",
    "directory, buffer 10,000", "directory, buffer 10,000, as storage", "directory" };

static bool contract_open(int kind, struct stream *s, struct mem *m) {
    struct err e;
    if (kind < 2) {
        stream_open_memory(s, m);
    } else if (!new_tdir("contract")
            || stream_open_dir_rw(s, tdir, kind == 4 ? 0 : 10000, m, &e) != ERR_OK) {
        return false;
    }
    if (kind == 1 || kind == 3) {
        stream_as_storage(s);
    }
    return true;
}

static void contract_close(int kind, struct stream *s) {
    struct err e;
    if (kind < 2) {
        stream_close(s);
    } else {
        CHECK_EQ(stream_finish(s, &e), ERR_OK);
        remove_tdir();
    }
}

/* A cut as the database makes it: a directory's after a sync. */
static enum err_code contract_cut(struct stream *s, int64_t pos, struct err *e) {
    enum err_code rc = stream_sync(s, e);
    return rc == ERR_OK ? stream_pretruncate(s, pos, e) : rc;
}

TEST(stream_contract) {
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[16];
    mem_init(&m);
    int checks = 0;
#ifdef BERGDB_TEST
    const int kinds = CONTRACT_KINDS;
    inj_set(INJ_NONE, PLAT_FORCE_SYNC, 0);
    plat_io_set(&NOFORCE);
#else
    const int kinds = 2;        /* the directories' forces take seconds without the seam */
#endif
    for (int kind = 0; kind < kinds; kind++) {
        int failed_before = (int) test_failed_checks_;
        /* An empty stream. */
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(stream_length(&s), 0);
        CHECK_EQ(stream_first_pos(&s), 0);
        CHECK_EQ(stream_read(&s, 0, b, 0, &e), ERR_OK);
        CHECK_EQ(stream_read(&s, 0, b, 1, &e), ERR_IO);
        CHECK(strcmp(e.java, "EOFException") == 0);
        contract_close(kind, &s);

        /* Length 0. */
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(stream_append(&s, b, 0, &e), ERR_OK);
        CHECK_EQ(stream_length(&s), 0);
        CHECK_EQ(append_at(&s, 10, &e), ERR_OK);
        CHECK_EQ(stream_append(&s, b, 0, &e), ERR_OK);
        CHECK_EQ(stream_length(&s), 10);
        CHECK_EQ(stream_read(&s, 10, b, 0, &e), ERR_OK);
        CHECK_EQ(stream_read(&s, 4, b, 0, &e), ERR_OK);
        CHECK(read_at(&s, 0, 10));
        contract_close(kind, &s);

        /* Appends and reads. */
        REQUIRE(contract_open(kind, &s, &m));
        const int32_t sizes[5] = { 1, 7, 1000, 70000, 3 };
        for (int i = 0; i < 5; i++) {
            CHECK_EQ(append_at(&s, sizes[i], &e), ERR_OK);
        }
        const int64_t length = stream_length(&s);
        CHECK_EQ(length, 71011);
        CHECK(read_at(&s, 0, (int32_t) length));
        CHECK(read_at(&s, 5, 10));
        CHECK(read_at(&s, length - 1, 1));
        CHECK(read_at(&s, 1000, 50000));
        contract_close(kind, &s);

        /* Reads past the end of 10 bytes; the last two: position + length overflows a long
         * (bergdb 021-14). */
        const int64_t past[5][2] = { { 10, 1 }, { 8, 4 }, { 1000, 1 }, { INT64_MAX, 1 },
            { INT64_MAX - 2, 4 } };
        for (int i = 0; i < 5; i++) {
            REQUIRE(contract_open(kind, &s, &m));
            CHECK_EQ(append_at(&s, 10, &e), ERR_OK);
            CHECK_EQ(stream_read(&s, past[i][0], b, (int32_t) past[i][1], &e), ERR_IO);
            CHECK(strcmp(e.java, "EOFException") == 0);
            CHECK(read_at(&s, 0, 10));
            contract_close(kind, &s);
        }

        /* A read below the first position, after a cut. */
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(append_at(&s, 1300000, &e), ERR_OK);
        CHECK_EQ(append_at(&s, 1200000, &e), ERR_OK);
        CHECK_EQ(contract_cut(&s, 2100000, &e), ERR_OK);
        CHECK_EQ(stream_length(&s), 2500000);
        int64_t first = stream_first_pos(&s);
        CHECK(first <= 2100000 && first > 0);
        CHECK(read_at(&s, 2100000, 1000));
        CHECK_EQ(stream_read(&s, first - 1, b, 1, &e), ERR_NOT_AVAILABLE);
        CHECK(strcmp(e.java, "ReadBelowFirstPosException") == 0);
        CHECK_EQ(append_at(&s, 10, &e), ERR_OK);
        CHECK(read_at(&s, 2100000, 400010));
        contract_close(kind, &s);

        /* Cuts within the length. */
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(append_at(&s, 1000, &e), ERR_OK);
        const int64_t cuts[4] = { 0, 300, 300, 999 };
        for (int i = 0; i < 4; i++) {
            CHECK_EQ(contract_cut(&s, cuts[i], &e), ERR_OK);
            CHECK_EQ(stream_length(&s), 1000);
            CHECK(stream_first_pos(&s) <= cuts[i]);
            CHECK(read_at(&s, cuts[i], (int32_t) (1000 - cuts[i])));
        }
        CHECK_EQ(append_at(&s, 5, &e), ERR_OK);
        CHECK(read_at(&s, 999, 6));
        contract_close(kind, &s);

        /* A cut at the length: 0, of an empty stream, and 3. */
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(contract_cut(&s, 0, &e), ERR_OK);
        CHECK_EQ(stream_length(&s), 0);
        CHECK_EQ(append_at(&s, 1, &e), ERR_OK);
        CHECK(read_at(&s, 0, 1));
        contract_close(kind, &s);
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(append_at(&s, 3, &e), ERR_OK);
        CHECK_EQ(contract_cut(&s, 3, &e), ERR_OK);
        CHECK_EQ(stream_length(&s), 3);
        CHECK_EQ(append_at(&s, 1, &e), ERR_OK);
        CHECK(read_at(&s, 3, 1));
        contract_close(kind, &s);

        /* A cut beyond the length: refused (ERR_ARG or ERR_IO), the stream as it was. */
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(append_at(&s, 10, &e), ERR_OK);
        first = stream_first_pos(&s);
        enum err_code rc = contract_cut(&s, 11, &e);
        CHECK(rc == ERR_ARG || rc == ERR_IO);
        CHECK(!s.failed);
        CHECK_EQ(stream_length(&s), 10);
        CHECK_EQ(stream_first_pos(&s), first);
        CHECK(read_at(&s, 0, 10));
        CHECK_EQ(append_at(&s, 5, &e), ERR_OK);
        CHECK(read_at(&s, 11, 4));
        CHECK(stream_first_pos(&s) <= 11);
        contract_close(kind, &s);

        /* The close. */
        REQUIRE(contract_open(kind, &s, &m));
        CHECK_EQ(append_at(&s, 5, &e), ERR_OK);
        contract_close(kind, &s);
        checks += 14;
        if (test_failed_checks_ != failed_before) {
            printf("    the contract on a %s failed\n", CONTRACT_KIND[kind]);
        }
    }
#ifdef BERGDB_TEST
    plat_io_set(NULL);
#endif
    printf("    the contract: %d checks on %d kinds of stream\n", checks, kinds);
    CHECK_MEM_ZERO(&m);
}

/* StorageContractTester.testWorkloadBufferedStream and testWorkloadStorageManager (seeds 1
 * and 2): a writer appends 1 to 3,000 bytes at a time, and now and then cuts, asks for the
 * length and the first position, and syncs; readers read what has been appended, at or
 * after the last cut, and compare it with what was. C has one caller: the reads come
 * between the writer's calls, two after each. On a directory with a buffer of 10,000 bytes,
 * about 600 kB, 16 cuts (each after a sync, as the database cuts) and files deleted (in
 * the test build with writes and no forces, as Java's NoForceIo); then the directory
 * opened again: its first position at or before the last cut, its bytes. */
TEST(stream_workload) {
    struct mem m;
    struct err e;
    struct stream s;
    mem_init(&m);
#ifdef BERGDB_TEST
    inj_set(INJ_NONE, PLAT_FORCE_SYNC, 0);
    plat_io_set(&NOFORCE);
#endif
#ifdef BERGDB_TEST
    const uint64_t seeds = 2;
#else
    const uint64_t seeds = 1;   /* the forces of a release build take longer */
#endif
    for (uint64_t seed = 1; seed <= seeds; seed++) {
        uint64_t random = seed;
        uint64_t rr = seed * 31;
        REQUIRE(new_tdir("workload"));
        REQUIRE(stream_open_dir_rw(&s, tdir, 10000, &m, &e) == ERR_OK);
        int64_t length = 0, cut = 0;
        int cuts = 0, reads = 0;
        bool ok = true;
        for (int op = 1; op <= 400 && ok; op++) {
            int32_t n = 1 + test_random_below(&random, 3000);
            ok &= append_at(&s, n, &e) == ERR_OK;
            length += n;
            if (op % 25 == 0 && length - cut > 20000) {
                cut = cut + test_random_below(&random, (int32_t) (length - cut - 10000));
                ok &= contract_cut(&s, cut, &e) == ERR_OK;
                cuts++;
            }
            if (op % 10 == 0) {
                ok &= stream_length(&s) == length;
                ok &= stream_first_pos(&s) <= cut;
            }
            if (op % 40 == 0) {
                ok &= stream_sync(&s, &e) == ERR_OK;
                ok &= stream_durable_length(&s) == length;
            }
            for (int r = 0; r < 2 && ok && length > cut; r++) {
                int64_t pos = cut + test_random(&rr) % (length - cut);
                pos = pos < cut ? pos + (length - cut) : pos;
                int64_t k = 1 + test_random_below(&rr, 4000);
                ok &= read_at(&s, pos, (int32_t) (length - pos < k ? length - pos : k));
                reads++;
            }
            if (!ok) {
                printf("    seed %d: op %d failed: %s %s\n", (int) seed, op, e.java, e.text);
            }
        }
        CHECK(ok);
        CHECK(cuts > 10);
        CHECK(s.files[0].start > 0);
        printf("    seed %d: %lld bytes, %d cuts, %d reads, %d files, the first at %lld\n",
                (int) seed, (long long) length, cuts, reads, (int) s.nfiles,
                (long long) s.files[0].start);
        CHECK_EQ(stream_finish(&s, &e), ERR_OK);
        REQUIRE(stream_open_dir(&s, tdir, &m, &e) == ERR_OK);
        CHECK_EQ(stream_length(&s), length);
        CHECK(stream_first_pos(&s) <= cut);
        CHECK(read_at(&s, cut, (int32_t) (length - cut)));
        stream_close(&s);
        remove_tdir();
    }
#ifdef BERGDB_TEST
    plat_io_set(NULL);
#endif
    CHECK_MEM_ZERO(&m);
}

/* FileStream.testLockFile (bergdb 005-63): bergdb.lock holds its text, is not a stream
 * file, and stays as it is through appends, a cut, a close and a new open; a directory
 * without it (as from 2026.1) opens and gets one, with the same text. */
TEST(stream_lock_file) {
    struct mem m;
    struct err e;
    struct stream s;
    char lock[512];
    static uint8_t text[1024], again[1024];
    mem_init(&m);
    REQUIRE(new_tdir("lockfile"));
    snprintf(lock, sizeof lock, "%s/bergdb.lock", tdir);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    FILE *f = fopen(lock, "rb");
    REQUIRE(f != NULL);
    size_t n = fread(text, 1, sizeof text, f);
    fclose(f);
    CHECK_EQ((int64_t) n, 225);
    CHECK(memcmp(text, "This directory contains a BergDB database.", 42) == 0);
    REQUIRE(append_at(&s, 500000, &e) == ERR_OK);
    CHECK_EQ(contract_cut(&s, 200000, &e), ERR_OK);
    CHECK_EQ(s.nfiles, 2);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    for (int round = 0; round < 3; round++) {
        if (round == 2) {
            CHECK_EQ(unlink(lock), 0);
        }
        REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
        CHECK_EQ(s.nfiles, 2);
        CHECK_EQ(stream_first_pos(&s), 200000);
        CHECK(read_at(&s, 300000, 1000));
        if (round == 0) {
            CHECK_EQ(append_at(&s, 1000, &e), ERR_OK);
        }
        CHECK_EQ(stream_finish(&s, &e), ERR_OK);
        f = fopen(lock, "rb");
        REQUIRE(f != NULL);
        size_t n2 = fread(again, 1, sizeof again, f);
        fclose(f);
        CHECK_EQ((int64_t) n2, (int64_t) n);
        CHECK(memcmp(again, text, n) == 0);
    }
    remove_tdir();
    CHECK_MEM_ZERO(&m);
}

/* FileStream.testReopenPast214TB (bergdb 005-19): a stream past 2^31 * 100,000 bytes (214.7
 * TB) opens again; the file names were parsed as ints. Java makes the position with
 * seekFirstPos, which C has not: here the empty file at it is made by hand, named by its
 * index, 2^31. The stream opens at it, takes appends, makes the next file's name, and
 * opens again, for writing and read-only, with its bytes. */
TEST(stream_reopen_past_214tb) {
    struct mem m;
    struct err e;
    struct stream s;
    const int64_t pos = (INT64_C(1) << 31) * STREAM_INDEX_UNIT;
    mem_init(&m);
    REQUIRE(new_tdir("past214tb"));
    write_file("00002147483648.bergdb", 0, 0);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK_EQ(stream_first_pos(&s), pos);
    CHECK_EQ(stream_length(&s), pos);
    uint8_t b[3] = { 1, 2, 3 };
    CHECK_EQ(stream_append(&s, b, 3, &e), ERR_OK);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK_EQ(stream_first_pos(&s), pos);
    CHECK_EQ(stream_length(&s), pos + 3);
    memset(b, 0, 3);
    CHECK_EQ(stream_read(&s, pos, b, 3, &e), ERR_OK);
    CHECK(b[0] == 1 && b[1] == 2 && b[2] == 3);
    CHECK_EQ(append_at(&s, 199997 + 10, &e), ERR_OK);       /* the next file at pos + 200,000 */
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    CHECK(tdir_has("00002147483650.bergdb"));
    REQUIRE(stream_open_dir(&s, tdir, &m, &e) == ERR_OK);
    CHECK_EQ(stream_first_pos(&s), pos);
    CHECK_EQ(stream_length(&s), pos + 200010);
    CHECK_EQ(s.nfiles, 2);
    CHECK(read_at(&s, pos + 200000, 10));
    stream_close(&s);
    remove_tdir();
    CHECK_MEM_ZERO(&m);
}

/* FileStream.testForcingOffForcesAtClose (bergdb 005-47): a close forces the last file, so
 * that a clean stop is durable (C's close syncs first, stream_finish: SYNC), and the bytes
 * are read again after a new open. Nothing is forced before: an append is buffered (C's
 * write buffer; Java's appends are written, not forced). C has no second close. */
TEST(stream_forces_at_close) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    uint8_t b[2] = { 4, 7 };
    mem_init(&m);
    REQUIRE(new_tdir("closeforce"));
    flog[0] = '\0';
    plat_io_set(&FLOG);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK_EQ(stream_append(&s, b, 2, &e), ERR_OK);
    CHECK(strcmp(flog, "") == 0);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    CHECK(strcmp(flog, "open 0 OPEN 0 dir write 0 SYNC 0") == 0);
    plat_io_set(NULL);
    REQUIRE(stream_open_dir(&s, tdir, &m, &e) == ERR_OK);
    memset(b, 0, 2);
    CHECK_EQ(stream_read(&s, 0, b, 2, &e), ERR_OK);
    CHECK(b[0] == 4 && b[1] == 7);
    stream_close(&s);
    remove_tdir();
    CHECK_MEM_ZERO(&m);
#endif
}

/* A database in memory frees what reclaim cuts (MemoryStream.pretruncate drops its arrays
 * below the cut; bergdb 022-05): with the retain duration one second and 1,200
 * transactions of 8,000 bytes, 0.1 s apart, the stream is about 9.7 MB and reclaim's cuts
 * leave little of it available; the stream's buffer then holds that, not the whole stream.
 * The values read again after an eviction (a budget of 100,000 bytes) come from the
 * stream's bytes that the cuts kept. Before, C's memory stream freed nothing at a cut: its
 * buffer was 16.8 MB here (the doubled allocation of the whole stream). */
TEST(stream_memory_database_frees_cut_bytes) {
    struct bergdb_mem bm = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_executed ex;
    struct bergdb_stats st;
    bergdb_db *db;
    bergdb_trans *t;
    bergdb_read *rd;
    static uint8_t v[8000];
    uint8_t key[16];
    char ik[16];
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.mem = &bm;
    o.startup_distance = 100000;
    bergdb_test_clock_set(&clock, 1000000);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    REQUIRE(bergdb_set_retain_duration(db, 10000000) == BERGDB_OK);    /* one second */
    const int n = 1200;
    for (int i = 0; i < n; i++) {
        bergdb_test_clock_set(&clock, 1000000 + 1000000 * (int64_t) (i + 1));
        snprintf(ik, sizeof ik, "/k/%d", i % 50);
        REQUIRE(bergdb_ikey_to_bkey((const uint8_t *) ik, strlen(ik), key) == BERGDB_OK);
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        v[0] = (uint8_t) i;
        v[1] = (uint8_t) (i >> 8);
        v[7999] = (uint8_t) (i * 7);
        REQUIRE(bergdb_trans_put(t, key, strlen(ik), v, sizeof v) == BERGDB_OK);
        CHECK_EQ(bergdb_execute(db, t, &ex), BERGDB_OK);
        bergdb_trans_free(t);
    }
    REQUIRE(bergdb_stats(db, &st) == BERGDB_OK);
    const int64_t buffer = bm.live[BERGDB_MEM_BUFFER];
    printf("    the stream %lld bytes, the first available position %lld, the stream's buffer "
            "%lld bytes\n", (long long) st.stream_length, (long long) st.first_available_pos,
            (long long) buffer);
    CHECK(st.stream_length > 9000000);
    CHECK(st.first_available_pos > st.stream_length - 3000000);
    CHECK(buffer < 5000000);
    /* Read again from the stream's bytes: each key's last value. */
    REQUIRE(bergdb_set_cache_size_indicator(db, 100000) == BERGDB_OK);
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    int64_t now;
    REQUIRE(bergdb_current_time(db, &now) == BERGDB_OK);
    for (int k = 0; k < 50; k++) {
        const int i = n - 50 + k;          /* n is a multiple of 50 */
        snprintf(ik, sizeof ik, "/k/%d", k);
        REQUIRE(bergdb_ikey_to_bkey((const uint8_t *) ik, strlen(ik), key) == BERGDB_OK);
        struct bergdb_one one;
        CHECK_EQ(bergdb_get_one(db, rd, now, key, strlen(ik), &one), BERGDB_OK);
        CHECK(one.value != NULL && one.value_len == sizeof v);
        if (one.value != NULL && one.value_len == sizeof v) {
            CHECK_EQ(one.value[0] | one.value[1] << 8, i);
            CHECK_EQ(one.value[7999], (uint8_t) (i * 7));
        }
    }
    bergdb_read_free(rd);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(bm.live_total, 0);
}

#ifdef BERGDB_TEST
/* A seam that makes chosen calls fail, as Java's ModelIo of FileStreamPowerLossTester
 * (failFileForce, failDirectoryForce, failDeleteAt): every file force, every directory
 * force, or the Nth delete, with an IOException; the others pass on. It counts the deletes
 * made and keeps the stream files open, so that a test can see that none is left open. */
static bool ff_file, ff_dir;
static int ff_unlink_at, ff_unlinks, ff_deleted, ff_open;
static enum err_code ff_open_rw(const char *path, int *fd, struct err *e) {
    enum err_code rc = plat_io_real()->open_rw(path, fd, e);
    if (rc == ERR_OK && *fd >= 0 && *fd < 256) {
        flog_fd_index[*fd] = flog_index(path) + 1;
        if (flog_fd_index[*fd] > 0) {
            ff_open++;
        }
    }
    return rc;
}
static enum err_code ff_pwrite(int fd, int64_t off, const uint8_t *buf, int64_t n,
        struct err *e) {
    return plat_io_real()->pwrite(fd, off, buf, n, e);
}
static enum err_code ff_force(int fd, enum plat_force_why why, struct err *e) {
    if (ff_file) {
        return err_set(e, ERR_IO, "IOException", "injected file force failure");
    }
    return plat_io_real()->force(fd, why, e);
}
static enum err_code ff_force_dir(const char *dir, struct err *e) {
    if (ff_dir) {
        return err_set(e, ERR_IO, "IOException", "injected directory force failure");
    }
    return plat_io_real()->force_dir(dir, e);
}
static enum err_code ff_unlink(const char *path, struct err *e) {
    if (++ff_unlinks == ff_unlink_at) {
        return err_set(e, ERR_IO, "IOException", "injected delete failure");
    }
    enum err_code rc = plat_io_real()->unlink(path, e);
    ff_deleted += rc == ERR_OK;
    return rc;
}
static void ff_close(int fd) {
    if (fd >= 0 && fd < 256 && flog_fd_index[fd] > 0) {
        flog_fd_index[fd] = 0;
        ff_open--;
    }
    plat_io_real()->close(fd);
}
static const struct plat_io FF = {
    ff_open_rw, ff_pwrite, ff_force, ff_force_dir, ff_unlink, ff_close
};

/* A new directory for the failure tests, the seam set, nothing to fail. */
static void ff_start(void) {
    const char *tmp = getenv("TMPDIR");
    snprintf(tdir, sizeof tdir, "%s/bergdb-t_ffail-XXXXXX", tmp != NULL ? tmp : "/tmp");
    ff_file = ff_dir = false;
    ff_unlink_at = ff_unlinks = ff_deleted = ff_open = 0;
    memset(flog_fd_index, 0, sizeof flog_fd_index);
    plat_io_set(&FF);
}

static void ff_end(void) {
    char cmd[400];
    plat_io_set(NULL);
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", tdir);
    if (system(cmd) != 0) {
        printf("    could not remove %s\n", tdir);
    }
}
#endif

/* FileStreamPowerLossTester.testSyncDoesNotAdvanceAfterFailedFileForce and
 * testSyncDoesNotAdvanceAfterFailedDirectoryForce, with testDurableFrontierWaitsForForce's
 * check: the durable length is the length at the last force that succeeded. Bytes appended
 * or written (a flush) are not durable; a sync makes them so. A sync whose file force or
 * directory force fails returns the error, leaves the durable length as it was (0 here, of
 * a new stream's 100 bytes or 200,100, which make a second file; and 100 when the force of
 * a sync after a first one fails), and fails the stream, which takes no more writes or
 * syncs; its close gives the error too and leaves no stream file open. (Java's: the failed
 * force through StorageManager, whose sync throws; C's sync is the call.) Before the fix of
 * stream_flush (bergdb 022-05), a sync after the failed force of a sync forced the files
 * again, and with a force that worked gave ERR_OK and the durable length 200, as did the
 * close: the stream's failure was checked only when the buffer held bytes. */
TEST(stream_failed_force_keeps_the_durable_length) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    static uint8_t data[200100];
    mem_init(&m);
    /* The durable length waits for the force. */
    ff_start();
    REQUIRE(mkdtemp(tdir) != NULL);
    REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
    CHECK_EQ(stream_append(&s, data, 100, &e), ERR_OK);
    CHECK_EQ(stream_durable_length(&s), 0);
    CHECK_EQ(stream_flush(&s, &e), ERR_OK);
    CHECK_EQ(stream_durable_length(&s), 0);
    CHECK_EQ(stream_sync(&s, &e), ERR_OK);
    CHECK_EQ(stream_durable_length(&s), 100);
    CHECK_EQ(stream_finish(&s, &e), ERR_OK);
    CHECK_EQ(ff_open, 0);
    ff_end();
    /* A failed force: of a new file, of the directory, of a file at a later sync. */
    for (int k = 0; k < 3; k++) {
        const int64_t n = k == 1 ? 200100 : 100;
        const int64_t durable = k == 2 ? 100 : 0;
        ff_start();
        REQUIRE(mkdtemp(tdir) != NULL);
        REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
        if (k == 2) {
            CHECK_EQ(stream_append(&s, data, 100, &e), ERR_OK);
            CHECK_EQ(stream_sync(&s, &e), ERR_OK);
        }
        ff_file = k != 1;
        ff_dir = k == 1;
        CHECK_EQ(stream_append(&s, data, n, &e), ERR_OK);
        CHECK_EQ(stream_sync(&s, &e), ERR_IO);
        CHECK(strstr(e.text, "injected") != NULL);
        CHECK_EQ(stream_durable_length(&s), durable);
        ff_file = ff_dir = false;
        CHECK_EQ(stream_sync(&s, &e), ERR_IO);      /* the stream has failed */
        CHECK_EQ(stream_durable_length(&s), durable);
        CHECK_EQ(stream_append(&s, data, 10, &e), ERR_IO);
        CHECK(strcmp(e.text, "The stream has failed: no more writes.") == 0);
        CHECK_EQ(stream_finish(&s, &e), ERR_IO);
        CHECK_EQ(ff_open, 0);                       /* no stream file left open */
        ff_end();
    }
    CHECK_MEM_ZERO(&m);
#endif
}

/* FileStreamPowerLossTester.testPartialDeletionAndDirectoryFailureKeepForcedBytes and
 * testPendingCutForceFailureFailsTheStream: a cut whose second delete fails, or whose
 * directory force after its first delete fails, stops there (one file deleted), returns the
 * error and fails the stream: no more writes or syncs, and the durable length stays the
 * last sync's; the files left hold the forced bytes, and a new stream on the directory
 * reads them (the tail from 800,000). The cut's failure comes from the cut's call here,
 * where Java's cut thread passes it on to the stream's next operation (C has no thread,
 * c/readme.md, section 9, point 9). And the cut without a failure deletes the four files
 * before 800,000, one at a time (testRecoveryBetweenEveryPrefixDeletion's count). */
TEST(stream_failed_cut_keeps_forced_bytes) {
#ifdef BERGDB_TEST
    struct mem m;
    struct err e;
    struct stream s;
    static uint8_t data[1000000];
    static uint8_t tail[200000];
    mem_init(&m);
    memset(data, 7, sizeof data);
    for (int k = 0; k < 3; k++) {
        ff_start();
        REQUIRE(mkdtemp(tdir) != NULL);
        REQUIRE(stream_open_dir_rw(&s, tdir, 0, &m, &e) == ERR_OK);
        CHECK_EQ(stream_append(&s, data, (int64_t) sizeof data, &e), ERR_OK);
        CHECK_EQ(stream_sync(&s, &e), ERR_OK);
        CHECK_EQ(stream_durable_length(&s), 1000000);
        if (k == 0) {
            ff_unlink_at = 2;
        } else if (k == 1) {
            ff_dir = true;
        }
        enum err_code rc = stream_pretruncate(&s, 800000, &e);
        CHECK_EQ(ff_deleted, k < 2 ? 1 : 4);
        if (k < 2) {
            CHECK_EQ(rc, ERR_IO);
            CHECK(strstr(e.text, "injected") != NULL);
            ff_unlink_at = 0;
            ff_dir = false;
            CHECK_EQ(stream_append(&s, data, 100, &e), ERR_IO);
            CHECK_EQ(stream_sync(&s, &e), ERR_IO);
            CHECK_EQ(stream_durable_length(&s), 1000000);
            CHECK_EQ(stream_finish(&s, &e), ERR_IO);
        } else {
            CHECK_EQ(rc, ERR_OK);
            CHECK_EQ(stream_first_pos(&s), 800000);
            CHECK_EQ(stream_finish(&s, &e), ERR_OK);
        }
        CHECK_EQ(ff_open, 0);
        plat_io_set(NULL);
        /* The files left, read by a new stream. */
        REQUIRE(stream_open_dir(&s, tdir, &m, &e) == ERR_OK);
        CHECK_EQ(stream_first_pos(&s), k < 2 ? 200000 : 800000);
        CHECK_EQ(stream_length(&s), 1000000);
        memset(tail, 0, sizeof tail);
        CHECK_EQ(stream_read(&s, 800000, tail, (int32_t) sizeof tail, &e), ERR_OK);
        bool all = true;
        for (size_t i = 0; i < sizeof tail; i++) {
            all = all && tail[i] == 7;
        }
        CHECK(all);
        stream_close(&s);
        ff_end();
    }
    CHECK_MEM_ZERO(&m);
#endif
}

const struct test stream_tests[] = {
    TEST_ENTRY(stream_memory),
    TEST_ENTRY(stream_dir),
    TEST_ENTRY(stream_storage),
    TEST_ENTRY(stream_read_past_end_near_max_value),
    TEST_ENTRY(stream_seam),
    TEST_ENTRY(stream_forces),
    TEST_ENTRY(stream_new_file_forces),
    TEST_ENTRY(stream_failed_open),
    TEST_ENTRY(stream_failure_refuses_writes),
    TEST_ENTRY(stream_failed_force_fails_the_database),
    TEST_ENTRY(stream_read_below_first_pos),
    TEST_ENTRY(stream_read_past_end),
    TEST_ENTRY(stream_read_from_buffer_nonempty),
    TEST_ENTRY(stream_contract),
    TEST_ENTRY(stream_workload),
    TEST_ENTRY(stream_lock_file),
    TEST_ENTRY(stream_reopen_past_214tb),
    TEST_ENTRY(stream_forces_at_close),
    TEST_ENTRY(stream_memory_database_frees_cut_bytes),
    TEST_ENTRY(stream_failed_force_keeps_the_durable_length),
    TEST_ENTRY(stream_failed_cut_keeps_forced_bytes),
    TEST_END
};
