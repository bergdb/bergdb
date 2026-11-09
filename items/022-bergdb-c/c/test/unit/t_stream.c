/*
 * Unit tests of stream (bergdb 012-06): the memory stream's reads and
 * refusals (MemoryStream), and a directory read as Java's FileStream reads
 * it: the files found, checked and ordered, reads across them, and the
 * refusals of BadDirStateException.
 */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <stdlib.h>
#include <unistd.h>
#include "test.h"
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

const struct test stream_tests[] = {
    TEST_ENTRY(stream_memory),
    TEST_ENTRY(stream_dir),
    TEST_ENTRY(stream_seam),
    TEST_ENTRY(stream_forces),
    TEST_ENTRY(stream_new_file_forces),
    TEST_END
};
