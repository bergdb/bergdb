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

const struct test stream_tests[] = {
    TEST_ENTRY(stream_memory),
    TEST_ENTRY(stream_dir),
    TEST_END
};
