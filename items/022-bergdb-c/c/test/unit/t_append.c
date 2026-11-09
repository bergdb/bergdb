/*
 * Unit tests of the append path (bergdb 012-09, part 1): RecoverableStream's
 * appends (rstream: the framing, the meta blocks written where the records
 * reach them, with the in-memory block's bytes, the checks), and a
 * directory written as Java's FileStream writes it (stream: the first file,
 * the capacities and their rules, the open rule at a restart, 012-02, 9.3,
 * C1, the lock file, the write buffer, sync and close). Java's tests of
 * both classes are ported where C has what they test.
 */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
#include "test.h"
#include "bytes.h"
#include "rstream.h"
#include "stream.h"

static char adir[256];
static struct mem am;
static struct err ae;

/* A fresh temporary directory path (not made: FileStream makes it). */
static bool new_dir(void) {
    const char *tmp = getenv("TMPDIR");
    snprintf(adir, sizeof adir, "%s/bergdb-t_append-XXXXXX", tmp != NULL ? tmp : "/tmp");
    if (mkdtemp(adir) == NULL) {
        return false;
    }
    rmdir(adir);
    return true;
}

static void remove_dir(void) {
    DIR *d = opendir(adir);
    struct dirent *x;
    char path[512];
    if (d == NULL) {
        return;
    }
    while ((x = readdir(d)) != NULL) {
        if (x->d_name[0] == '.') {
            continue;
        }
        snprintf(path, sizeof path, "%s/%s", adir, x->d_name);
        unlink(path);
    }
    closedir(d);
    rmdir(adir);
}

static int64_t file_size(const char *name) {
    char path[512];
    struct stat st;
    snprintf(path, sizeof path, "%s/%s", adir, name);
    return stat(path, &st) == 0 ? (int64_t) st.st_size : -1;
}

/* The names of the .bergdb files and their sizes, as "NAME:SIZE ...". */
static void layout(char *out, size_t size) {
    struct dirent **list;
    int n = scandir(adir, &list, NULL, alphasort);
    size_t at = 0;
    out[0] = '\0';
    for (int i = 0; i < n; i++) {
        const char *name = list[i]->d_name;
        size_t len = strlen(name);
        if (len > 7 && strcmp(name + len - 7, ".bergdb") == 0 && at < size) {
            at += (size_t) snprintf(out + at, size - at, "%.*s:%lld ", (int) (len - 7), name,
                    (long long) file_size(name));
        }
        free(list[i]);
    }
    free(list);
}

static uint8_t zeros[1000000];

/* ---- rstream ---- */

/* A record of 'size' bytes: its size field, then 'fill', the last byte 10. */
static uint8_t *record(int32_t size, uint8_t fill) {
    uint8_t *b = mem_alloc(&am, (size_t) size, MEM_BUFFER);
    memset(b, fill, (size_t) size);
    bytes_put_int_le(size, b);
    b[size - 1] = RS_LAST_BYTE;
    return b;
}

/* RecoverableStream.Tester.test1: the block at 0 first, then the record. */
TEST(append_rs_test1) {
    struct stream s;
    struct rs r;
    mem_init(&am);
    stream_open_memory(&s, &am);
    rs_init(&r, &s);
    uint8_t *t = record(20, 0);
    CHECK_EQ(rs_append(&r, t, 20, true, &ae), ERR_OK);
    CHECK_EQ(stream_length(&s), META_BLOCK_SIZE + 20);
    /* The block's bytes are the in-memory block's: "berg", 154, lastTrans
     * -1, the last byte 10. */
    uint8_t b[META_BLOCK_SIZE];
    CHECK_EQ(stream_read(&s, 0, b, META_BLOCK_SIZE, &ae), ERR_OK);
    CHECK_BYTES(b, r.meta.block, META_BLOCK_SIZE);
    CHECK_EQ(bytes_get_long_le(b + 16), -1);
    CHECK_EQ(b[127], 10);
    CHECK_EQ(r.posOfLastValidMetaBlock, 0);
    CHECK_EQ(r.lastTransSposOfLastValidMetaBlock, -1);
    mem_free(&am, t, 20, MEM_BUFFER);
    stream_close(&s);
    CHECK_MEM_ZERO(&am);
}

/* RecoverableStream.Tester.largeTransaction: a record over three blocks. */
TEST(append_rs_large) {
    struct stream s;
    struct rs r;
    const int32_t size = 3 * META_BLOCK_DISTANCE + 20;
    mem_init(&am);
    stream_open_memory(&s, &am);
    rs_init(&r, &s);
    uint8_t *t = record(size, 7);
    CHECK_EQ(rs_append(&r, t, size, true, &ae), ERR_OK);
    CHECK_EQ(stream_length(&s), (int64_t) size + 4 * META_BLOCK_SIZE);
    /* The record's bytes read back across the blocks. */
    uint8_t *back = mem_alloc(&am, (size_t) size, MEM_BUFFER);
    CHECK_EQ(rs_read(&s, META_BLOCK_SIZE, back, size, &ae), ERR_OK);
    CHECK_BYTES(back, t, (size_t) size);
    CHECK_EQ(r.posOfLastValidMetaBlock, 3 * META_BLOCK_DISTANCE);
    mem_free(&am, back, (size_t) size, MEM_BUFFER);
    mem_free(&am, t, (size_t) size, MEM_BUFFER);
    stream_close(&s);
    CHECK_MEM_ZERO(&am);
}

/* appendNamedTransactions: records of 1000 bytes, each block names the
 * record before it; a record that ends at a block writes it ("size >=
 * distanceToMeta") and the next begins after it. */
TEST(append_rs_named) {
    struct stream s;
    struct rs r;
    mem_init(&am);
    stream_open_memory(&s, &am);
    rs_init(&r, &s);
    uint8_t *t = record(1000, 1);
    int64_t pos[450];
    for (int i = 0; i < 450; i++) {
        REQUIRE(rs_append_record(&r, t, 1000, &pos[i], &ae) == ERR_OK);
    }
    CHECK_EQ(pos[0], META_BLOCK_SIZE);
    CHECK_EQ(meta_last_trans(&r.meta), pos[449]);
    /* The block at 200,000: inside record 199 (128 + 199 * 1000 = 199,128
     * to 200,127 with the block), so it names record 198. */
    uint8_t b[META_BLOCK_SIZE];
    CHECK_EQ(stream_read(&s, META_BLOCK_DISTANCE, b, META_BLOCK_SIZE, &ae), ERR_OK);
    CHECK_EQ(bytes_get_long_le(b + 16), pos[198]);
    CHECK_EQ(pos[200], rs_get_spos(pos[199], 1000));
    mem_free(&am, t, 1000, MEM_BUFFER);

    /* A record that ends exactly at the block writes it, and names the
     * record before it. */
    struct stream s2;
    struct rs r2;
    stream_open_memory(&s2, &am);
    rs_init(&r2, &s2);
    int64_t p1, p2;
    const int32_t n1 = META_BLOCK_DISTANCE - META_BLOCK_SIZE;
    uint8_t *t1 = record(n1, 2);
    CHECK_EQ(rs_append_record(&r2, t1, n1, &p1, &ae), ERR_OK);
    CHECK_EQ(stream_length(&s2), META_BLOCK_DISTANCE + META_BLOCK_SIZE);
    CHECK_EQ(stream_read(&s2, META_BLOCK_DISTANCE, b, META_BLOCK_SIZE, &ae), ERR_OK);
    CHECK_EQ(bytes_get_long_le(b + 16), -1);
    uint8_t *t2 = record(16, 3);
    CHECK_EQ(rs_append_record(&r2, t2, 16, &p2, &ae), ERR_OK);
    CHECK_EQ(p2, META_BLOCK_DISTANCE + META_BLOCK_SIZE);
    mem_free(&am, t1, (size_t) n1, MEM_BUFFER);
    mem_free(&am, t2, 16, MEM_BUFFER);
    stream_close(&s);
    stream_close(&s2);
    CHECK_MEM_ZERO(&am);
}

/* append's checks, before anything is written. */
TEST(append_rs_checks) {
    struct stream s;
    struct rs r;
    mem_init(&am);
    stream_open_memory(&s, &am);
    rs_init(&r, &s);
    uint8_t *t = record(24, 0);
    t[23] = 0;
    CHECK_EQ(rs_append(&r, t, 24, true, &ae), ERR_ARG);
    CHECK(strcmp(ae.text, "Last byte of transaction must be 10") == 0);
    t[23] = RS_LAST_BYTE;
    bytes_put_int_le(25, t);
    CHECK_EQ(rs_append(&r, t, 24, true, &ae), ERR_ARG);
    CHECK(strcmp(ae.text, "Bad transactionSize in byte buffer, was 25, expected 24") == 0);
    CHECK_EQ(stream_length(&s), 0);
    /* Without the checks, as recovery's fill appends. */
    CHECK_EQ(rs_append(&r, t, 24, false, &ae), ERR_OK);
    bytes_put_int_le(24, t);
    /* A stream that ends in a meta block. */
    CHECK_EQ(stream_truncate_memory(&s, 100, &ae), ERR_OK);
    CHECK_EQ(rs_append(&r, t, 24, true, &ae), ERR_FORMAT);
    CHECK(strcmp(ae.text, "Bad state, in the middle of a meta block, 100, 100.") == 0);
    CHECK_EQ(stream_length(&s), 100);
    mem_free(&am, t, 24, MEM_BUFFER);
    stream_close(&s);
    CHECK_MEM_ZERO(&am);
}

/* A start's copy of the last valid block (recovery's steps 1 and 3), its
 * reserved bytes included; none: the refusal. */
TEST(append_rs_last_valid) {
    struct stream s;
    struct rs r, r2;
    mem_init(&am);
    stream_open_memory(&s, &am);
    rs_init(&r2, &s);
    /* An empty stream: the read of the block at 0 fails (Java's
     * StreamIoException). */
    CHECK_EQ(rs_use_last_valid_meta_block(&r2, &ae), ERR_IO);
    /* Only an invalid block: refused. */
    struct stream s0;
    struct rs r0;
    stream_open_memory(&s0, &am);
    rs_init(&r0, &s0);
    r0.meta.block[META_BLOCK_SIZE - 1] = 0;
    uint8_t *t0 = record(24, 0);
    CHECK_EQ(rs_append(&r0, t0, 24, true, &ae), ERR_OK);
    CHECK_EQ(rs_use_last_valid_meta_block(&r0, &ae), ERR_FORMAT);
    CHECK(strstr(ae.text, "Could not find *any* valid meta block") != NULL);
    mem_free(&am, t0, 24, MEM_BUFFER);
    stream_close(&s0);

    rs_init(&r, &s);
    meta_set_startup_distance(&r.meta, 12345);
    meta_set_max_node_size(&r.meta, 14);
    r.meta.block[100] = 77;         /* a reserved byte */
    uint8_t *t = record(300000, 4);
    int64_t p;
    CHECK_EQ(rs_append_record(&r, t, 300000, &p, &ae), ERR_OK);
    meta_set_startup_distance(&r.meta, 999);    /* not written */
    CHECK_EQ(rs_use_last_valid_meta_block(&r2, &ae), ERR_OK);
    CHECK_EQ(r2.posOfLastValidMetaBlock, META_BLOCK_DISTANCE);
    CHECK_EQ(meta_startup_distance(&r2.meta), 12345);
    CHECK_EQ(meta_max_node_size(&r2.meta), 14);
    CHECK_EQ(r2.meta.block[100], 77);
    CHECK_EQ(meta_last_trans(&r2.meta), -1);
    mem_free(&am, t, 300000, MEM_BUFFER);
    stream_close(&s);
    CHECK_MEM_ZERO(&am);
}

/* ---- the directory ---- */

/* FileStream.test0, test1 and testRestart0. */
TEST(append_dir_test0) {
    struct stream s;
    uint8_t b[1] = { 123 };
    char text[300];
    mem_init(&am);
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_first_pos(&s), 0);
    CHECK_EQ(stream_length(&s), 0);
    CHECK_EQ(file_size("00000000000000.bergdb"), -1);      /* made by the first write */
    CHECK_EQ(stream_append(&s, b, 1, &ae), ERR_OK);
    CHECK_EQ(stream_length(&s), 1);
    b[0] = 0;
    CHECK_EQ(stream_read(&s, 0, b, 1, &ae), ERR_OK);       /* from the buffer */
    CHECK_EQ(b[0], 123);
    CHECK_EQ(file_size("00000000000000.bergdb"), -1);
    CHECK_EQ(stream_durable_length(&s), 0);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    CHECK_EQ(file_size("00000000000000.bergdb"), 1);

    /* The lock file, with Java's text (FileStream.LOCK_TEXT, 225 bytes). */
    CHECK_EQ(file_size("bergdb.lock"), 225);
    snprintf(text, sizeof text, "%s/bergdb.lock", adir);
    FILE *f = fopen(text, "r");
    REQUIRE(f != NULL);
    size_t n = fread(text, 1, sizeof text - 1, f);
    fclose(f);
    text[n] = '\0';
    CHECK(strncmp(text, "This directory contains a BergDB database. BergDB locks this file\n",
            66) == 0);

    /* testRestart0. */
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_length(&s), 1);
    CHECK_EQ(stream_read(&s, 0, b, 1, &ae), ERR_OK);
    CHECK_EQ(b[0], 123);
    stream_close(&s);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

/* FileStream.testBigAppend0 and tFileSizeIncrease: 200,000-byte files
 * until the stream is 4 MB, then 1,000,000. */
TEST(append_dir_sizes) {
    struct stream s;
    char got[4096];
    mem_init(&am);
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 10000, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 234000, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 445000, &ae), ERR_OK);
    CHECK_EQ(stream_length(&s), (10 + 234 + 445) * 1000);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    layout(got, sizeof got);
    CHECK(strcmp(got, "00000000000000:200000 00000000000002:200000 00000000000004:200000 "
            "00000000000006:89000 ") == 0);
    remove_dir();

    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    for (int i = 0; i < 50; i++) {
        CHECK_EQ(stream_append(&s, zeros, 100000, &ae), ERR_OK);
    }
    CHECK_EQ(s.nfiles, 0);                  /* in the buffer so far, no file yet */
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    CHECK_EQ(s.nfiles, 21);
    CHECK_EQ(s.files[0].length, 200000);
    CHECK_EQ(s.files[20].length, 1000000);
    CHECK_EQ(stream_durable_length(&s), 5000000);
    stream_close(&s);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

/* FileStream.testFileSizeRules0, and the rule's other cases: up only at a
 * multiple of the next size, down at once. */
TEST(append_dir_size_rules) {
    CHECK_EQ(stream_file_size_index(0, 5000000, 5000000), 1);
    CHECK_EQ(stream_file_size_index(0, 3000000, 3000000), 0);
    CHECK_EQ(stream_file_size_index(0, 4200000, 4200000), 0);       /* not at 1 MB */
    CHECK_EQ(stream_file_size_index(0, 5000000, 4200000), 1);
    CHECK_EQ(stream_file_size_index(1, 20000000, 20000000), 2);
    CHECK_EQ(stream_file_size_index(1, 21000000, 21000000), 1);     /* not at 5 MB */
    CHECK_EQ(stream_file_size_index(0, 40000000, 40000000), 2);     /* a jump, at 1 MB */
    CHECK_EQ(stream_file_size_index(2, 30000000, 1000000), 0);      /* down at once */
    CHECK_EQ(stream_file_size_index(STREAM_FILE_SIZES - 1, INT64_C(4000000000000),
            INT64_C(4000000000000)), STREAM_FILE_SIZES - 1);
    /* testFileSizeRules1 without max2G (C has no such setting). */
    CHECK_EQ(stream_file_size_index(6, INT64_C(50000000000), INT64_C(50000000000)), 7);
}

/* C1 (012-02, 10.3; FileLayoutProbe): a restart reopens the last file with
 * the capacity of the larger of the last two files; from 4.0 MB, a 1 MB
 * file reopened at 104,880 bytes after a file of 200,000 takes 200,000,
 * and files of 200,000 follow until 5 MB. */
TEST(append_dir_restart_layout) {
    struct stream s;
    char got[4096];
    mem_init(&am);
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 1000, &am, &ae), ERR_OK);
    for (int i = 0; i < 41; i++) {
        CHECK_EQ(stream_append(&s, zeros, 100000, &ae), ERR_OK);
    }
    CHECK_EQ(stream_append(&s, zeros, 4880, &ae), ERR_OK);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    CHECK_EQ(file_size("00000000000040.bergdb"), 104880);
    CHECK_EQ(stream_open_dir_rw(&s, adir, 1000, &am, &ae), ERR_OK);
    CHECK_EQ(s.maxSize, 200000);
    for (int i = 0; i < 19; i++) {
        CHECK_EQ(stream_append(&s, zeros, 50000, &ae), ERR_OK);
    }
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    layout(got, sizeof got);
    CHECK(strstr(got, "00000000000038:200000 00000000000040:200000 00000000000042:200000 "
            "00000000000044:200000 00000000000046:200000 00000000000048:200000 "
            "00000000000050:54880 ") != NULL);

    /* Without the restart: one file of 1,000,000 from 4.0 MB. */
    remove_dir();
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 1000, &am, &ae), ERR_OK);
    for (int i = 0; i < 41; i++) {
        CHECK_EQ(stream_append(&s, zeros, 100000, &ae), ERR_OK);
    }
    CHECK_EQ(stream_append(&s, zeros, 4880, &ae), ERR_OK);
    for (int i = 0; i < 19; i++) {
        CHECK_EQ(stream_append(&s, zeros, 50000, &ae), ERR_OK);
    }
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    layout(got, sizeof got);
    CHECK(strstr(got, "00000000000038:200000 00000000000040:1000000 00000000000050:54880 ")
            != NULL);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

/* The write buffer: written when full, reads across the files and the
 * buffer, sync; a small buffer. */
TEST(append_dir_buffer) {
    struct stream s;
    uint8_t data[1000], b[1000];
    mem_init(&am);
    for (int i = 0; i < 1000; i++) {
        data[i] = (uint8_t) (i * 7 + 1);
    }
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 99, &am, &ae), ERR_ARG);     /* below 100 */
    CHECK_EQ(stream_open_dir_rw(&s, adir, 100, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, data, 250, &ae), ERR_OK);
    CHECK_EQ(s.fileLength, 200);                    /* two buffers written */
    CHECK_EQ(s.buf_len, 50);
    CHECK_EQ(stream_read(&s, 150, b, 100, &ae), ERR_OK);       /* files and buffer */
    CHECK_BYTES(b, data + 150, 100);
    CHECK_EQ(stream_read(&s, 240, b, 11, &ae), ERR_IO);        /* past the end */
    CHECK(strcmp(ae.java, "EOFException") == 0);
    CHECK_EQ(stream_append(&s, data + 250, 750, &ae), ERR_OK);
    CHECK_EQ(stream_read(&s, 0, b, 1000, &ae), ERR_OK);
    CHECK_BYTES(b, data, 1000);
    CHECK_EQ(stream_durable_length(&s), 0);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    CHECK_EQ(stream_durable_length(&s), 1000);
    CHECK_EQ(file_size("00000000000000.bergdb"), 1000);
    stream_close(&s);

    /* A read-only directory takes no append. */
    CHECK_EQ(stream_open_dir(&s, adir, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, data, 1, &ae), ERR_ARG);
    stream_close(&s);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

/* FileStream.testRestartMissingFile: a missing file is refused, and the
 * failed open leaves nothing open (the lock released). And a file that
 * someone else changed fails the stream (DbFile.append's check), which
 * then refuses every write. */
TEST(append_dir_refusals) {
    struct stream s;
    char path[512];
    mem_init(&am);
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 500000, &ae), ERR_OK);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    snprintf(path, sizeof path, "%s/00000000000002.bergdb", adir);
    CHECK_EQ(unlink(path), 0);
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_FORMAT);
    CHECK(strcmp(ae.java, "BadDirStateException") == 0);
    CHECK_MEM_ZERO(&am);
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_FORMAT);
    remove_dir();

    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 100, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 50, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    snprintf(path, sizeof path, "%s/00000000000000.bergdb", adir);
    FILE *f = fopen(path, "ab");
    REQUIRE(f != NULL);
    fputc(1, f);
    fclose(f);
    CHECK_EQ(stream_append(&s, zeros, 50, &ae), ERR_OK);       /* buffered */
    CHECK_EQ(stream_sync(&s, &ae), ERR_IO);
    CHECK(strstr(ae.text, "is not of expected length (50), but 51 bytes") != NULL);
    CHECK_EQ(stream_append(&s, zeros, 1, &ae), ERR_IO);
    CHECK_EQ(stream_sync(&s, &ae), ERR_IO);
    stream_close(&s);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

/* The append path whole: records through rstream into a directory, a
 * restart between them with the block copied, and the bytes read back. */
TEST(append_dir_records) {
    struct stream s;
    struct rs r;
    int64_t p[400];
    mem_init(&am);
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 4096, &am, &ae), ERR_OK);
    rs_init(&r, &s);
    meta_set_startup_distance(&r.meta, 1000000);
    meta_set_max_node_size(&r.meta, 30);
    meta_set_time(&r.meta, 500);
    uint8_t *t = record(1504, 9);
    for (int i = 0; i < 200; i++) {
        REQUIRE(rs_append_record(&r, t, 1504, &p[i], &ae) == ERR_OK);
    }
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    CHECK_EQ(stream_open_dir_rw(&s, adir, 4096, &am, &ae), ERR_OK);
    rs_init(&r, &s);
    CHECK_EQ(rs_use_last_valid_meta_block(&r, &ae), ERR_OK);
    CHECK_EQ(r.posOfLastValidMetaBlock, META_BLOCK_DISTANCE);
    CHECK_EQ(meta_time(&r.meta), 500);
    meta_set_last_trans(&r.meta, p[199]);
    for (int i = 200; i < 400; i++) {
        REQUIRE(rs_append_record(&r, t, 1504, &p[i], &ae) == ERR_OK);
    }
    CHECK_EQ(p[200], rs_get_spos(p[199], 1504));
    /* Before the close: the meta block at 400,000 from the buffer or the
     * files; it names the record before it. */
    uint8_t b[META_BLOCK_SIZE];
    CHECK_EQ(stream_read(&s, 2 * META_BLOCK_DISTANCE, b, META_BLOCK_SIZE, &ae), ERR_OK);
    int64_t named = bytes_get_long_le(b + 16);
    CHECK(named > p[200] && rs_get_spos(named, 1504) <= 2 * META_BLOCK_DISTANCE + 128);
    CHECK_EQ(bytes_get_int_le(b + 40), 1000000);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    CHECK_EQ(file_size("00000000000000.bergdb"), 200000);
    CHECK_EQ(file_size("00000000000004.bergdb"), 200000);
    CHECK_EQ(file_size("00000000000006.bergdb"), rs_get_spos(p[399], 1504) - 600000);
    mem_free(&am, t, 1504, MEM_BUFFER);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

/* Each allocation of an open, appends over new files and a close made to
 * fail in turn (012-01, 4.5): NOMEM, a stream that refuses its writes,
 * and nothing left allocated. */
TEST(append_dir_failure_runs) {
    int64_t n = 1;
    for (;; n++) {
        struct stream s;
        bool failed = false;
        REQUIRE(new_dir());
        mem_init(&am);
        am.fail_at = n;
        enum err_code rc = stream_open_dir_rw(&s, adir, 1000, &am, &ae);
        if (rc != ERR_OK) {
            CHECK_EQ(rc, ERR_NOMEM);
            failed = true;
        } else {
            for (int i = 0; i < 6 && rc == ERR_OK; i++) {
                rc = stream_append(&s, zeros, 100000, &ae);
            }
            enum err_code code = ae.code;
            enum err_code rc2 = stream_finish(&s, &ae);
            if (rc != ERR_OK) {
                /* A write's NOMEM, the first file's too (made by the first
                 * write, 015-06), fails the stream: its close then refuses
                 * the write (ERR_IO) and frees everything. */
                CHECK_EQ(code, ERR_NOMEM);
                failed = true;
            } else if (rc2 != ERR_OK) {
                CHECK_EQ(ae.code, ERR_NOMEM);
                failed = true;
            }
        }
        CHECK_MEM_ZERO(&am);
        remove_dir();
        if (!failed && am.allocs < n) {
            break;
        }
    }
    CHECK(n > 4);
}

/* createDirIfNeeded: missing ancestors are made too; a path that is a
 * file is refused. */
TEST(append_dir_mkdirs) {
    struct stream s;
    char deep[512], file[512];
    mem_init(&am);
    REQUIRE(new_dir());
    snprintf(deep, sizeof deep, "%s/x/y", adir);
    CHECK_EQ(stream_open_dir_rw(&s, deep, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 1, &ae), ERR_OK);    /* the first file (015-06) */
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    snprintf(file, sizeof file, "%s/00000000000000.bergdb", deep);
    CHECK_EQ(stream_open_dir_rw(&s, file, 0, &am, &ae), ERR_IO);
    CHECK_MEM_ZERO(&am);
    unlink(file);
    snprintf(file, sizeof file, "%s/bergdb.lock", deep);
    unlink(file);
    rmdir(deep);
    snprintf(deep, sizeof deep, "%s/x", adir);
    rmdir(deep);
    remove_dir();
}

/* The directory's entries, sorted, as "NAME NAME ...". */
static void entries(char *out, size_t size) {
    struct dirent **list;
    int n = scandir(adir, &list, NULL, alphasort);
    size_t at = 0;
    out[0] = '\0';
    for (int i = 0; i < n; i++) {
        if (list[i]->d_name[0] != '.' && at < size) {
            at += (size_t) snprintf(out + at, size - at, "%s%s", at > 0 ? " " : "",
                    list[i]->d_name);
        }
        free(list[i]);
    }
    free(list);
}

/* bergdb 015-06, FileStream.testNoFileUntilFirstAppend: a new stream has no
 * file until its first write, and reads as an empty one: 0 bytes at 0, and
 * an EOFException past the end, which leaves the stream usable; an empty
 * append makes no file, and a close before the first write leaves only
 * bergdb.lock. Before, the open made an empty first file. */
TEST(append_dir_first_file) {
    struct stream s;
    uint8_t b[1] = { 0 };
    char got[512];
    mem_init(&am);
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_read(&s, 0, b, 0, &ae), ERR_OK);
    CHECK_EQ(stream_read(&s, 0, b, 1, &ae), ERR_IO);
    CHECK(strcmp(ae.java, "EOFException") == 0);
    CHECK(strcmp(ae.text, "Cannot read 1 bytes at spos 0, the stream is empty.") == 0);
    CHECK_EQ(stream_append(&s, b, 0, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    entries(got, sizeof got);
    CHECK(strcmp(got, "bergdb.lock") == 0);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    entries(got, sizeof got);
    CHECK(strcmp(got, "bergdb.lock") == 0);

    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    b[0] = 7;
    CHECK_EQ(stream_append(&s, b, 1, &ae), ERR_OK);
    b[0] = 0;
    CHECK_EQ(stream_read(&s, 0, b, 1, &ae), ERR_OK);
    CHECK_EQ(b[0], 7);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    entries(got, sizeof got);
    CHECK(strcmp(got, "00000000000000.bergdb bergdb.lock") == 0);
    CHECK_EQ(file_size("00000000000000.bergdb"), 1);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

/* bergdb 015-31: a cut at the stream's length keeps the last file, as a
 * file that the cut ends in is (Java's StreamContract, "a cut at the
 * length", 0 and 3), also a full last file, and one after the files that
 * the cut deletes; the stream goes on. Before, the cut took every file and
 * failed the stream (ERR_IO, "Bug"). */
TEST(append_dir_cut_at_length) {
    struct stream s;
    uint8_t b[4] = { 9, 8, 7, 6 };
    char got[512];
    mem_init(&am);
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_pretruncate(&s, 0, &ae), ERR_OK);         /* empty */
    CHECK_EQ(stream_length(&s), 0);
    CHECK_EQ(stream_append(&s, b, 1, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    CHECK_EQ(stream_read(&s, 0, b + 3, 1, &ae), ERR_OK);
    CHECK_EQ(b[3], 9);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    remove_dir();

    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, b, 3, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    CHECK_EQ(stream_pretruncate(&s, 3, &ae), ERR_OK);         /* 3 bytes */
    CHECK_EQ(stream_length(&s), 3);
    CHECK_EQ(stream_first_pos(&s), 0);
    b[3] = 5;
    CHECK_EQ(stream_append(&s, b + 3, 1, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    b[3] = 0;
    CHECK_EQ(stream_read(&s, 3, b + 3, 1, &ae), ERR_OK);
    CHECK_EQ(b[3], 5);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    CHECK_EQ(file_size("00000000000000.bergdb"), 4);
    remove_dir();

    /* A full last file, then one after the cut's files. */
    REQUIRE(new_dir());
    CHECK_EQ(stream_open_dir_rw(&s, adir, 0, &am, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 200000, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    CHECK_EQ(stream_pretruncate(&s, 200000, &ae), ERR_OK);
    CHECK_EQ(stream_first_pos(&s), 0);
    CHECK_EQ(stream_append(&s, b, 1, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    CHECK_EQ(stream_append(&s, zeros, 49999, &ae), ERR_OK);
    CHECK_EQ(stream_sync(&s, &ae), ERR_OK);
    CHECK_EQ(stream_pretruncate(&s, 250000, &ae), ERR_OK);
    CHECK_EQ(stream_first_pos(&s), 200000);
    CHECK_EQ(stream_length(&s), 250000);
    CHECK_EQ(stream_read(&s, 200000, b + 3, 1, &ae), ERR_OK);
    CHECK_EQ(b[3], 9);
    CHECK_EQ(stream_finish(&s, &ae), ERR_OK);
    layout(got, sizeof got);
    CHECK(strcmp(got, "00000000000002:50000 ") == 0);
    remove_dir();
    CHECK_MEM_ZERO(&am);
}

const struct test append_tests[] = {
    TEST_ENTRY(append_rs_test1),
    TEST_ENTRY(append_rs_large),
    TEST_ENTRY(append_rs_named),
    TEST_ENTRY(append_rs_checks),
    TEST_ENTRY(append_rs_last_valid),
    TEST_ENTRY(append_dir_test0),
    TEST_ENTRY(append_dir_sizes),
    TEST_ENTRY(append_dir_size_rules),
    TEST_ENTRY(append_dir_restart_layout),
    TEST_ENTRY(append_dir_buffer),
    TEST_ENTRY(append_dir_refusals),
    TEST_ENTRY(append_dir_records),
    TEST_ENTRY(append_dir_failure_runs),
    TEST_ENTRY(append_dir_mkdirs),
    TEST_ENTRY(append_dir_first_file),
    TEST_ENTRY(append_dir_cut_at_length),
    TEST_END
};
