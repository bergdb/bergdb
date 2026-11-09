/*
 * Unit tests of meta, rstream and nstream's walk (bergdb 012-06): Java's
 * @Nano tests of MetaBlock and RecoverableStream ported where they test
 * reading (positions, the meta blocks, recovery's crash cases as plans),
 * and the refusals of the meta blocks, the walk, an incomplete creation
 * and a cut stream. The streams are made by t_append, RecoverableStream's
 * append without its checks (the writer is 012-09's), in memory streams.
 */
#include "test.h"
#include "bytes.h"
#include "meta.h"
#include "nstream.h"
#include "rstream.h"
#include "spos.h"
#include "stream.h"

#define D META_BLOCK_DISTANCE
#define M META_BLOCK_SIZE

/* One record's bytes: big enough for the tests' records (3 * D + 20). */
static uint8_t tbuf[3 * D + 64];

/* RecoverableStream.append(buffer, 0, size, false, -1): the bytes, and the in-memory meta
 * block written whole when they reach a multiple of 200,000. */
static void t_append(struct stream *s, const struct meta *mb, const uint8_t *buf, int64_t size) {
    struct err e;
    int64_t blockPos = s->length % D;
    int64_t distanceToMeta = blockPos == 0 ? 0 : D - blockPos;
    while (size >= distanceToMeta) {
        stream_append_memory(s, buf, distanceToMeta, &e);
        stream_append_memory(s, mb->block, M, &e);
        size -= distanceToMeta;
        buf += distanceToMeta;
        distanceToMeta = D - M;
    }
    if (size > 0) {
        stream_append_memory(s, buf, size, &e);
    }
}

/* A record of 'size' bytes, its last byte 'last', of which the first 'n' are appended; then
 * the block's lastTrans is set to it (NodeStream.appendNodes). Returns its position. */
static int64_t t_record(struct stream *s, struct meta *mb, int32_t size, uint8_t last,
        int32_t n) {
    int64_t pos = rs_next_spos(s->length);
    memset(tbuf, 0, (size_t) size);
    bytes_put_int_le(size, tbuf);
    tbuf[size - 1] = last;
    t_append(s, mb, tbuf, n);
    meta_set_last_trans(mb, pos);
    return pos;
}

/* ======== MetaBlock ======== */

/* MetaBlock.Tester: time, version, startupDistance, maxNodeSize (005-50). */
TEST(meta_fields) {
    struct meta b;
    meta_init(&b);
    meta_set_time(&b, 1234567);
    CHECK_EQ(meta_time(&b), 1234567);
    CHECK_EQ(meta_version(&b), 154);
    meta_set_startup_distance(&b, 10 * 1000000);
    CHECK_EQ(meta_startup_distance(&b), 10 * 1000000);
    CHECK_EQ(meta_max_node_size(&b), 0);
    CHECK(meta_set_max_node_size(&b, 62));
    CHECK_EQ(meta_max_node_size(&b), 62);
    CHECK_EQ(b.block[44], 62);
    for (int i = 45; i < M - 1; i++) {
        CHECK_EQ(b.block[i], 0);
    }
    CHECK(meta_set_max_node_size(&b, 65535));
    CHECK_EQ(meta_max_node_size(&b), 65535);
    CHECK(!meta_set_max_node_size(&b, 65536));
    CHECK(!meta_set_max_node_size(&b, -1));
    CHECK_EQ(meta_last_trans(&b), -1);
    CHECK(meta_is_valid(&b));
    CHECK_EQ(b.block[M - 1], 10);
    CHECK(memcmp(b.block, "berg", 4) == 0);
    CHECK_EQ(bytes_get_int_le(b.block + 4), 154);
    b.block[6] = 1;                     /* the version is an int (bergdb 019-01) */
    CHECK_EQ(meta_version(&b), 65690);
    b.block[6] = 0;
    b.block[7] = 1;
    CHECK_EQ(meta_version(&b), 16777370);
}

/* checkFormat: only a valid block; the magic bytes, lastTrans, the time. */
TEST(meta_check_format) {
    struct meta b;
    struct err e;
    meta_init(&b);
    CHECK_EQ(meta_check_format(&b, &e), ERR_OK);
    meta_set_last_trans(&b, -2);
    CHECK_EQ(meta_check_format(&b, &e), ERR_FORMAT);
    meta_set_last_trans(&b, 128);
    meta_set_time(&b, -1);
    CHECK_EQ(meta_check_format(&b, &e), ERR_FORMAT);
    meta_set_time(&b, 0);
    b.block[2] = 'x';
    CHECK_EQ(meta_check_format(&b, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    b.block[M - 1] = 0;         /* invalid: not checked */
    CHECK_EQ(meta_check_format(&b, &e), ERR_OK);
}

/* beginsAsBlock and the fill-out template (005-33): the magic bytes and the version, an
 * int since bergdb 019-01 (release 2026.3), so bytes 6 and 7 are compared too. */
TEST(meta_begins_as_block) {
    uint8_t t[M];
    for (int i = 0; i < M; i++) {
        t[i] = meta_fill_out_template(i);
    }
    CHECK(memcmp(t, "berg\x9a\x00\x00\x00", 8) == 0);
    CHECK_EQ(t[M - 1], 0);
    for (int n = 0; n <= M; n++) {
        CHECK(meta_begins_as_block(t, n));
    }
    t[5] = 1;
    CHECK(meta_begins_as_block(t, 5));
    CHECK(!meta_begins_as_block(t, 6));
    for (int at = 6; at <= 7; at++) {
        for (int i = 0; i < M; i++) {
            t[i] = meta_fill_out_template(i);
        }
        t[at] = 1;
        CHECK(meta_begins_as_block(t, at));
        CHECK(!meta_begins_as_block(t, at + 1));
        CHECK(!meta_begins_as_block(t, M));
    }
}

/* ======== RecoverableStream's positions ======== */

/* testGetRemainingTransBytes1, 3, 4; testThatConstantsMatch; testGetTransPos. */
TEST(rs_positions) {
    struct err e;
    int64_t r;
    CHECK(rs_remaining_trans_bytes(100, 300, &r, &e) == ERR_OK && r == 300 - M);
    CHECK(rs_remaining_trans_bytes(0, D + 1000, &r, &e) == ERR_OK && r == D + 1000 - 2 * M);
    CHECK(rs_remaining_trans_bytes(0, D + M, &r, &e) == ERR_OK && r == D - M);
    CHECK_EQ(rs_remaining_trans_bytes(301, 300, &r, &e), ERR_ARG);
    CHECK(M % RS_TRANS_ALIGNMENT == 0);
    CHECK(D % RS_TRANS_ALIGNMENT == 0);
    CHECK_EQ(rs_trans_pos(0), 0);
    CHECK_EQ(rs_trans_pos(1), 0);
    CHECK_EQ(rs_trans_pos(M), 0);
    CHECK_EQ(rs_trans_pos(M + 1), 1);
    CHECK_EQ(rs_trans_pos(D), D - M);
    CHECK_EQ(rs_trans_pos(D - 1), D - M - 1);
    CHECK_EQ(rs_trans_pos(2 * D + M + 1), 2 * (D - M) + 1);
    CHECK_EQ(rs_next_spos(0), M);
    CHECK_EQ(rs_next_spos(D + 5), D + M);
    CHECK_EQ(rs_next_spos(D + M), D + M);
    CHECK_EQ(rs_next_spos(1000), 1000);
}

/* testGetPos1, testGetPos2. */
TEST(rs_get_spos) {
    const int64_t s = M, d = D;
    CHECK_EQ(rs_get_spos(s, d), d + s + s);
    CHECK_EQ(rs_get_spos(s, 0), s);
    CHECK_EQ(rs_get_spos(s + 18, 3), s + 21);
    CHECK_EQ(rs_get_spos(10 * d + s, 38), 10 * d + s + 38);
    CHECK_EQ(rs_get_spos(10 * d + (d - 10), 20), 11 * d + s + 10);
    CHECK_EQ(rs_get_spos(10 * d + (d - s - 10), 5 * (d - s)), 15 * d + (d - s - 10));
    /* A byte that would fall at a multiple of D falls after the block there. */
    CHECK_EQ(rs_get_spos(d - 8, 8), d + s);
    CHECK_EQ(rs_get_spos(d - 8, 7), d - 1);
}

/* testGetStartSpos (005-34): the inverse of getSpos, and its refusals. Java draws from
 * java.util.Random(34); the draws do not matter here. */
TEST(rs_get_start_spos) {
    struct err e;
    int64_t out;
    const int64_t s = M, d = D;
    CHECK(rs_get_start_spos(s + 32, 32, &out, &e) == ERR_OK && out == s);
    CHECK(rs_get_start_spos(d + s + 1000, 2000, &out, &e) == ERR_OK && out == d - 1000);
    CHECK(rs_get_start_spos(d + s, 1000, &out, &e) == ERR_OK && out == d - 1000);
    CHECK(rs_get_start_spos(15 * d + (d - s - 10), 5 * (d - s), &out, &e) == ERR_OK
            && out == 10 * d + (d - s - 10));
    uint64_t state = 34;
    for (int i = 0; i < 100000; i++) {
        int64_t start = (int64_t) test_random_below(&state, 1000) * d + s
                + test_random_below(&state, (int32_t) (d - s));
        int64_t size;
        switch (i % 4) {
        case 0: size = test_random_below(&state, (int32_t) (3 * d)); break;
        case 1: size = test_random_below(&state, 100); break;
        case 2: size = d - start % d - test_random_below(&state, 3);
            size = size < 0 ? 0 : size; break;
        default: size = (int64_t) test_random_below(&state, 20000) * (d - s)
                + test_random_below(&state, 2); break;
        }
        int64_t spos = rs_get_spos(start, size);
        if (rs_get_start_spos(spos, size, &out, &e) != ERR_OK || out != start) {
            CHECK_EQ(out, start);
            break;
        }
    }
    const int64_t bad[4][2] = { { s + 10, 11 }, { d + 5, 0 }, { d, 100 }, { -1, 0 } };
    for (int i = 0; i < 4; i++) {
        CHECK_EQ(rs_get_start_spos(bad[i][0], bad[i][1], &out, &e), ERR_ARG);
        CHECK(strcmp(e.java, "IllegalArgumentException") == 0);
    }
}

/* ======== Reads, meta blocks, recovery ======== */

/* A record across two meta blocks reads back whole; a position in a block reads from its
 * end; reads past the end fail. */
TEST(rs_read_across) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    mem_init(&m);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    int32_t size = 2 * D + 1000;
    memset(tbuf, 0, (size_t) size);
    for (int32_t i = 0; i < size; i++) {
        tbuf[i] = (uint8_t) (i * 7 + 3);
    }
    bytes_put_int_le(size, tbuf);
    tbuf[size - 1] = 10;
    t_append(&s, &mb, tbuf, size);
    CHECK_EQ(s.length, M + size + 2 * M);
    static uint8_t back[2 * D + 1000];
    CHECK_EQ(rs_read(&s, M, back, size, &e), ERR_OK);
    CHECK(memcmp(back, tbuf, (size_t) size) == 0);
    CHECK_EQ(rs_read(&s, 0, back, 10, &e), ERR_OK);        /* from the block's end */
    CHECK(memcmp(back, tbuf, 10) == 0);
    CHECK_EQ(rs_read(&s, D + 5, back, 10, &e), ERR_OK);
    CHECK(memcmp(back, tbuf + (D - M), 10) == 0);
    /* RecoverableStream wraps the stream's IOException: StreamIoException,
     * Java's message, the inner one, as its text, the inner name its cause
     * (bergdb 022-02, D6; before, the text began with the inner name, 012-14,
     * 6.4). The last part of the read, after two meta blocks, passes the end:
     * MemoryStream's EOFException. */
    char want[ERR_TEXT];
    CHECK_EQ(rs_read(&s, M, back, size + 1, &e), ERR_IO);
    CHECK(strcmp(e.java, "StreamIoException") == 0);
    CHECK(strcmp(e.cause, "EOFException") == 0);
    snprintf(want, sizeof want, "Not enough bytes left in the stream, position is %d, length "
            "to read is %d and stream size is %lld.", 2 * D + M, size + 1 - 2 * (D - M),
            (long long) s.length);
    CHECK(strcmp(e.text, want) == 0);
    /* A database's stream (stream_as_storage) is read through Java's
     * BufferedStream, whose EOFException comes first: Java's text of the
     * corrupt-stream set's reads past the end (022-01, step 4). */
    stream_as_storage(&s);
    CHECK_EQ(rs_read(&s, M, back, size + 1, &e), ERR_IO);
    CHECK(strcmp(e.java, "StreamIoException") == 0);
    CHECK(strcmp(e.cause, "EOFException") == 0);
    snprintf(want, sizeof want, "Cannot read %d bytes at position %d, stream size is %lld.",
            size + 1 - 2 * (D - M), 2 * D + M, (long long) s.length);
    CHECK(strcmp(e.text, want) == 0);
    CHECK_EQ(rs_read(&s, M, back, size, &e), ERR_OK);
    CHECK(memcmp(back, tbuf, (size_t) size) == 0);
    s.storage = false;
    /* Below the first position: the code stays NOT_AVAILABLE (isReadBelowCut). */
    /* NodeStream's read of a record whose size passes the end: refused before
     * the buffer, NodeStream.checkReadSize's StreamFormatException (bergdb
     * 005-74, as Java's since release 2026.2; before, the read's error, a
     * StreamIoException of an EOFException, 012-14, 7.4). */
    {
        struct ns_buf nb = {0};
        int32_t got;
        uint8_t hdr[8] = {0};
        struct stream s2;
        stream_open_memory(&s2, &m);
        t_append(&s2, &mb, tbuf, 100);          /* a meta block and 100 bytes */
        bytes_put_int_le(1000000, hdr);
        memcpy(s2.bytes + M, hdr, 4);           /* the record at M claims 1,000,000 bytes */
        CHECK_EQ(ns_read_trans_bytes(&s2, &m, M, &nb, &got, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        CHECK(strncmp(e.text, "Bad item byte size, 1000000, at spos 128: beyond the stream's "
                "record bytes", 74) == 0);
        ns_buf_free(&nb, &m);
        stream_close(&s2);
    }
    REQUIRE(stream_pretruncate(&s, D, &e) == ERR_OK);
    CHECK_EQ(rs_read(&s, M, back, 10, &e), ERR_NOT_AVAILABLE);
    CHECK(strcmp(e.java, "StreamIoException") == 0);
    CHECK(strcmp(e.cause, "ReadBelowFirstPosException") == 0);
    snprintf(want, sizeof want, "Cannot read from position %d, first valid position is %d.",
            M, D);
    CHECK(strcmp(e.text, want) == 0);
    /* An error of another kind is not wrapped and has no cause. */
    int64_t spos;
    CHECK_EQ(rs_get_start_spos(-1, 0, &spos, &e), ERR_ARG);
    CHECK(strcmp(e.cause, "") == 0);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* NodeStreamTester.testReadSizeNearMaxValue (bergdb 021-14, as Java's since release
 * 2026.4): a size at a position near Long.MAX_VALUE is refused; the check's rs_get_spos
 * wrapped, and the check passed, in C as in Java. Not reached from a stream: the reader's
 * read of the size field before it refuses such a position. */
TEST(ns_read_size_near_max_value) {
    struct err e;
    CHECK(!ns_bad_read_size(200, 40, 1000, &e));
    const int64_t positions[] = { 961, 1000, 1001, INT64_MAX - 39, INT64_MAX - 7,
        INT64_MAX - 1 };
    for (size_t i = 0; i < sizeof positions / sizeof positions[0]; i++) {
        err_clear(&e);
        CHECK(ns_bad_read_size(positions[i], 40, 1000, &e));
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        char want[200];
        snprintf(want, sizeof want, "Bad item byte size, 40, at spos %lld: beyond the stream's "
                "record bytes, length 1000.", (long long) positions[i]);
        CHECK(strcmp(e.text, want) == 0);
    }
}

/* readMetaBlock refuses another magic (BadMagicBytes) and another version, valid or not;
 * readLastValidMetaBlock takes the last valid complete block. */
TEST(rs_meta_blocks) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb, out;
    bool found;
    mem_init(&m);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 2 * D, 10, 2 * D);           /* blocks at 0, D and 2D */
    CHECK_EQ(rs_read_meta_block(&s, D, &out, &e), ERR_OK);
    CHECK_EQ(meta_last_trans(&out), -1);
    CHECK(rs_read_last_valid_meta_block(&s, &out, &found, &e) == ERR_OK && found);
    CHECK_EQ(out.pos, 2 * D);
    s.bytes[2 * D + M - 1] = 0;                     /* the last block invalid */
    CHECK(rs_read_last_valid_meta_block(&s, &out, &found, &e) == ERR_OK && found);
    CHECK_EQ(out.pos, D);
    s.bytes[2 * D + 1] = 'X';                       /* its magic: refused, valid or not */
    CHECK_EQ(rs_read_last_valid_meta_block(&s, &out, &found, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "BadMagicBytes") == 0);
    s.bytes[2 * D + 1] = 'e';
    s.bytes[2 * D + 4] = 155;                       /* the version */
    CHECK_EQ(rs_read_last_valid_meta_block(&s, &out, &found, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    s.bytes[2 * D + 4] = 154;
    /* The version is an int (bergdb 019-01, as Java's since release 2026.3): byte 6 or 7
     * set is another version, refused valid or not. Before, they were not read. */
    s.bytes[2 * D + 6] = 1;
    CHECK_EQ(rs_read_last_valid_meta_block(&s, &out, &found, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    CHECK(strcmp(e.text, "Cannot read meta block with version 65690. Version supported: 154")
            == 0);
    s.bytes[2 * D + 6] = 0;
    s.bytes[2 * D + 7] = 1;
    CHECK_EQ(rs_read_meta_block(&s, 2 * D, &out, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    CHECK(strcmp(e.text, "Cannot read meta block with version 16777370. Version supported: "
            "154") == 0);
    s.bytes[2 * D + 7] = 0;
    CHECK(rs_read_last_valid_meta_block(&s, &out, &found, &e) == ERR_OK && found);
    s.bytes[D + M - 1] = 0;
    s.bytes[M - 1] = 0;
    CHECK(rs_read_last_valid_meta_block(&s, &out, &found, &e) == ERR_OK && !found);
    struct rs_recovery plan;
    CHECK_EQ(rs_plan_recovery(&s, &plan, &e), ERR_FORMAT);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* Db.refuseOtherNodeSize (005-50): the last valid block's node size, 0 refused. */
TEST(rs_check_node_size) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    mem_init(&m);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    CHECK_EQ(rs_check_node_size(&s, 30, &e), ERR_IO);      /* empty: a read past the end, as
                                                               Java's (a start creates first) */
    t_record(&s, &mb, 20, 10, 20);                          /* the block at 0 has size 0 */
    CHECK_EQ(rs_check_node_size(&s, 30, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    stream_close(&s);
    meta_init(&mb);
    meta_set_max_node_size(&mb, 14);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 20, 10, 20);
    CHECK_EQ(rs_check_node_size(&s, 14, &e), ERR_OK);
    CHECK_EQ(rs_check_node_size(&s, 30, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* Recovery's plans for Java's crash tests (RecoverableStream.Tester): test1,
 * crashInFirstTransaction, crashInTransactionSize, crashInThirdTransaction,
 * largeTransaction, crashInLargeTransaction, crashInMetaBlockHeader,
 * crashAtMetaBlockPosition; the length after recover() is Java's. */
TEST(rs_recovery_java_cases) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    struct rs_recovery p;
    mem_init(&m);

    /* test1: one whole record of 20. */
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 20, 10, 20);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.torn, SPOS_NULL);
    CHECK_EQ(p.last_whole, M);
    CHECK_EQ(p.length_after, M + 20);
    stream_close(&s);

    /* crashInFirstTransaction: 10 of its 20 bytes. */
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 20, 10, 10);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.torn, M);
    CHECK_EQ(p.torn_have, 10);
    CHECK_EQ(p.torn_size, 20);
    CHECK_EQ(p.zero_fill, 10);
    CHECK_EQ(p.header_fix_len, 0);
    CHECK_EQ(p.last_whole, SPOS_NULL);
    CHECK_EQ(p.length_after, M + 20);
    stream_close(&s);

    /* crashInTransactionSize: 2 bytes of its size; completed with 0, 0 and byte 4. */
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 20, 10, 2);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.header_fix_len, 3);
    CHECK(p.header_fix[0] == 0 && p.header_fix[1] == 0 && p.header_fix[2] == 4);
    CHECK_EQ(p.torn_have, 2);
    CHECK_EQ(p.torn_size, 20);
    CHECK_EQ(p.zero_fill, 15);
    CHECK_EQ(p.length_after, M + 20);
    stream_close(&s);

    /* crashInThirdTransaction. */
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 20, 10, 20);
    int64_t second = t_record(&s, &mb, 20, 10, 20);
    int64_t third = t_record(&s, &mb, 20, 10, 10);
    CHECK_EQ(s.length, M + 50);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.torn, third);
    CHECK_EQ(p.last_whole, second);
    CHECK_EQ(p.zero_fill, 10);
    CHECK_EQ(p.length_after, M + 60);
    stream_close(&s);

    /* largeTransaction, and crashInLargeTransaction (its last 10 bytes missing). */
    int32_t large = 3 * D + 20;
    int64_t expected = 3 * D + 20 + 4 * M;
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, large, 10, large);
    CHECK_EQ(s.length, expected);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.torn, SPOS_NULL);
    CHECK_EQ(p.length_after, expected);
    stream_close(&s);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, large, 10, large - 10);
    CHECK_EQ(s.length, expected - 10);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.torn, M);
    CHECK_EQ(p.zero_fill, 10);
    CHECK_EQ(p.length_after, expected);
    CHECK_EQ(p.last_valid.pos, 3 * D);      /* written in the record, naming none before */
    CHECK_EQ(meta_last_trans(&p.last_valid), -1);
    stream_close(&s);

    /* crashInMetaBlockHeader: a record of 200,001, the stream cut 3 bytes into the block
     * at 200,000: the block completed (invalid), the record filled. */
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 200001, 10, 200001);
    stream_truncate_memory(&s, 200003, &e);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.meta_fill, M - 3);
    CHECK_EQ(p.last_valid.pos, 0);
    CHECK_EQ(p.torn, M);
    CHECK_EQ(p.zero_fill, 200001 - (D - M));
    CHECK_EQ(p.length_after, M + 200001 + M);
    stream_close(&s);

    /* crashAtMetaBlockPosition (005-27): a record that ends at 200,000, cut there before
     * its block. */
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, D - M, 10, D - M);
    CHECK_EQ(s.length, D + M);
    stream_truncate_memory(&s, D, &e);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.meta_fill, M);
    CHECK_EQ(p.last_valid.pos, 0);
    CHECK_EQ(p.torn, SPOS_NULL);
    CHECK_EQ(p.last_whole, M);
    CHECK_EQ(p.length_after, D + M);
    stream_close(&s);

    CHECK_MEM_ZERO(&m);
}

/* transHeaderFixBytes: a size read so far below 17 gets 1 as its first missing byte; four
 * size bytes get only byte 4; a size below 5 is refused; one of exactly 5 is whole. */
TEST(rs_recovery_header_fix) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    struct rs_recovery p;
    uint8_t b[4];
    mem_init(&m);

    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_append(&s, &mb, (const uint8_t *) "\x05", 1);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.header_fix_len, 4);
    CHECK(p.header_fix[0] == 1 && p.header_fix[1] == 0 && p.header_fix[2] == 0
            && p.header_fix[3] == 4);
    CHECK_EQ(p.torn_size, 5 + 256);
    CHECK_EQ(p.zero_fill, 256);
    CHECK_EQ(p.length_after, M + 5 + 256);
    stream_close(&s);

    meta_init(&mb);
    stream_open_memory(&s, &m);
    bytes_put_int_le(3, b);
    t_append(&s, &mb, b, 4);
    CHECK_EQ(rs_plan_recovery(&s, &p, &e), ERR_FORMAT);     /* Bad transaction size */
    stream_close(&s);

    meta_init(&mb);
    stream_open_memory(&s, &m);
    bytes_put_int_le(5, b);
    t_append(&s, &mb, b, 4);
    REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
    CHECK_EQ(p.header_fix_len, 1);
    CHECK_EQ(p.torn_size, 5);
    CHECK_EQ(p.zero_fill, 0);
    CHECK_EQ(p.length_after, M + 5);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* isIncompleteCreation (005-33), as 012-02, 4.5 lists its cases. */
TEST(rs_incomplete_creation) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    bool yes;
    mem_init(&m);
    for (int n = 0; n <= 136 + M; n++) {
        meta_init(&mb);
        stream_open_memory(&s, &m);
        t_record(&s, &mb, 136, 10, 136);           /* the creation: 264 bytes */
        stream_truncate_memory(&s, n, &e);
        REQUIRE(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK);
        CHECK_EQ(yes, n > 0 && n < 264);
        stream_close(&s);
    }
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 136, 0, 136);                /* whole, failed: yes */
    CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && yes);
    s.bytes[0] = 'x';                              /* another magic: no */
    CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && !yes);
    stream_close(&s);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 136, 10, 136);
    t_record(&s, &mb, 48, 10, 10);                 /* longer than a creation: no */
    CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && !yes);
    stream_close(&s);
    /* A creation cut at 10 bytes whose byte 6 or 7 of the version is set: not one (bergdb
     * 019-01; RecoverableStream.Tester.testIsIncompleteCreation's case). */
    for (int at = 6; at <= 7; at++) {
        meta_init(&mb);
        stream_open_memory(&s, &m);
        t_record(&s, &mb, 136, 10, 136);
        stream_truncate_memory(&s, 10, &e);
        CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && yes);
        s.bytes[at] = 1;
        CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && !yes);
        stream_close(&s);
    }
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.checkLastTransSpos (bergdb 019-34, as Java's since release 2026.3;
 * DbTesterRestart.testMetaBlockLastTransPosRefused at the plan): the last valid meta block
 * names, as its last transaction, Spos.NULL or a position from the first transaction byte
 * up to the block; else the plan is refused, before anything is written, with a
 * StreamFormatException that names the block and the position. Before, a position past
 * the stream's end gave recovery's IllegalArgumentException ("spos >= streamSize"), and a
 * position in the first meta block or after its block was walked from. */
TEST(rs_last_trans_spos_refused) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    struct rs_recovery p;
    mem_init(&m);

    /* The first meta block's byte 23, the last byte of its last transaction's position
     * (Spos.NULL as the creation wrote it), xor 0x80 and 0xff: past the stream's end. */
    const int64_t past[2] = { INT64_C(0x7fffffffffffffff), INT64_C(0x00ffffffffffffff) };
    for (int i = 0; i < 2; i++) {
        meta_init(&mb);
        stream_open_memory(&s, &m);
        t_record(&s, &mb, 20, 10, 20);
        t_record(&s, &mb, 20, 10, 20);
        CHECK_EQ(bytes_get_long_le(s.bytes + 16), -1);
        s.bytes[23] ^= (uint8_t) (i == 0 ? 0x80 : 0xff);
        const int64_t length = s.length;
        CHECK_EQ(rs_plan_recovery(&s, &p, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        char want[200];
        snprintf(want, sizeof want, "The meta block at 0 names the last transaction at %lld, "
                "which cannot be one in a stream from 0: not before the block.",
                (long long) past[i]);
        CHECK(strcmp(e.text, want) == 0);
        CHECK_EQ(s.length, length);
        stream_close(&s);
    }

    /* The second meta block, which a large record puts in the stream, naming a position in
     * the first meta block (10) or one after itself (D + M): refused; naming the record
     * before it, or Spos.NULL: taken. */
    const int64_t bad[2] = { 10, D + M };
    for (int i = 0; i < 4; i++) {
        meta_init(&mb);
        stream_open_memory(&s, &m);
        int64_t first = t_record(&s, &mb, 20, 10, 20);
        t_record(&s, &mb, D, 10, D);                   /* across the block at D */
        int64_t named = i < 2 ? bad[i] : i == 2 ? first : SPOS_NULL;
        bytes_put_long_le(named, s.bytes + D + 16);
        if (i < 2) {
            CHECK_EQ(rs_plan_recovery(&s, &p, &e), ERR_FORMAT);
            CHECK(strcmp(e.java, "StreamFormatException") == 0);
            char want[200];
            snprintf(want, sizeof want, "The meta block at %d names the last transaction at "
                    "%lld, which cannot be one in a stream from 0: not before the block.",
                    (int) D, (long long) named);
            CHECK(strcmp(e.text, want) == 0);
        } else {
            CHECK_EQ(rs_plan_recovery(&s, &p, &e), ERR_OK);
            CHECK_EQ(p.last_valid.pos, D);
            CHECK_EQ(p.torn, SPOS_NULL);
        }
        stream_close(&s);
    }
    CHECK_MEM_ZERO(&m);
}

/* getPosOfTransCompletedBefore (005-39): the record that the last valid block at or
 * before a position names; in a cut stream, the first valid block that names one at or
 * after the first position; else refused. */
TEST(rs_pos_of_trans_completed_before) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    int64_t p;
    mem_init(&m);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    int64_t pos[40];
    for (int i = 0; i < 40; i++) {
        pos[i] = t_record(&s, &mb, 50000, 10, 50000);
    }
    /* Blocks at 0 (none: 128), at D (the record before it ends), ... */
    CHECK(rs_pos_of_trans_completed_before(&s, 100, &p, &e) == ERR_OK && p == M);
    CHECK(rs_pos_of_trans_completed_before(&s, D - 1, &p, &e) == ERR_OK && p == M);
    CHECK(rs_pos_of_trans_completed_before(&s, D, &p, &e) == ERR_OK && p == pos[2]);
    CHECK(rs_pos_of_trans_completed_before(&s, 5 * D + 7, &p, &e) == ERR_OK);
    CHECK(p < 5 * D && rs_get_spos(p, 50000) >= 5 * D - 50000);
    /* Cut at 1,000,000: the block there names a record before it; the next one names one
     * after it. */
    CHECK_EQ(stream_pretruncate_memory(&s, 1500000, &e), ERR_OK);
    CHECK_EQ(s.first, 1000000);
    CHECK(rs_pos_of_trans_completed_before(&s, s.first, &p, &e) == ERR_OK);
    CHECK(p >= 1000000);
    struct ns_iter it;
    bool has;
    ns_iter_init(&it, &s, &m, s.first, false);
    CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && has && it.tpos == p);
    ns_iter_free(&it);
    /* Every block after the cut invalid: refused. */
    for (int64_t b = 1000000; b + M <= s.length; b += D) {
        s.bytes[b + M - 1] = 0;
    }
    CHECK_EQ(rs_pos_of_trans_completed_before(&s, s.first, &p, &e), ERR_FORMAT);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* The walk (NodeStream.TransIterator): failed records skipped; an exact start at one, a
 * size below 17 and a last byte neither 0 nor 10 refused; a cut record fails as a read. */
TEST(ns_walk) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    struct ns_iter it;
    bool has;
    mem_init(&m);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    int64_t a = t_record(&s, &mb, 48, 10, 48);
    int64_t b = t_record(&s, &mb, 64, 0, 64);
    int64_t c = t_record(&s, &mb, 24, 10, 24);
    ns_iter_init(&it, &s, &m, 0, false);
    CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && has && it.tpos == a);
    CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && has && it.tpos == c);
    CHECK_EQ(it.trans_count, 2);
    CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && !has);
    ns_iter_free(&it);
    ns_iter_init(&it, &s, &m, b, true);
    CHECK_EQ(ns_iter_next(&it, &has, &e), ERR_FORMAT);       /* 005-28 */
    ns_iter_free(&it);
    s.bytes[c + 23] = 7;                                      /* Bad lastByte */
    ns_iter_init(&it, &s, &m, a, true);
    CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && has);
    CHECK_EQ(ns_iter_next(&it, &has, &e), ERR_FORMAT);
    ns_iter_free(&it);
    s.bytes[c] = 16;                                          /* below 17 */
    ns_iter_init(&it, &s, &m, c, true);
    CHECK_EQ(ns_iter_next(&it, &has, &e), ERR_FORMAT);
    ns_iter_free(&it);
    s.bytes[c] = 24;
    s.bytes[c + 1] = 0x10;                                    /* past the end (005-74) */
    ns_iter_init(&it, &s, &m, c, true);
    CHECK_EQ(ns_iter_next(&it, &has, &e), ERR_FORMAT);
    CHECK_EQ(it.buf.cap, 0);                                  /* nothing allocated for it */
    ns_iter_free(&it);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester.testIsIncompleteCreation's other cases (bergdb 005-33), which
 * rs_incomplete_creation does not make: zero bytes (1, 100, 128 and a creation's 264) are
 * not a creation; a block of version 155 cut at 10 bytes is not, its magic bytes alone
 * (cut at 4) are; a complete first block that is invalid, or that names a record, is not;
 * a creation with a record after it, committed or failed, is not; a first record of 1,000
 * bytes cut at 300 is not (longer than a creation), cut at 200 is; a short first record,
 * committed or failed, with more bytes after it is not. The call only reads. */
TEST(rs_incomplete_creation_java) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    bool yes;
    static uint8_t zeros[264];
    mem_init(&m);
    const int32_t n_zeros[4] = { 1, 100, M, 264 };
    for (int i = 0; i < 4; i++) {
        stream_open_memory(&s, &m);
        REQUIRE(stream_append_memory(&s, zeros, n_zeros[i], &e) == ERR_OK);
        CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && !yes);
        stream_close(&s);
    }
    for (int c = 0; c < 6; c++) {
        meta_init(&mb);
        stream_open_memory(&s, &m);
        t_record(&s, &mb, 136, 10, 136);           /* the creation: 264 bytes */
        bool expected = false;
        if (c == 0) {
            s.bytes[4] = 155;
            REQUIRE(stream_truncate_memory(&s, 10, &e) == ERR_OK);
        } else if (c == 1) {
            s.bytes[4] = 155;
            REQUIRE(stream_truncate_memory(&s, 4, &e) == ERR_OK);
            expected = true;                        /* the magic bytes only */
        } else if (c == 2) {
            s.bytes[M - 1] = 0;                     /* an invalid block */
            REQUIRE(stream_truncate_memory(&s, 200, &e) == ERR_OK);
        } else if (c == 3) {
            bytes_put_long_le(M, s.bytes + 16);     /* a block that names a record */
            REQUIRE(stream_truncate_memory(&s, 200, &e) == ERR_OK);
        } else {
            if (c == 5) {
                s.bytes[264 - 1] = 0;               /* the creation's record failed */
            }
            t_record(&s, &mb, 24, 10, 24);          /* a record after it */
        }
        const int64_t length = s.length;
        CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK);
        CHECK_EQ(yes, expected);
        CHECK_EQ(s.length, length);
        stream_close(&s);
    }
    meta_init(&mb);
    stream_open_memory(&s, &m);
    t_record(&s, &mb, 1000, 10, 300 - M);           /* a large first record, cut at 300 */
    CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && !yes);
    REQUIRE(stream_truncate_memory(&s, 200, &e) == ERR_OK);
    CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && yes);
    stream_close(&s);
    for (int last = 0; last < 2; last++) {
        meta_init(&mb);
        stream_open_memory(&s, &m);
        t_record(&s, &mb, 24, last == 0 ? 10 : 0, 24);
        t_record(&s, &mb, 100, 10, 50);             /* 50 bytes of a record after it */
        CHECK(rs_is_incomplete_creation(&s, 264, &yes, &e) == ERR_OK && !yes);
        stream_close(&s);
    }
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester's testTransHeaderFixBytes1 to 4 and
 * testTransHeaderFixBytesBelowMin, through recovery's plan: the bytes of a cut record's size
 * that exist, and the size that transHeaderFixBytes completes: 0 gives 256; 40, 40; 10,
 * below the least size, 266 (10 until 2026-10-13); 2 and 1, 258; 3 and 0, 3 + 65,536. */
TEST(rs_trans_header_fix_bytes) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    struct rs_recovery p;
    mem_init(&m);
    const uint8_t existing[5][2] = { { 0 }, { 40 }, { 10 }, { 2, 1 }, { 3, 0 } };
    const int32_t have[5] = { 1, 1, 1, 2, 2 };
    const int32_t size[5] = { 256, 40, 256 + 10, 256 + 2, 3 + 256 * 256 };
    for (int i = 0; i < 5; i++) {
        meta_init(&mb);
        stream_open_memory(&s, &m);
        t_append(&s, &mb, existing[i], have[i]);
        REQUIRE(rs_plan_recovery(&s, &p, &e) == ERR_OK);
        CHECK_EQ(p.torn, M);
        CHECK_EQ(p.torn_have, have[i]);
        CHECK_EQ(p.header_fix_len, 5 - have[i]);
        uint8_t total[5];
        memcpy(total, existing[i], (size_t) have[i]);
        memcpy(total + have[i], p.header_fix, (size_t) p.header_fix_len);
        CHECK_EQ(bytes_get_int_le(total), size[i]);
        CHECK_EQ(total[4], RS_TORN_HEADER_FILLER);
        CHECK_EQ(p.torn_size, size[i]);
        CHECK_EQ(p.length_after, rs_get_spos(M, size[i]));
        stream_close(&s);
    }
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester.testPosOfTransCompletedBefore (bergdb 005-39): with 1,300 named
 * records of 1,000 bytes, at every 997th position the record that the last valid block at
 * or before it names, which is the last that ends before that block (the first, 128, at the
 * block at 0, which names none), not in general the last completed before the position:
 * at 399,000, 198,128. */
TEST(rs_pos_of_trans_completed_before_java) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    int64_t p;
    static int64_t starts[1300];
    mem_init(&m);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    for (int i = 0; i < 1300; i++) {
        starts[i] = t_record(&s, &mb, 1000, 10, 1000);
    }
    int wrong = 0;
    for (int64_t spos = 0; spos < s.length; spos += 997) {
        const int64_t blockPos = spos / D * D;
        int64_t expected = M;
        for (int i = 0; i < 1300; i++) {
            if (rs_get_spos(starts[i], 1000) < blockPos) {
                expected = starts[i];
            }
        }
        if (rs_pos_of_trans_completed_before(&s, spos, &p, &e) != ERR_OK || p != expected) {
            if (wrong++ < 3) {
                printf("    spos %lld: %lld, expected %lld\n", (long long) spos, (long long) p,
                        (long long) expected);
            }
        }
    }
    CHECK_EQ(wrong, 0);
    CHECK(rs_pos_of_trans_completed_before(&s, 399000, &p, &e) == ERR_OK && p == 198128);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester.testPosOfTransCompletedBeforeAfterCut (bergdb 005-39): in a
 * stream whose front is cut (at 1,000,000, a MemoryStream's array), the meta blocks up to
 * the first one after the cut name a record before it: every position before the block at
 * 1,200,000 gives the record that block names, at or after the cut (a position before the
 * first position too), and a walk from 0 begins there. With 1,100 records the last block
 * names one before the cut: refused, StreamFormatException. */
TEST(rs_pos_of_trans_completed_before_after_cut) {
    struct mem m;
    struct err e;
    struct stream s;
    struct meta mb;
    int64_t p;
    static int64_t starts[1300];
    mem_init(&m);
    meta_init(&mb);
    stream_open_memory(&s, &m);
    for (int i = 0; i < 1300; i++) {
        starts[i] = t_record(&s, &mb, 1000, 10, 1000);
    }
    REQUIRE(stream_pretruncate_memory(&s, 5 * D, &e) == ERR_OK);
    CHECK_EQ(stream_first_pos(&s), 5 * D);
    int64_t first;
    REQUIRE(rs_pos_of_trans_completed_before(&s, 6 * D, &first, &e) == ERR_OK);
    CHECK(first >= 5 * D && rs_get_spos(first, 1000) < 6 * D);
    const int64_t before[5] = { 0, 500, 5 * D, 5 * D + 50000, 6 * D - 1 };
    for (int i = 0; i < 5; i++) {
        CHECK(rs_pos_of_trans_completed_before(&s, before[i], &p, &e) == ERR_OK);
        CHECK_EQ(p, first);
    }
    struct ns_iter it;
    bool has = true;
    int count = 0;
    ns_iter_init(&it, &s, &m, 0, false);
    while (ns_iter_next(&it, &has, &e) == ERR_OK && has) {
        CHECK(count > 0 || it.tpos == first);
        count++;
    }
    CHECK(!has);
    ns_iter_free(&it);
    int expected = 0;
    for (int i = 0; i < 1300; i++) {
        expected += starts[i] >= first ? 1 : 0;
    }
    CHECK_EQ(count, expected);
    stream_close(&s);

    meta_init(&mb);
    stream_open_memory(&s, &m);
    for (int i = 0; i < 1100; i++) {
        t_record(&s, &mb, 1000, 10, 1000);
    }
    REQUIRE(stream_pretruncate_memory(&s, 5 * D, &e) == ERR_OK);
    const int64_t refused[2] = { 0, 5 * D + 50000 };
    for (int i = 0; i < 2; i++) {
        CHECK_EQ(rs_pos_of_trans_completed_before(&s, refused[i], &p, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
    }
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* NodeStreamTester.testCorruptReadNodeSize, testCorruptReadTransSize and
 * testCorruptIteratorSize (bergdb 005-74, F3, as Java's since release 2026.2): a size field
 * of Integer.MAX_VALUE, 2^30, -1, 0, 6 or 7 at 128, in a stream of 132 bytes, is refused by
 * readNode, readTransBytes and the exact iterator with a StreamFormatException that names
 * the size, before its buffer is allocated: no allocation at all. */
TEST(ns_corrupt_read_sizes) {
    struct mem m;
    struct err e;
    const int32_t sizes[] = { INT32_MAX, 1 << 30, -1, 0, 6, 7 };
    mem_init(&m);
    for (int reader = 0; reader < 3; reader++) {
        for (size_t i = 0; i < sizeof sizes / sizeof sizes[0]; i++) {
            struct stream s;
            uint8_t bytes[132];
            memset(bytes, 0, sizeof bytes);
            bytes_put_int_le(sizes[i], bytes + 128);
            stream_open_memory(&s, &m);
            REQUIRE(stream_append_memory(&s, bytes, (int64_t) sizeof bytes, &e) == ERR_OK);
            const int64_t allocs = m.allocs;
            struct ns_buf nb = { NULL, 0 };
            enum err_code rc;
            err_clear(&e);
            if (reader == 0) {
                struct sn_node n;
                rc = ns_read_node(&s, &m, 128, &nb, &n, &e);
            } else if (reader == 1) {
                int32_t got;
                rc = ns_read_trans_bytes(&s, &m, 128, &nb, &got, &e);
            } else {
                struct ns_iter it;
                bool has;
                ns_iter_init(&it, &s, &m, 128, true);
                rc = ns_iter_next(&it, &has, &e);
                CHECK_EQ(it.buf.cap, 0);
                ns_iter_free(&it);
            }
            CHECK_EQ(rc, ERR_FORMAT);
            CHECK(strcmp(e.java, "StreamFormatException") == 0);
            CHECK(strstr(e.text, "size") != NULL);
            CHECK_EQ(nb.cap, 0);
            CHECK_EQ(m.allocs, allocs);             /* nothing allocated for it */
            if (rc != ERR_FORMAT || strstr(e.text, "size") == NULL) {
                printf("    reader %d, size %d: %s: %s\n", reader, (int) sizes[i], e.java, e.text);
            }
            ns_buf_free(&nb, &m);
            stream_close(&s);
        }
    }
    CHECK_MEM_ZERO(&m);
}

/* NodeStreamTester.testReadSizeExcludesMetaBlocks: meta blocks are not bytes available to
 * a node or a record. A record at D - 8 whose size, 136, fits the stream's bytes after it
 * (D + 144 in all), but only 24 record bytes exist there: refused. */
TEST(ns_read_size_excludes_meta_blocks) {
    struct mem m;
    struct err e;
    struct stream s;
    static uint8_t bytes[D + 144];
    mem_init(&m);
    memset(bytes, 0, sizeof bytes);
    const int64_t pos = D - 8;
    bytes_put_int_le(136, bytes + pos);
    stream_open_memory(&s, &m);
    REQUIRE(stream_append_memory(&s, bytes, (int64_t) sizeof bytes, &e) == ERR_OK);
    struct ns_buf nb = { NULL, 0 };
    int32_t got;
    CHECK_EQ(ns_read_trans_bytes(&s, &m, pos, &nb, &got, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strstr(e.text, "size") != NULL);
    CHECK_EQ(nb.cap, 0);
    struct sn_node n;
    CHECK_EQ(ns_read_node(&s, &m, pos, &nb, &n, &e), ERR_FORMAT);  /* as a node, too */
    CHECK(strstr(e.text, "size") != NULL);
    ns_buf_free(&nb, &m);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* NodeStreamTester.testReadSizeAtMetaBlock: a record whose last byte is just before a
 * meta block, in a stream that ends there (the block not written yet) or holds the block,
 * and a record across one, are read whole. */
TEST(ns_read_size_at_meta_block) {
    struct mem m;
    struct err e;
    static uint8_t bytes[200144];
    const int64_t lengths[] = { 200000, 200128, 200144 };
    const int64_t pos = D - 32;
    mem_init(&m);
    for (int k = 0; k < 3; k++) {
        const int32_t size = lengths[k] == 200144 ? 48 : 32;
        uint8_t expected[48];
        memset(expected, 0, sizeof expected);
        bytes_put_int_le(size, expected);
        for (int32_t i = 4; i < size; i++) {
            expected[i] = (uint8_t) i;
        }
        memset(bytes, 0, sizeof bytes);
        for (int32_t i = 0; i < size; i++) {
            bytes[rs_get_spos(pos, i)] = expected[i];
        }
        struct stream s;
        stream_open_memory(&s, &m);
        REQUIRE(stream_append_memory(&s, bytes, lengths[k], &e) == ERR_OK);
        struct ns_buf nb = { NULL, 0 };
        int32_t got = -1;
        CHECK_EQ(ns_read_trans_bytes(&s, &m, pos, &nb, &got, &e), ERR_OK);
        CHECK_EQ(got, size);
        CHECK(got == size && memcmp(nb.p, expected, (size_t) size) == 0);
        ns_buf_free(&nb, &m);
        stream_close(&s);
    }
    CHECK_MEM_ZERO(&m);
}

const struct test rstream_tests[] = {
    TEST_ENTRY(meta_fields),
    TEST_ENTRY(meta_check_format),
    TEST_ENTRY(meta_begins_as_block),
    TEST_ENTRY(rs_positions),
    TEST_ENTRY(rs_get_spos),
    TEST_ENTRY(rs_get_start_spos),
    TEST_ENTRY(rs_read_across),
    TEST_ENTRY(rs_meta_blocks),
    TEST_ENTRY(rs_check_node_size),
    TEST_ENTRY(rs_recovery_java_cases),
    TEST_ENTRY(rs_recovery_header_fix),
    TEST_ENTRY(rs_incomplete_creation),
    TEST_ENTRY(rs_last_trans_spos_refused),
    TEST_ENTRY(rs_pos_of_trans_completed_before),
    TEST_ENTRY(ns_walk),
    TEST_ENTRY(ns_read_size_near_max_value),
    TEST_ENTRY(rs_incomplete_creation_java),
    TEST_ENTRY(rs_trans_header_fix_bytes),
    TEST_ENTRY(rs_pos_of_trans_completed_before_java),
    TEST_ENTRY(rs_pos_of_trans_completed_before_after_cut),
    TEST_ENTRY(ns_corrupt_read_sizes),
    TEST_ENTRY(ns_read_size_excludes_meta_blocks),
    TEST_ENTRY(ns_read_size_at_meta_block),
    TEST_END
};
