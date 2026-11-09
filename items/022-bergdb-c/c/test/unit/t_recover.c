/* The tests of recover (bergdb 012-10, part 1): Java's RecoverableStream
 * tests of recover() (crashInFirstTransaction, crashInTransactionSize,
 * crashInThirdTransaction, largeTransaction, crashInLargeTransaction,
 * crashInMetaBlockHeader, crashAtMetaBlockPosition), on a memory stream and
 * records of raw bytes, as Java's; and the meta blocks that a fill writes:
 * valid, with the lastTrans of the last valid block before the cut (012-02,
 * 4.4). The 005-40 test of a wrong crypto key is left out (no encryption in
 * C). */
#include <stdlib.h>
#include <string.h>
#include "bytes.h"
#include "mem.h"
#include "meta.h"
#include "nstream.h"
#include "recover.h"
#include "rstream.h"
#include "spos.h"
#include "stream.h"
#include "test.h"

#define D META_BLOCK_DISTANCE
#define M META_BLOCK_SIZE

/* A record of size bytes: its size field and its last byte 10, zeros between. */
static uint8_t *record(int32_t size) {
    uint8_t *b = calloc((size_t) size, 1);
    bytes_put_int_le(size, b);
    b[size - 1] = RS_LAST_BYTE;
    return b;
}

static uint8_t byte_at(struct stream *s, int64_t pos) {
    uint8_t b = 0xee;
    struct err e;
    CHECK_EQ(stream_read(s, pos, &b, 1, &e), ERR_OK);
    return b;
}

static void recover_all(struct stream *s, struct rs_recovery *plan) {
    struct rs r2;
    struct err e;
    rs_init(&r2, s);
    CHECK_EQ(rcv_recover(&r2, plan, &e), ERR_OK);
}

TEST(recover_crash_in_first_transaction) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    uint8_t *t = record(20);
    CHECK_EQ(rs_append(&r1, t, 10, false, &e), ERR_OK);    /* only its first 10 bytes */
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(stream_length(&s), M + 20);
    CHECK_EQ(byte_at(&s, M + 20 - 1), 0);
    CHECK_EQ(plan.torn, M);
    CHECK_EQ(plan.zero_fill, 10);
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

TEST(recover_crash_in_transaction_size) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    uint8_t *t = record(20);
    CHECK_EQ(rs_append(&r1, t, 2, false, &e), ERR_OK);     /* the size field incomplete */
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(stream_length(&s), M + 20);
    CHECK_EQ(byte_at(&s, M + 20 - 1), 0);
    CHECK_EQ(plan.header_fix_len, 3);
    CHECK_EQ(byte_at(&s, M + 4), RS_TORN_HEADER_FILLER);
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

TEST(recover_crash_in_third_transaction) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    uint8_t *t = record(20);
    CHECK_EQ(rs_append(&r1, t, 20, true, &e), ERR_OK);
    CHECK_EQ(rs_append(&r1, t, 20, true, &e), ERR_OK);
    CHECK_EQ(rs_append(&r1, t, 10, false, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), M + 20 + 20 + 10);
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(stream_length(&s), M + 60);
    CHECK_EQ(byte_at(&s, M + 60 - 1), 0);
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

TEST(recover_large_transaction) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    int32_t size = 3 * D + 20;
    uint8_t *t = record(size);
    CHECK_EQ(rs_append(&r1, t, size, true, &e), ERR_OK);
    int64_t expected = 3 * (int64_t) D + 20 + 4 * M;
    CHECK_EQ(stream_length(&s), expected);
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(stream_length(&s), expected);
    CHECK_EQ(plan.torn, SPOS_NULL);
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

TEST(recover_crash_in_large_transaction) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    int32_t size = 3 * D + 20;
    uint8_t *t = record(size);
    CHECK_EQ(rs_append(&r1, t, size - 10, false, &e), ERR_OK);     /* its last 10 bytes missing */
    int64_t expected = 3 * (int64_t) D + 20 + 4 * M - 10;
    CHECK_EQ(stream_length(&s), expected);
    /* the last valid block is at 3 D (lastTrans -1: the walk from 128) */
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(stream_length(&s), expected + 10);
    CHECK_EQ(byte_at(&s, expected + 10 - 1), 0);
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* A cut before a meta block of a large record: the fill writes the blocks
 * it reaches, valid, with the lastTrans of the last valid block before the
 * cut (the scan of recovered-199993 in 012-02, 4.4). */
TEST(recover_fill_writes_meta_blocks) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    uint8_t *t = record(48);
    CHECK_EQ(rs_append_record(&r1, t, 48, &(int64_t) { 0 }, &e), ERR_OK);   /* at 128 */
    int32_t size = 2 * D + 1000;
    uint8_t *big = record(size);
    CHECK_EQ(rs_append(&r1, big, D - 128 - 48 - 7, false, &e), ERR_OK);   /* cut before D */
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(plan.torn, M + 48);
    CHECK_EQ(stream_length(&s), rs_get_spos(M + 48, size));
    /* the blocks at D and 2 D: valid, lastTrans 128 (the block at 0 named none, -1;
     * the record at 128 is the last one before the cut, but the in-memory block is a
     * copy of the last valid block, which was written before it: -1) */
    for (int k = 1; k <= 2; k++) {
        uint8_t b[M];
        CHECK_EQ(stream_read(&s, (int64_t) k * D, b, M, &e), ERR_OK);
        struct meta mb;
        meta_from_bytes(&mb, b, (int64_t) k * D);
        CHECK(meta_is_valid(&mb));
        CHECK_EQ(meta_last_trans(&mb), -1);
    }
    CHECK_EQ(byte_at(&s, stream_length(&s) - 1), 0);
    free(t);
    free(big);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

TEST(recover_crash_in_meta_block_header) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    uint8_t *t = record(200001);
    CHECK_EQ(rs_append(&r1, t, 200001, true, &e), ERR_OK);
    s.length = 200003;          /* MemoryStream.truncate */
    struct rs_recovery plan;
    recover_all(&s, &plan);
    /* the block at D completed from the fill-out template, invalid; the record
     * filled to its end */
    CHECK_EQ(plan.meta_fill, M - 3);
    uint8_t b[M];
    CHECK_EQ(stream_read(&s, D, b, M, &e), ERR_OK);
    CHECK_EQ(b[M - 1], 0);
    CHECK_EQ(stream_length(&s), rs_get_spos(M, 200001));
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

TEST(recover_crash_at_meta_block_position) {
    struct mem m;
    mem_init(&m);
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    struct err e;
    int32_t size = D - M;
    uint8_t *t = record(size);
    CHECK_EQ(rs_append(&r1, t, size, true, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), D + M);     /* the meta block is written with the record */
    s.length = D;
    struct rs r2;
    rs_init(&r2, &s);
    struct rs_recovery plan;
    CHECK_EQ(rcv_recover(&r2, &plan, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), D + M);
    CHECK_EQ(r2.posOfLastValidMetaBlock, 0);
    uint8_t *t2 = record(20);
    CHECK_EQ(rs_append(&r2, t2, 20, true, &e), ERR_OK);
    struct rs r3;
    rs_init(&r3, &s);
    CHECK_EQ(rcv_recover(&r3, &plan, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), D + M + 20);
    /* the records: the first, then the 20 bytes after the invalid block */
    struct ns_iter it;
    ns_iter_init(&it, &s, &m, M, true);
    bool has;
    CHECK_EQ(ns_iter_next(&it, &has, &e), ERR_OK);
    CHECK(has && it.size == size);
    CHECK_EQ(ns_iter_next(&it, &has, &e), ERR_OK);
    CHECK(has && it.size == 20);
    CHECK_EQ(ns_iter_next(&it, &has, &e), ERR_OK);
    CHECK(!has);
    ns_iter_free(&it);
    free(t);
    free(t2);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester.appendNamedTransactions: 'count' committed records of 1000
 * bytes, each named by the meta blocks after it (rs_append_record); their positions. */
static void append_named(struct rs *r, int count, int64_t *starts) {
    struct err e;
    uint8_t *t = record(1000);
    for (int i = 0; i < count; i++) {
        CHECK_EQ(rs_append_record(r, t, 1000, &starts[i], &e), ERR_OK);
    }
    free(t);
}

/* The committed records of a walk from position 0 (RecoverableStream.Iterator(r, 0)). */
static int committed_records(struct stream *s, struct mem *m) {
    struct ns_iter it;
    struct err e;
    bool has = true;
    int n = 0;
    ns_iter_init(&it, s, m, 0, false);
    while (has && ns_iter_next(&it, &has, &e) == ERR_OK && has) {
        n++;
    }
    ns_iter_free(&it);
    return n;
}

/* RecoverableStream.Tester.testRecoverOtherVersionWritesNothing and
 * testRecoverWithWrongKeyWritesNothing (bergdb 005-40): a recovery that cannot read the
 * meta blocks writes nothing, also when a crash has cut the stream at a meta block or in
 * it (0, 3, 5 and 50 bytes into the block at 200,000), where it filled that block out
 * first until 2026-10-25. Blocks of another version (155): VersioningStreamException,
 * which names it. Blocks whose magic bytes are not "berg", as a wrong key reads them
 * (C has no encryption, so the bytes are changed here): BadMagicBytes. The same stream
 * as it was written recovers as before the cut: from the block at 0, with the records
 * that end before the block at 200,000. */
TEST(recover_unreadable_meta_blocks_write_nothing) {
    struct mem m;
    mem_init(&m);
    struct err e;
    static int64_t starts[250];
    const int64_t cuts[4] = { 0, 3, 5, 50 };
    for (int damage = 0; damage < 3; damage++) {
        for (int c = 0; c < 4; c++) {
            struct stream s;
            stream_open_memory(&s, &m);
            struct rs r1;
            rs_init(&r1, &s);
            append_named(&r1, 250, starts);
            int complete = 0;
            for (int i = 0; i < 250; i++) {
                complete += rs_get_spos(starts[i], 1000) <= D ? 1 : 0;
            }
            for (int64_t pos = 0; pos + M <= stream_length(&s); pos += D) {
                if (damage == 0) {
                    s.bytes[pos + 1] ^= 0x5a;       /* "berg" read with another key */
                } else if (damage == 1) {
                    s.bytes[pos + 4] = 155;         /* the version, 155 */
                }
            }
            REQUIRE(stream_truncate_memory(&s, D + cuts[c], &e) == ERR_OK);
            struct rs r2;
            rs_init(&r2, &s);
            struct rs_recovery plan;
            enum err_code rc = rcv_recover(&r2, &plan, &e);
            if (damage == 0) {
                CHECK_EQ(rc, ERR_FORMAT);
                CHECK(strcmp(e.java, "BadMagicBytes") == 0);
                CHECK_EQ(stream_length(&s), D + cuts[c]);
            } else if (damage == 1) {
                CHECK_EQ(rc, ERR_FORMAT);
                CHECK(strcmp(e.java, "VersioningStreamException") == 0);
                CHECK(strstr(e.text, "155") != NULL);
                CHECK_EQ(stream_length(&s), D + cuts[c]);
            } else {
                CHECK_EQ(rc, ERR_OK);
                CHECK_EQ(r2.posOfLastValidMetaBlock, 0);
                CHECK_EQ(committed_records(&s, &m), complete);
                CHECK_EQ(complete, 199);
            }
            stream_close(&s);
        }
    }
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester.crashInTransHeader1 and crashInTransHeader2: a crash after one
 * byte of a record's size (1, of 1025) or two (2 and 0, of 65,538): with zeros alone the
 * size would be 1 or 2, below a record's least; transHeaderFixBytes adds 1 as the first
 * missing byte, so the record is 257 or 65,538 bytes, filled with zeros, failed. */
TEST(recover_crash_in_trans_header) {
    struct mem m;
    mem_init(&m);
    struct err e;
    for (int c = 0; c < 2; c++) {
        const int32_t size = c == 0 ? 1025 : 0x00010002;
        const int32_t have = c + 1;
        const int32_t fixed = c == 0 ? 1 + 256 : 2 + 65536;
        struct stream s;
        stream_open_memory(&s, &m);
        struct rs r1;
        rs_init(&r1, &s);
        uint8_t *t = record(size);
        CHECK_EQ(rs_append(&r1, t, size, true, &e), ERR_OK);
        REQUIRE(stream_truncate_memory(&s, M + have, &e) == ERR_OK);
        struct rs_recovery plan;
        recover_all(&s, &plan);
        CHECK_EQ(plan.torn, M);
        CHECK_EQ(plan.header_fix_len, 5 - have);
        CHECK_EQ(plan.torn_size, fixed);
        CHECK_EQ(stream_length(&s), M + fixed);
        uint8_t b[5];
        CHECK_EQ(stream_read(&s, M, b, 5, &e), ERR_OK);
        CHECK_EQ(bytes_get_int_le(b), fixed);
        CHECK_EQ(b[4], RS_TORN_HEADER_FILLER);
        CHECK_EQ(byte_at(&s, M + fixed - 1), 0);
        CHECK_EQ(committed_records(&s, &m), 0);
        free(t);
        stream_close(&s);
    }
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester.recoverFromMiddleOfStream: two records of 3 * 200,000 + 20
 * bytes, each named by the meta blocks after it; a recovery walks from the record that the
 * last valid block names, the first, and appends nothing. */
TEST(recover_from_middle_of_stream) {
    struct mem m;
    mem_init(&m);
    struct err e;
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    const int32_t size = 3 * D + 20;
    uint8_t *t = record(size);
    int64_t p1, p2;
    CHECK_EQ(rs_append_record(&r1, t, size, &p1, &e), ERR_OK);
    CHECK_EQ(stream_length(&s), 3 * (int64_t) D + 20 + 4 * M);
    CHECK_EQ(rs_append_record(&r1, t, size, &p2, &e), ERR_OK);
    const int64_t length = stream_length(&s);
    CHECK(length > 2 * (int64_t) size);
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(stream_length(&s), length);
    CHECK_EQ(plan.walk_from, p1);
    CHECK_EQ(plan.last_whole, p2);
    CHECK_EQ(plan.torn, SPOS_NULL);
    CHECK_EQ(committed_records(&s, &m), 2);
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

/* RecoverableStream.Tester.testIterator: three records of 20 bytes, their byte 5 1, 2 and
 * 3; after a recovery, which appends nothing, a walk gives them in order, with their bytes. */
TEST(recover_iterator) {
    struct mem m;
    mem_init(&m);
    struct err e;
    struct stream s;
    stream_open_memory(&s, &m);
    struct rs r1;
    rs_init(&r1, &s);
    uint8_t *t = record(20);
    for (int i = 1; i <= 3; i++) {
        t[5] = (uint8_t) i;
        CHECK_EQ(rs_append(&r1, t, 20, true, &e), ERR_OK);
    }
    CHECK_EQ(stream_length(&s), M + 60);
    struct rs_recovery plan;
    recover_all(&s, &plan);
    CHECK_EQ(stream_length(&s), M + 60);
    struct ns_iter it;
    bool has;
    ns_iter_init(&it, &s, &m, 0, false);
    for (int i = 1; i <= 3; i++) {
        CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && has);
        CHECK_EQ(it.size, 20);
        CHECK_EQ(it.buf.p[5], i);
    }
    CHECK(ns_iter_next(&it, &has, &e) == ERR_OK && !has);
    ns_iter_free(&it);
    free(t);
    stream_close(&s);
    CHECK_MEM_ZERO(&m);
}

const struct test recover_tests[] = {
    TEST_ENTRY(recover_crash_in_first_transaction),
    TEST_ENTRY(recover_crash_in_transaction_size),
    TEST_ENTRY(recover_crash_in_third_transaction),
    TEST_ENTRY(recover_large_transaction),
    TEST_ENTRY(recover_crash_in_large_transaction),
    TEST_ENTRY(recover_fill_writes_meta_blocks),
    TEST_ENTRY(recover_crash_in_meta_block_header),
    TEST_ENTRY(recover_crash_at_meta_block_position),
    TEST_ENTRY(recover_unreadable_meta_blocks_write_nothing),
    TEST_ENTRY(recover_crash_in_trans_header),
    TEST_ENTRY(recover_from_middle_of_stream),
    TEST_ENTRY(recover_iterator),
    TEST_END
};
