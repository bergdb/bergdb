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

const struct test recover_tests[] = {
    TEST_ENTRY(recover_crash_in_first_transaction),
    TEST_ENTRY(recover_crash_in_transaction_size),
    TEST_ENTRY(recover_crash_in_third_transaction),
    TEST_ENTRY(recover_large_transaction),
    TEST_ENTRY(recover_crash_in_large_transaction),
    TEST_ENTRY(recover_fill_writes_meta_blocks),
    TEST_ENTRY(recover_crash_in_meta_block_header),
    TEST_ENTRY(recover_crash_at_meta_block_position),
    TEST_END
};
