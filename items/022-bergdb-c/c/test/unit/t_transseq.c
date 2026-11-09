/* Unit tests of transseq (bergdb 012-09, part 1): Java's @Nano tests of
 * TransSeq, ported (the paced take since f89846d: testShare,
 * testDeadline, testDeadlineAfterDecrease, testDecrease,
 * testSumsAfterTake; and testTake1, testTake2, testTakeWithBudget,
 * testPosOfTransBefore; the take in integers of bergdb 005-79, release
 * 2026.2: testShareFpExact, testShareFpClamp, testDivluExact,
 * testDitherFp, against unsigned __int128 where Java has BigInteger), the
 * checksum, StartupPos, and the allocation-failure runs. Java's own values
 * of the share and the dither are checked in t_vectors.c (jsem.txt). */
#include <inttypes.h>
#include "test.h"
#include "jsem.h"
#include "snode.h"
#include "transseq.h"

static struct mem tm;
static struct err te;

/* newTransInfo(tpos, lastPos, tt): no nodes, ownBytes(0). */
static struct ts_info *info3(int64_t tpos, int64_t lastPos, int64_t tt) {
    struct ts_info *info = ts_info_new(&tm);
    if (info == NULL) {
        return NULL;
    }
    info->tpos = tpos;
    info->lastPos = lastPos;
    info->tt = tt;
    info->ownBytes = ts_own_bytes(0);
    return info;
}

/* A node object of the tests: an id, and the order the take met it. */
struct tnode {
    int64_t id;
};

/* newTransInfo(tpos, lastPos, node): one key node. */
static struct ts_info *info_node(int64_t tpos, int64_t lastPos, struct tnode *node) {
    struct ts_info *info = info3(tpos, lastPos, -1);
    if (info != NULL) {
        ts_info_add_node(info, &tm, node, node->id, NODE_KEY, &te);
    }
    return info;
}

/* paceInfo(tpos, count, ownBytes): count got-dirty key nodes. */
static struct ts_info *pace_info(int64_t tpos, int32_t count, int64_t ownBytes) {
    struct ts_info *info = info3(tpos, tpos + 99, -1);
    info->ownBytes = ownBytes;
    for (int32_t i = 0; i < count; i++) {
        ts_info_add_node(info, &tm, NULL, 2 * i + 1, NODE_KEY, &te);
    }
    return info;
}

/* paceSeq(tpos): ten transactions from tpos, 100 apart, of 10 got-dirty
 * nodes and 100 own bytes. */
static void pace_seq(struct ts_seq *s, int64_t tpos) {
    ts_init(s, &tm);
    for (int i = 0; i < 10; i++) {
        ts_add(s, pace_info(tpos + 100 * i, 10, 100), &te);
    }
}

/* The nodes a take met, in order (Java's TransNodesForMe, a list). */
struct met {
    void *nodes[16];
    int n;
};

static int32_t meet(struct met *m, struct ts_info *taken) {
    int32_t count = 0;
    for (struct ts_info *t = taken; t != NULL; t = t->next) {
        for (int32_t i = 0; i < t->ndirty; i++) {
            if (m != NULL && m->n < 16) {
                m->nodes[m->n++] = t->gotDirtyNodes[i].node;
            }
            count++;
        }
    }
    ts_info_free_chain(taken, &tm);
    return count;
}

/* take with Long.MAX_VALUE as the budget; the nodes to m. */
static int64_t take(struct ts_seq *s, int64_t sp, int64_t length, int32_t sd, int64_t own,
        struct met *m, int32_t *count) {
    struct ts_info *taken;
    int32_t ntaken;
    int64_t r = ts_take(s, sp, length, sd, own, INT64_MAX, NULL, NULL, &taken, &ntaken);
    int32_t c = meet(m, taken);
    if (count != NULL) {
        *count = c;
    }
    return r;
}

/* TransSeq.test0, testAddOne, testAddThree. */
TEST(transseq_add) {
    struct ts_seq s;
    mem_init(&tm);
    ts_init(&s, &tm);
    CHECK_EQ(ts_size(&s), 0);
    CHECK(ts_is_empty(&s));
    CHECK_EQ(ts_span(&s), 0);

    CHECK_EQ(ts_add(&s, info3(120, 200, -1), &te), ERR_OK);
    CHECK_EQ(ts_size(&s), 1);
    CHECK(!ts_is_empty(&s));
    ts_free(&s);

    ts_init(&s, &tm);
    CHECK_EQ(ts_add(&s, info3(100, 120, -1), &te), ERR_OK);
    CHECK_EQ(ts_add(&s, info3(200, 220, -1), &te), ERR_OK);
    CHECK_EQ(ts_add(&s, info3(300, 320, -1), &te), ERR_OK);
    CHECK_EQ(ts_size(&s), 3);
    CHECK_EQ(ts_span(&s), 200);
    CHECK_EQ(s.ownBytes, 3 * 48);

    /* add refuses a tpos that is not later than the newest's. */
    struct ts_info *bad = info3(300, 320, -1);
    CHECK_EQ(ts_add(&s, bad, &te), ERR_ARG);
    CHECK(strcmp(te.text, "info.tpos <= last.tpos, 300, 300") == 0);
    CHECK_EQ(ts_size(&s), 3);
    ts_info_free(bad, &tm);
    CHECK_EQ(ts_add(&s, NULL, &te), ERR_ARG);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testPosOfTransBefore and testPosOfTransBeforeWithEmptySeq. */
TEST(transseq_pos_of_trans_before) {
    struct ts_seq s;
    mem_init(&tm);
    ts_init(&s, &tm);
    CHECK_EQ(ts_pos_of_trans_before(&s, 0), -1);
    CHECK_EQ(ts_pos_of_trans_before(&s, 99), -1);
    CHECK_EQ(ts_pos_of_trans_before(&s, INT64_MAX), -1);
    CHECK_EQ(ts_pos_of_trans_before(&s, INT64_MIN), -1);

    ts_add(&s, info3(100, 120, -1), &te);
    ts_add(&s, info3(200, 220, -1), &te);
    CHECK_EQ(ts_pos_of_trans_before(&s, 0), -1);
    CHECK_EQ(ts_pos_of_trans_before(&s, 99), -1);
    CHECK_EQ(ts_pos_of_trans_before(&s, 100), -1);
    CHECK_EQ(ts_pos_of_trans_before(&s, 101), 100);
    CHECK_EQ(ts_pos_of_trans_before(&s, 9999999), 200);
    CHECK_EQ(ts_pos_of_trans_before(&s, 160), 100);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testTake1: the deadline alone; a record of no own bytes has no
 * share. With sd 50, d_h = 100. */
TEST(transseq_take1) {
    struct ts_seq s;
    struct tnode n1 = { 1 }, n2 = { 3 };
    struct met m = { { NULL }, 0 };
    mem_init(&tm);
    ts_init(&s, &tm);
    ts_add(&s, info_node(100, 120, &n1), &te);
    ts_add(&s, info_node(200, 220, &n2), &te);

    take(&s, 0, 199, 50, 0, &m, NULL);
    CHECK_EQ(m.n, 0);

    take(&s, 0, 200, 50, 0, &m, NULL);
    CHECK_EQ(m.n, 1);
    CHECK(m.nodes[0] == &n1);

    take(&s, 0, 300, 50, 0, &m, NULL);
    CHECK_EQ(m.n, 2);
    CHECK(m.nodes[0] == &n1);
    CHECK(m.nodes[1] == &n2);
    CHECK(ts_is_empty(&s));
    CHECK(s.last == NULL);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testTake2. */
TEST(transseq_take2) {
    struct ts_seq s;
    struct tnode n1 = { 1 }, n2 = { 3 };
    struct met m = { { NULL }, 0 };
    mem_init(&tm);
    ts_init(&s, &tm);
    ts_add(&s, info_node(100, 120, &n1), &te);
    ts_add(&s, info_node(200, 220, &n2), &te);

    take(&s, 0, 300, 50, 0, &m, NULL);
    CHECK_EQ(m.n, 2);
    CHECK(m.nodes[0] == &n1);
    CHECK(m.nodes[1] == &n2);
    CHECK(ts_is_empty(&s));
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* The cost of the budget test: each node a fixed size (StoredKeyNode's
 * of an empty KeyNode in Java's test; any fixed size here) and 16. */
#define NODE_COST (40 + 16)

static int64_t cost_fn(void *ctx, const struct ts_info *info) {
    int *calls = ctx;
    (*calls)++;
    return (int64_t) info->ndirty * NODE_COST;
}

/* TransSeq.testTakeWithBudget (005-17): whole transactions, as many as
 * fit; the cost asked for only while the budget is not Long.MAX_VALUE. */
TEST(transseq_take_with_budget) {
    struct ts_seq s;
    struct tnode n1 = { 1 }, n2 = { 3 }, n3 = { 5 };
    struct met m = { { NULL }, 0 };
    struct ts_info *taken;
    int32_t ntaken;
    int calls = 0;
    const int64_t cost = NODE_COST;
    mem_init(&tm);
    ts_init(&s, &tm);
    ts_add(&s, info_node(100, 120, &n1), &te);
    ts_add(&s, info_node(200, 220, &n2), &te);
    ts_add(&s, info_node(300, 320, &n3), &te);

    /* All three are past the deadline, d_h = 300, longer than their span,
     * 200, and have no share; the budget decides. */
    CHECK_EQ(ts_take(&s, 0, 600, 150, 0, cost - 1, cost_fn, &calls, &taken, &ntaken), 0);
    CHECK_EQ(meet(&m, taken), 0);
    CHECK_EQ(ntaken, 0);
    CHECK_EQ(calls, 1);
    CHECK_EQ(ts_take(&s, 0, 600, 150, 0, 2 * cost + 1, cost_fn, &calls, &taken, &ntaken), 200);
    CHECK_EQ(ntaken, 2);
    CHECK_EQ(meet(&m, taken), 2);
    CHECK_EQ(m.n, 2);
    CHECK_EQ(calls, 4);
    CHECK_EQ(ts_take(&s, 200, 600, 150, 0, cost, cost_fn, &calls, &taken, &ntaken), 300);
    CHECK_EQ(meet(&m, taken), 1);
    CHECK_EQ(m.n, 3);
    CHECK(m.nodes[0] == &n1 && m.nodes[1] == &n2 && m.nodes[2] == &n3);
    CHECK(ts_is_empty(&s));

    /* With Long.MAX_VALUE the cost is not asked for. */
    calls = 0;
    ts_add(&s, info_node(400, 420, &n1), &te);
    CHECK_EQ(ts_take(&s, 0, 1000, 150, 0, INT64_MAX, cost_fn, &calls, &taken, &ntaken), 400);
    CHECK_EQ(meet(NULL, taken), 1);
    CHECK_EQ(calls, 0);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testShare: the share (005-49), the transactions that fit, and
 * the next with the probability of the part that fits. */
TEST(transseq_share) {
    struct ts_seq s;
    mem_init(&tm);

    /* D = 100 nodes, O = 1000 bytes. A record of 100 own bytes, a section
     * of 2000 and sd 800: a share of 25 nodes, two transactions and half
     * of the third, which is taken if the hash of the stream's length is
     * below 0.5. In units of 2^-16 (bergdb 005-79): the share 25 * 2^16,
     * and the hashes 26,583 and 65,167, 0.4056 and 0.9944. */
    CHECK_EQ(ts_share_fp(100, 100, 1000, 2000, 800), INT64_C(25) << 16);
    CHECK_EQ(ts_dither_fp(1300), 26583);
    CHECK_EQ(ts_dither_fp(1200), 65167);
    pace_seq(&s, 0);
    CHECK_EQ(take(&s, 1300 - 2000, 1300, 800, 100, NULL, NULL), 200);
    CHECK_EQ(ts_size(&s), 7);
    ts_free(&s);
    pace_seq(&s, 0);
    CHECK_EQ(take(&s, 1200 - 2000, 1200, 800, 100, NULL, NULL), 100);
    CHECK_EQ(ts_size(&s), 8);
    ts_free(&s);

    /* Half the section, half the share: 12.5 nodes, one transaction and a
     * quarter of the next, which the hash 0.41 does not take. */
    pace_seq(&s, 0);
    CHECK_EQ(take(&s, 1300 - 1000, 1300, 800, 100, NULL, NULL), 0);
    CHECK_EQ(ts_size(&s), 9);
    ts_free(&s);

    /* A tie, which the take stops at (<=; bergdb 005-79, the review of
     * Part B): the part that fits, all of the share, 297,636 / 2^16 nodes,
     * equals u times the transaction's 6 nodes, 49,606 * 6. It is
     * StreamDigest's l3-node14's one take where the double rule of
     * 2026-10-28 differs: that rule took the transaction. One transaction
     * of 6 nodes at 500,000, the stream's length 531,776, sd 2^16, a
     * section of u bytes, and o = O = 1000 own bytes. */
    const int64_t tieLength = 531776;
    CHECK_EQ(ts_dither_fp(tieLength), 49606);
    CHECK_EQ(ts_share_fp(6, 1000, 1000, 49606, 65536), 297636);
    ts_init(&s, &tm);
    ts_add(&s, pace_info(500000, 6, 1000), &te);
    CHECK_EQ(take(&s, tieLength - 49606, tieLength, 65536, 1000, NULL, NULL),
            tieLength - 49606);
    CHECK_EQ(ts_size(&s), 1);
    ts_free(&s);

    /* On average a record takes its share, 2.5 transactions, also when
     * what it takes decides the length of the stream, and so the hash, for
     * the next record. A record is 400 bytes and 104 for each transaction
     * taken. */
    int64_t transactions = 0;
    int64_t length = 8000000;
    for (int i = 0; i < 10000; i++) {
        pace_seq(&s, length - 1500);
        take(&s, length - 2000, length, 800, 100, NULL, NULL);
        const int32_t taken = 10 - ts_size(&s);
        transactions += taken;
        length += 400 + 104 * taken;
        ts_free(&s);
    }
    double mean = (double) transactions / 10000.0;
    CHECK(mean > 2.48 && mean < 2.52);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testDeadline (007-03, step 3; 007-07): a transaction that
 * begins d_h = 2 * sd or more before the end of the stream is taken
 * whatever the share; or, while the span is longer than d_h, one that
 * begins the span or more before the end. */
TEST(transseq_deadline) {
    struct ts_seq s;
    mem_init(&tm);
    ts_init(&s, &tm);
    for (int i = 0; i < 5; i++) {
        ts_add(&s, pace_info(100 * i, 1000, 100), &te);
    }
    /* A record of 1 own byte: a share of 32 nodes, less than a
     * transaction. With sd 250, d_h = 500, longer than the span, 400:
     * takes the transactions at 0 to 300; the one at 400 waits. */
    CHECK_EQ(take(&s, -1, 800, 250, 1, NULL, NULL), 300);
    CHECK_EQ(ts_size(&s), 1);
    CHECK_EQ(s.first->tpos, 400);
    ts_free(&s);

    /* With sd 100, d_h = 200 is shorter than the span: the deadline is at
     * the span. It takes the transactions at 0 and 100. */
    ts_init(&s, &tm);
    for (int i = 0; i < 5; i++) {
        ts_add(&s, pace_info(100 * i, 1000, 100), &te);
    }
    CHECK_EQ(take(&s, -1, 500, 100, 1, NULL, NULL), 100);
    CHECK_EQ(ts_size(&s), 3);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testDeadlineAfterDecrease (007-07): records of no own bytes
 * have no share; transactions 100 apart from 0 to 1900, records of 100
 * bytes, sd 100, so d_h = 200. Each record takes the two that begin
 * within the last record's length of the oldest, so the span shrinks by a
 * record each time until it is below d_h. */
TEST(transseq_deadline_after_decrease) {
    struct ts_seq s;
    mem_init(&tm);
    ts_init(&s, &tm);
    for (int i = 0; i < 20; i++) {
        ts_add(&s, pace_info(100 * i, 10, 100), &te);
    }
    int64_t length = 2000;
    int64_t sp = -1;
    for (int i = 0; i < 40; i++) {
        const int64_t span = ts_span(&s);
        const int32_t size = ts_size(&s);
        sp = take(&s, sp, length, 100, 0, NULL, NULL);
        if (span >= 200) {
            CHECK_EQ(ts_size(&s), size - 2);
        }
        ts_add(&s, pace_info(length, 10, 100), &te);
        CHECK(s.first->tpos > length - (200 >= span ? 200 : span));
        if (span >= 200) {
            CHECK_EQ(ts_span(&s), span - 100);
        }
        length += 100;
    }
    CHECK_EQ(ts_span(&s), 100);
    CHECK_EQ(ts_size(&s), 2);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testDecrease (007-03, D4; 007-07): sd 100000 lowered to 25000;
 * no record takes more than its share, and the span shrinks with every
 * record until it is below twice the setting. */
TEST(transseq_decrease) {
    struct ts_seq s;
    mem_init(&tm);
    ts_init(&s, &tm);
    int64_t length = 0;
    int64_t sp = -1;
    int32_t sd = 100000;
    int below = -1;
    for (int i = 0; i < 1300; i++) {
        int32_t taken;
        if (i == 1000) {
            sd = 25000;
        }
        const int64_t span = ts_span(&s);
        sp = take(&s, sp, length, sd, 1000, NULL, &taken);
        ts_add(&s, pace_info(length, 10, 1000), &te);

        /* The deadline, at the span while that is longer than 2 * sd: the
         * span shrinks. */
        const int64_t d = 2 * (int64_t) sd >= span ? 2 * (int64_t) sd : span;
        CHECK(s.first->tpos > length - d);
        if (span >= 2 * (int64_t) sd) {
            CHECK(ts_span(&s) < span);
        }
        length += 1000 + 100 * taken;

        /* At the decrease the section is 100000, so the share is 40
         * nodes, and it shrinks with the section. */
        if (i >= 1000) {
            CHECK(taken <= 40);
            if (below < 0 && ts_span(&s) < 2 * (int64_t) sd) {
                below = i - 1000;
            }
        }
    }
    CHECK(below >= 0 && below <= 20);
    CHECK(length - sp >= 25000 - 5000 && length - sp <= 25000 + 5000);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testSumsAfterTake: the sums are those of the transactions left,
 * so a start, which adds the section's transactions again, has the same
 * sums and checksum (005-49; 010, P2). */
TEST(transseq_sums_after_take) {
    struct ts_seq s, r;
    mem_init(&tm);
    ts_init(&s, &tm);
    for (int i = 0; i < 6; i++) {
        ts_add(&s, pace_info(100 * i, i + 1, 50 + 10 * i), &te);
    }
    /* d_h = 520, longer than the span, 500, takes the transactions at 0 to
     * 300. */
    CHECK_EQ(take(&s, -1, 820, 260, 1, NULL, NULL), 300);

    ts_init(&r, &tm);
    for (struct ts_info *a = s.first; a != NULL; a = a->next) {
        struct ts_info *b = info3(a->tpos, a->lastPos, a->tt);
        b->startupPos = a->startupPos;
        b->ownBytes = a->ownBytes;
        for (int32_t i = 0; i < a->ndirty; i++) {
            ts_info_add_node(b, &tm, a->gotDirtyNodes[i].node, a->gotDirtyNodes[i].id,
                    a->gotDirtyNodes[i].type, &te);
        }
        ts_add(&r, b, &te);
    }
    CHECK_EQ(ts_size(&r), 2);
    CHECK_EQ(r.dirtyCount, 5 + 6);
    CHECK_EQ(r.ownBytes, 90 + 100);
    CHECK_EQ(r.dirtyCount, s.dirtyCount);
    CHECK_EQ(r.ownBytes, s.ownBytes);
    CHECK_EQ(ts_checksum(&r), ts_checksum(&s));
    ts_free(&s);
    ts_free(&r);
    CHECK_MEM_ZERO(&tm);
}

/* The checksum is java.util.zip.CRC32 over MyChecksum's bytes (values from
 * Python's zlib.crc32 over the same bytes). */
TEST(transseq_checksum) {
    struct ts_seq s;
    mem_init(&tm);
    ts_init(&s, &tm);
    CHECK_EQ(ts_checksum(&s), INT64_C(2747386400));     /* 24 zero bytes */
    struct ts_info *info = info3(100, 120, -1);
    ts_info_add_node(info, &tm, NULL, 7, NODE_KEY, &te);
    ts_info_add_node(info, &tm, NULL, 9, NODE_TOP, &te);
    ts_add(&s, info, &te);
    CHECK_EQ(ts_checksum(&s), INT64_C(3655751955));
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

static void visit_fn(void *ctx, const struct ts_node *node, int64_t tpos, int64_t lastTpos) {
    int64_t *sum = ctx;
    *sum += node->id * 1000000 + tpos * 1000 + (lastTpos - tpos);
}

/* TransSeq.visitGotDirtyNodes: the nodes of the transactions with tpos at
 * most the limit. */
TEST(transseq_visit) {
    struct ts_seq s;
    int64_t sum = 0;
    mem_init(&tm);
    ts_init(&s, &tm);
    ts_visit_got_dirty_nodes(&s, 1000, visit_fn, &sum);
    CHECK_EQ(sum, 0);
    ts_add(&s, pace_info(100, 2, 48), &te);     /* ids 1 and 3, lastPos tpos + 99 */
    ts_add(&s, pace_info(200, 1, 48), &te);
    ts_visit_got_dirty_nodes(&s, 199, visit_fn, &sum);
    CHECK_EQ(sum, (1 + 3) * 1000000 + 2 * (100 * 1000 + 99));
    sum = 0;
    ts_visit_got_dirty_nodes(&s, 200, visit_fn, &sum);
    CHECK_EQ(sum, (1 + 3 + 1) * 1000000 + 2 * (100 * 1000 + 99) + 200 * 1000 + 99);
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* StartupPos. */
TEST(transseq_startup_pos) {
    struct ts_startup_pos p;
    CHECK_EQ(ts_startup_pos_init(&p, -1, &te), ERR_ARG);
    CHECK_EQ(ts_startup_pos_init(&p, 0, &te), ERR_OK);
    CHECK_EQ(ts_startup_pos_get(&p), 0);
    ts_startup_pos_set(&p, 128);
    CHECK_EQ(ts_startup_pos_get(&p), 128);
    CHECK_EQ(p.evictPos, 0);
    ts_startup_pos_release_for_evict(&p);
    CHECK_EQ(p.evictPos, 128);
}

/* ts_info_add_node fails cleanly: NOMEM, nothing added. */
TEST(transseq_failure_runs) {
    for (int64_t n = 1; n < 10; n++) {
        mem_init(&tm);
        tm.fail_at = n;
        struct ts_info *info = ts_info_new(&tm);
        if (info == NULL) {
            CHECK_EQ(n, 1);
            CHECK_MEM_ZERO(&tm);
            continue;
        }
        int added = 0;
        for (int i = 0; i < 9; i++) {
            if (ts_info_add_node(info, &tm, NULL, i, NODE_KEY, &te) != ERR_OK) {
                CHECK_EQ(te.code, ERR_NOMEM);
                break;
            }
            added++;
        }
        CHECK_EQ(info->ndirty, added);
        ts_info_free(info, &tm);
        CHECK_MEM_ZERO(&tm);
    }
}

/* ======== The take in integers, bergdb 005-79 ======== */

/* SplitMix64, the tests' random numbers (not Java's sequences: each case
 * is checked against the exact value, so the cases need not be Java's). */
static uint64_t sm_state;

static int64_t sm_next(void) {
    uint64_t z = (sm_state += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return (int64_t) (z ^ (z >> 31));
}

/* A number below 2^k, with k uniform from 0 to maxBits (TransSeq.spread). */
static int64_t spread(int maxBits) {
    const int k = (int) ((uint64_t) sm_next() % (uint64_t) (maxBits + 1));
    return k == 0 ? 0 : (int64_t) ((uint64_t) sm_next() >> (64 - k));
}

/* A number in [0, n), n > 0. */
static int64_t below(int64_t n) {
    return (int64_t) ((uint64_t) sm_next() % (uint64_t) n);
}

/* The exact reference of the tests: clang's and gcc's 128-bit integers. */
__extension__ typedef unsigned __int128 u128;

/* shareFp as unsigned __int128 computes it (Java's shareExact, with
 * BigInteger): floor(D o S 2^16 / (O sd)), at most D 2^16; within the
 * bounds, D o S 2^16 is below 2^126 and O sd below 2^94. */
static int64_t share_exact(int64_t D, int64_t o, int64_t O, int64_t S, int32_t sd) {
    const u128 x = (u128) (uint64_t) D * (uint64_t) o
            * (uint64_t) S << 16;
    const u128 q = x / ((u128) (uint64_t) O * (uint64_t) sd);
    const u128 max = (u128) (uint64_t) D << 16;
    return (int64_t) (q < max ? q : max);
}

static int share_fails;

static void check_share_fp(int64_t D, int64_t o, int64_t O, int64_t S, int32_t sd) {
    const int64_t expected = share_exact(D, o, O, S, sd);
    const int64_t actual = ts_share_fp(D, o, O, S, sd);
    if (actual != expected && share_fails++ < 5) {
        printf("ts_share_fp(%" PRId64 ", %" PRId64 ", %" PRId64 ", %" PRId64 ", %d) = %" PRId64
                ", exactly %" PRId64 "\n", D, o, O, S, sd, actual, expected);
    }
    CHECK_EQ(actual, expected);
}

static void check_divlu(int64_t u1, int64_t u0, int64_t v) {
    const u128 x = (u128) (uint64_t) u1 << 64 | (uint64_t) u0;
    const int64_t expected = (int64_t) (uint64_t) (x / (uint64_t) v);
    CHECK_EQ(ts_divlu(u1, u0, v), expected);
}

/* TransSeq.testDivluExact: divlu, the 128 by 64-bit division of shareFp,
 * against unsigned __int128: unsigned words that use all 64 bits, divisors
 * of every bit length, the quotient below 2^64 (u1 < v), and the edges,
 * where the estimated quotient digits are corrected. */
TEST(transseq_divlu_exact) {
    const int64_t m = -1;                       /* 2^64 - 1 */
    const int64_t vs[] = {1, 2, 3, 10, INT64_C(0xFFFFFFFF), INT64_C(1) << 32,
            (INT64_C(1) << 32) + 1, INT64_MAX, INT64_MIN, INT64_MIN + 1, m - 1, m,
            J64(0x8000000080000000), J64(0xFFFFFFFF00000000), J64(0x80000000FFFFFFFF)};
    for (size_t i = 0; i < sizeof vs / sizeof vs[0]; i++) {
        const int64_t v = vs[i];
        const int64_t u1s[] = {0, 1, v - 1, j_ushr64(v - 1, 1), j_divu64(v, 3)};
        for (size_t j = 0; j < sizeof u1s / sizeof u1s[0]; j++) {
            const int64_t u1 = u1s[j];
            if (j_cmpu64(u1, v) >= 0) {
                continue;
            }
            const int64_t u0s[] = {0, 1, m, INT64_MIN, INT64_MAX, INT64_C(0xFFFFFFFF),
                    J64(0xFFFFFFFF00000000), v, v - 1};
            for (size_t k = 0; k < sizeof u0s / sizeof u0s[0]; k++) {
                check_divlu(u1, u0s[k], v);
            }
        }
    }
    sm_state = 7905;
    for (int i = 0; i < 100000; i++) {
        int64_t v = spread(64);
        if (v == 0) {
            v = 1;
        }
        int64_t u1 = j_remu64(spread(64), v);
        if (i % 4 == 0) {
            u1 = v - 1 - (u1 & 0xFF);           /* near v: corrections */
            if (j_cmpu64(u1, v) >= 0) {
                u1 = v - 1;
            }
        }
        check_divlu(u1, sm_next(), v);
    }
}

/* TransSeq.testShareFpExact: shareFp against the exact floor, clamped at
 * D 2^16, on 10^5 cases: half spread over the bit lengths within the
 * bounds, which mostly clamp; half as BergDB has them, a section near sd
 * and o at most O, where the share is a few nodes; and on the edges, each
 * bound at its largest, O = 1, sd = 10, o = 0 and D = 0. */
TEST(transseq_share_fp_exact) {
    const int64_t dMax = (INT64_C(1) << 32) - 1, oMax = (INT64_C(1) << 31) - 1;
    const int64_t sMax = (INT64_C(1) << 47) - 1;
    const int32_t sdMax = INT32_MAX;
    const int64_t Ds[] = {0, 1, 1000, dMax};
    const int64_t os[] = {0, 1, 48, oMax};
    const int64_t Ss[] = {0, 1, 10, INT64_C(1) << 31, sMax};
    const int64_t Os[] = {1, 48, oMax, sMax + 1, INT64_MAX};
    const int32_t sds[] = {10, 1 << 20, sdMax};
    share_fails = 0;
    for (int a = 0; a < 4; a++) {
        for (int b = 0; b < 4; b++) {
            for (int c = 0; c < 5; c++) {
                for (int d = 0; d < 5; d++) {
                    for (int f = 0; f < 3; f++) {
                        check_share_fp(Ds[a], os[b], Os[d], Ss[c], sds[f]);
                    }
                }
            }
        }
    }
    sm_state = 79;
    for (int i = 0; i < 50000; i++) {
        const int64_t D = spread(32), o = spread(31), S = spread(47);
        const int64_t O = i % 2 == 0 ? 1 + j_remu64(spread(48), S + 1)
                : 1 + spread(62) + spread(62);
        const int32_t sd = 10 + (int32_t) j_remu64(spread(31), sdMax - INT64_C(9));
        check_share_fp(D, o, O, S, sd);
    }
    for (int i = 0; i < 50000; i++) {
        const int32_t sd = 10 + (int32_t) j_remu64(spread(31), sdMax - INT64_C(9));
        const int64_t S = below(INT64_C(4) * sd + 1);
        const int64_t O = 48 + below(S + 1);
        const int64_t oCap = (INT64_C(1) << 31) - 48;
        const int64_t o = 48 + below(O < oCap ? O : oCap);
        const int64_t D = below(1 + (dMax < O / 40 ? dMax : O / 40));
        check_share_fp(D, o, O, S, sd);
    }
}

/* TransSeq.testShareFpClamp: outside the bounds the share is all of D,
 * INT64_MAX, and every transaction before the deadline is taken: D = 2^32,
 * S = 2^47, o = 2^31, O or sd not positive. At the bounds' largest values
 * the share is D 2^16 here, the min. */
TEST(transseq_share_fp_clamp) {
    struct ts_seq s;
    mem_init(&tm);
    CHECK_EQ(ts_share_fp(INT64_C(1) << 32, 48, 1000, 2000, 800), INT64_MAX);
    CHECK_EQ(ts_share_fp(100, 48, 1000, INT64_C(1) << 47, 800), INT64_MAX);
    CHECK_EQ(ts_share_fp(100, INT64_C(1) << 31, 1000, 2000, 800), INT64_MAX);
    CHECK_EQ(ts_share_fp(100, 48, 0, 2000, 800), INT64_MAX);
    CHECK_EQ(ts_share_fp(100, 48, 1000, 2000, 0), INT64_MAX);
    CHECK_EQ(ts_share_fp(-1, 48, 1000, 2000, 800), INT64_MAX);
    const int64_t dMax = (INT64_C(1) << 32) - 1;
    CHECK_EQ(ts_share_fp(dMax, (INT64_C(1) << 31) - 1, 1, (INT64_C(1) << 47) - 1, 10),
            dMax << 16);

    /* Beyond the bounds a record takes every transaction before the
     * deadline. */
    ts_init(&s, &tm);
    for (int i = 0; i < 10; i++) {
        ts_add(&s, pace_info((INT64_C(1) << 48) + 100 * i, 10, 100), &te);
    }
    const int64_t length = (INT64_C(1) << 48) + 2000;
    CHECK_EQ(take(&s, 0, length, 800, 100, NULL, NULL), (INT64_C(1) << 48) + 900);
    CHECK(ts_is_empty(&s));
    ts_free(&s);
    CHECK_MEM_ZERO(&tm);
}

/* TransSeq.testDitherFp: ditherFp is the floor of the double dither of
 * 005-49 times 2^16, the top 16 of its 53 bits. */
TEST(transseq_dither_fp) {
    sm_state = 79;
    for (int i = 0; i < 1000; i++) {
        const int64_t pos = i < 500 ? i : sm_next();
        int64_t z = pos * J64(0x9E3779B97F4A7C15);
        z = (z ^ j_ushr64(z, 30)) * J64(0xBF58476D1CE4E5B9);
        z = (z ^ j_ushr64(z, 27)) * J64(0x94D049BB133111EB);
        const int64_t top53 = j_ushr64(z ^ j_ushr64(z, 31), 11);
        const int32_t u = ts_dither_fp(pos);
        CHECK(u >= 0 && u < 65536);
        CHECK_EQ(u, j_ushr64(top53, 37));
    }
}

const struct test transseq_tests[] = {
    TEST_ENTRY(transseq_add),
    TEST_ENTRY(transseq_pos_of_trans_before),
    TEST_ENTRY(transseq_take1),
    TEST_ENTRY(transseq_take2),
    TEST_ENTRY(transseq_take_with_budget),
    TEST_ENTRY(transseq_share),
    TEST_ENTRY(transseq_share_fp_exact),
    TEST_ENTRY(transseq_share_fp_clamp),
    TEST_ENTRY(transseq_divlu_exact),
    TEST_ENTRY(transseq_dither_fp),
    TEST_ENTRY(transseq_deadline),
    TEST_ENTRY(transseq_deadline_after_decrease),
    TEST_ENTRY(transseq_decrease),
    TEST_ENTRY(transseq_sums_after_take),
    TEST_ENTRY(transseq_checksum),
    TEST_ENTRY(transseq_visit),
    TEST_ENTRY(transseq_startup_pos),
    TEST_ENTRY(transseq_failure_runs),
    TEST_END
};
