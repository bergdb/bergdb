/* Unit tests of transseq (bergdb 012-09, part 1): Java's @Nano tests of
 * TransSeq, ported (the paced take since f89846d: testShare,
 * testDeadline, testDeadlineAfterDecrease, testDecrease,
 * testSumsAfterTake; and testTake1, testTake2, testTakeWithBudget,
 * testPosOfTransBefore), the checksum, StartupPos, and the
 * allocation-failure runs. The take's double vectors (share, dither) are
 * checked in t_vectors.c. */
#include "test.h"
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
     * below 0.5. */
    CHECK(ts_dither(1300) > 0.4055 && ts_dither(1300) < 0.4057);
    CHECK(ts_dither(1200) > 0.9943 && ts_dither(1200) < 0.9945);
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

const struct test transseq_tests[] = {
    TEST_ENTRY(transseq_add),
    TEST_ENTRY(transseq_pos_of_trans_before),
    TEST_ENTRY(transseq_take1),
    TEST_ENTRY(transseq_take2),
    TEST_ENTRY(transseq_take_with_budget),
    TEST_ENTRY(transseq_share),
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
