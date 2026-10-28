/* Unit tests of strmap (bergdb 012-09, part 1): Java's @Nano tests of
 * StringMap, ported; reclaim's row in HashMap's order (012-02, 8.13);
 * String.hashCode; parse's trimming; HashMap's resizes. Java's own texts
 * are in vectors/strmap.txt when it exists (t_vectors.c). */
#include "test.h"
#include "strmap.h"

static struct mem sm_m;
static struct err sm_e;

/* StringMap.test1. */
TEST(strmap_test1) {
    struct sm m;
    mem_init(&sm_m);
    sm_init(&m, &sm_m);
    const char *text = "k1=v1\nk2=v2\n";
    CHECK_EQ(sm_parse(&m, text, strlen(text), &sm_e), ERR_OK);
    CHECK(strcmp(sm_get(&m, "k1"), "v1") == 0);
    CHECK(strcmp(sm_get(&m, "k2"), "v2") == 0);
    CHECK(sm_get(&m, "k3") == NULL);
    sm_free(&m);
    CHECK_MEM_ZERO(&sm_m);
}

/* StringMap.test2: put, serialize and parse again. */
TEST(strmap_test2) {
    struct sm m, m2;
    char *text;
    size_t n;
    mem_init(&sm_m);
    sm_init(&m, &sm_m);
    CHECK_EQ(sm_put(&m, "name", "Nalia", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "id", "1234", &sm_e), ERR_OK);
    CHECK(strcmp(sm_get(&m, "name"), "Nalia") == 0);
    CHECK(strcmp(sm_get(&m, "id"), "1234") == 0);
    REQUIRE(sm_serialize(&m, &text, &n, &sm_e) == ERR_OK);
    /* HashMap's order: "name" in bucket 8, "id" in bucket 11. */
    CHECK(strcmp(text, "name=Nalia\nid=1234\n") == 0);
    sm_init(&m2, &sm_m);
    CHECK_EQ(sm_parse(&m2, text, n, &sm_e), ERR_OK);
    CHECK(strcmp(sm_get(&m2, "name"), "Nalia") == 0);
    CHECK(strcmp(sm_get(&m2, "id"), "1234") == 0);
    mem_free(&sm_m, text, n + 1, MEM_BUFFER);
    sm_free(&m);
    sm_free(&m2);
    CHECK_MEM_ZERO(&sm_m);
}

/* StringMap.testLong, and Long.parseLong's edges. */
TEST(strmap_long) {
    struct sm m;
    int64_t x = 0;
    mem_init(&sm_m);
    sm_init(&m, &sm_m);
    CHECK_EQ(sm_put(&m, "name", "Nalia", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "id", "1234", &sm_e), ERR_OK);
    CHECK(sm_has_long(&m, "id"));
    CHECK(!sm_has_long(&m, "name"));
    CHECK(!sm_has_long(&m, "x"));
    CHECK_EQ(sm_get_long(&m, "id", &x, &sm_e), ERR_OK);
    CHECK_EQ(x, 1234);
    CHECK_EQ(sm_get_long(&m, "x", &x, &sm_e), ERR_FORMAT);
    CHECK(strcmp(sm_e.text, "No value for key x") == 0);
    CHECK_EQ(sm_get_long(&m, "name", &x, &sm_e), ERR_FORMAT);
    CHECK(strcmp(sm_e.java, "NumberFormatException") == 0);
    CHECK(sm_parse_long("-9223372036854775808", 20, &x) && x == INT64_MIN);
    CHECK(sm_parse_long("9223372036854775807", 19, &x) && x == INT64_MAX);
    CHECK(!sm_parse_long("9223372036854775808", 19, &x));
    CHECK(sm_parse_long("+5", 2, &x) && x == 5);
    CHECK(!sm_parse_long("+", 1, &x));
    CHECK(!sm_parse_long("", 0, &x));
    CHECK(!sm_parse_long(" 5", 2, &x));
    CHECK(sm_parse_long("-1", 2, &x) && x == -1);
    sm_free(&m);
    CHECK_MEM_ZERO(&sm_m);
}

/* Reclaim's row (IterationInfo.serialize), its puts in Java's order: the
 * text of 012-02, 8.13. */
TEST(strmap_reclaim_row) {
    struct sm m;
    char *text;
    size_t n;
    mem_init(&sm_m);
    sm_init(&m, &sm_m);
    CHECK_EQ(sm_put(&m, "pStart", "5574880", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "pCut", "5041560", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "tStart", "10000289400000", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "tEnd", "0", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "kvCount", "466", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "lastKey", "26177508076421160", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "done", "false", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "cut", "false", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "rewritten", "102488", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "pEnd", "-1", &sm_e), ERR_OK);
    CHECK_EQ(sm_put(&m, "pSafe", "-1", &sm_e), ERR_OK);
    REQUIRE(sm_serialize(&m, &text, &n, &sm_e) == ERR_OK);
    CHECK(strcmp(text, "pCut=5041560\ntEnd=0\ncut=false\npStart=5574880\n"
            "tStart=10000289400000\nlastKey=26177508076421160\nrewritten=102488\npEnd=-1\n"
            "pSafe=-1\ndone=false\nkvCount=466\n") == 0);
    CHECK_EQ((int64_t) n, (int64_t) strlen(text));
    mem_free(&sm_m, text, n + 1, MEM_BUFFER);
    /* A put of a key that is there replaces its value in place. */
    CHECK_EQ(sm_put(&m, "pCut", "7", &sm_e), ERR_OK);
    REQUIRE(sm_serialize(&m, &text, &n, &sm_e) == ERR_OK);
    CHECK(strncmp(text, "pCut=7\ntEnd=0\n", 14) == 0);
    mem_free(&sm_m, text, n + 1, MEM_BUFFER);
    sm_free(&m);
    CHECK_MEM_ZERO(&sm_m);
}

/* String.hashCode over UTF-16 code units (values from Java's rule,
 * computed in Python). */
TEST(strmap_string_hash) {
    CHECK_EQ(sm_string_hash("hello", 5), 99162322);
    CHECK_EQ(sm_string_hash("pStart", 6), -1008297518);
    CHECK_EQ(sm_string_hash("", 0), 0);
    CHECK_EQ(sm_string_hash("\xc3\xbc", 2), 252);                   /* ü */
    CHECK_EQ(sm_string_hash("\xf0\x9f\x98\x80x", 5), 54959989);     /* a surrogate pair */
    CHECK_EQ(sm_string_hash("Stange\n\r  next line", 19), -1591410798);
}

/* parse: lines trimmed, a key before the first '=', a value after it
 * (possibly empty, with '='), lines without a key skipped. */
TEST(strmap_parse) {
    struct sm m;
    mem_init(&sm_m);
    sm_init(&m, &sm_m);
    const char *text = "  a = 1 \n=x\nnone\n\tb==2=\nc=\n\nd=last";
    CHECK_EQ(sm_parse(&m, text, strlen(text), &sm_e), ERR_OK);
    CHECK_EQ(m.n, 4);
    CHECK(strcmp(sm_get(&m, "a "), " 1") == 0);
    CHECK(strcmp(sm_get(&m, "b"), "=2=") == 0);
    CHECK(strcmp(sm_get(&m, "c"), "") == 0);
    CHECK(strcmp(sm_get(&m, "d"), "last") == 0);
    CHECK(sm_get(&m, "a") == NULL);
    sm_free(&m);
    CHECK_MEM_ZERO(&sm_m);
}

/* HashMap's table: 16, 32 after the 13th key, 64 after the 25th; the order
 * by bucket then by first put. Keys "k0" to "k39". */
TEST(strmap_resizes) {
    struct sm m;
    char key[8], value[8];
    mem_init(&sm_m);
    sm_init(&m, &sm_m);
    for (int i = 0; i < 40; i++) {
        snprintf(key, sizeof key, "k%d", i);
        snprintf(value, sizeof value, "%d", i);
        CHECK_EQ(sm_put(&m, key, value, &sm_e), ERR_OK);
        CHECK_EQ(m.tableSize, i < 12 ? 16 : i < 24 ? 32 : 64);
    }
    char *text;
    size_t n;
    REQUIRE(sm_serialize(&m, &text, &n, &sm_e) == ERR_OK);
    /* Each line's bucket is not below the one before. */
    int32_t last = -1;
    int lines = 0;
    for (char *p = text; *p != '\0'; lines++) {
        char *eq = strchr(p, '=');
        char *nl = strchr(p, '\n');
        int32_t h = sm_string_hash(p, (size_t) (eq - p));
        int32_t bucket = (h ^ (int32_t) ((uint32_t) h >> 16)) & 63;
        CHECK(bucket >= last);
        last = bucket;
        p = nl + 1;
    }
    CHECK_EQ(lines, 40);
    mem_free(&sm_m, text, n + 1, MEM_BUFFER);
    sm_free(&m);
    CHECK_MEM_ZERO(&sm_m);
}

/* NOMEM in turn: the map as it was. */
TEST(strmap_failure_runs) {
    for (int64_t k = 1; k < 30; k++) {
        struct sm m;
        mem_init(&sm_m);
        sm_m.fail_at = k;
        sm_init(&m, &sm_m);
        for (int i = 0; i < 5; i++) {
            char key[8];
            snprintf(key, sizeof key, "k%d", i);
            int32_t before = m.n;
            if (sm_put(&m, key, "v", &sm_e) != ERR_OK) {
                CHECK_EQ(sm_e.code, ERR_NOMEM);
                CHECK_EQ(m.n, before);
                break;
            }
        }
        sm_free(&m);
        CHECK_MEM_ZERO(&sm_m);
    }
}

const struct test strmap_tests[] = {
    TEST_ENTRY(strmap_test1),
    TEST_ENTRY(strmap_test2),
    TEST_ENTRY(strmap_long),
    TEST_ENTRY(strmap_reclaim_row),
    TEST_ENTRY(strmap_string_hash),
    TEST_ENTRY(strmap_parse),
    TEST_ENTRY(strmap_resizes),
    TEST_ENTRY(strmap_failure_runs),
    TEST_END
};
