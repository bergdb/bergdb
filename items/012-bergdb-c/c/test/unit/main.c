/* The unit tests' runner (bergdb 012-04): build/test/unit [-l] [name...]. */
#define TEST_MAIN
#include "test.h"

extern const struct test jsem_tests[];
extern const struct test bytes_tests[];
extern const struct test checksum_tests[];
extern const struct test klong_tests[];
extern const struct test keys_tests[];
extern const struct test spos_tests[];
extern const struct test mem_tests[];
extern const struct test vectors_tests[];
extern const struct test stream_tests[];
extern const struct test rstream_tests[];
extern const struct test records_tests[];
extern const struct test knode_tests[];
extern const struct test obj_tests[];
extern const struct test tnode_tests[];
extern const struct test nwrite_tests[];
extern const struct test kmodel_tests[];
extern const struct test knodevec_tests[];
extern const struct test topvec_tests[];
extern const struct test roundtrip_tests[];
extern const struct test clock_tests[];
extern const struct test keymod_tests[];
extern const struct test transseq_tests[];
extern const struct test append_tests[];
extern const struct test strmap_tests[];

int main(int argc, char **argv) {
    const struct test *const tables[] = {
        jsem_tests,
        bytes_tests,
        checksum_tests,
        klong_tests,
        keys_tests,
        spos_tests,
        mem_tests,
        vectors_tests,
        stream_tests,
        rstream_tests,
        records_tests,
        knode_tests,
        obj_tests,
        tnode_tests,
        nwrite_tests,
        kmodel_tests,
        knodevec_tests,
        topvec_tests,
        roundtrip_tests,
        clock_tests,
        keymod_tests,
        transseq_tests,
        append_tests,
        strmap_tests,
        NULL
    };
    return test_main(argc, argv, "UNIT", tables);
}
