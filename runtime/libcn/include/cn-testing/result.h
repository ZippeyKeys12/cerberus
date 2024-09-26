#ifndef CN_TEST_RESULT_H
#define CN_TEST_RESULT_H

#include <stdint.h>

typedef uint64_t seed;

enum cn_test_result {
    CN_TEST_PASS,
    CN_TEST_FAIL,
    CN_TEST_SKIP
};

struct cn_test_summary {
    uint32_t passes;
    uint32_t fails;
    uint32_t skips;
};

#endif // CN_TEST_RESULT_H
