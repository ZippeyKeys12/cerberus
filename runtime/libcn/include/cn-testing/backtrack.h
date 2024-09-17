#ifndef CN_GEN_BACKTRACK_H
#define CN_GEN_BACKTRACK_H

#include <stdlib.h>

enum cn_gen_backtrack_request {
    CN_GEN_BACKTRACK_NONE,
    CN_GEN_BACKTRACK_ASSERT,
    CN_GEN_BACKTRACK_ALLOC
};

enum cn_gen_backtrack_request cn_gen_backtrack_type(void);

void cn_gen_backtrack_reset(void);

void cn_gen_backtrack_assert_failure(void);

void cn_gen_backtrack_relevant_add(char* varname);

int cn_gen_backtrack_relevant_contains(char* varname);

void cn_gen_backtrack_alloc_set(size_t sz);

size_t cn_gen_backtrack_alloc_get();

#endif // CN_GEN_BACKTRACK_H
