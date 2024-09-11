#include <stdio.h>

#include "backtrack.h"

int contains(char* var) {
    return 1;
}

#define CN_GEN_INIT()                                                                   \
    if (0) {                                                                            \
    cn_label_bennet_backtrack:                                                          \
        printf("Failed to generate value");                                             \
        exit(1);                                                                        \
    }

#define CN_GEN_UNIFORM(ty, sz) cn_gen_uniform_##ty(sz)

#define CN_GEN_ALLOC(sz) todo(sz)

#define CN_GEN_CALL(...) todo()

#define CN_GEN_ASSIGN(addr, ty, val) *(ty *)addr = val;

#define CN_GEN_LET_START(backtracks, var)                                               \
    int var##_backtracks = backtracks;                                                  \
    cn_label_##var##_gen:

#define CN_GEN_LET_END(backtracks, ty, var, gen, last_var)                              \
        ty var = gen; \
        if (0) {                                                                        \
        cn_label_##var##_backtrack:                                                     \
            if (var##_backtracks > 0 && contains((char*)#var)) {                        \
                var##_backtracks--;                                                     \
                goto cn_label_##var##_gen;                                              \
            } else {                                                                    \
                goto cn_label_##last_var##_backtrack;                                   \
            }\
        }

#define CN_GEN_RETURN(val) val

#define CN_GEN_ASSERT(cond, last_var)                                                   \
    if (!(cond)) {                                                                      \
       goto cn_label_##last_var##_backtrack;                                            \
    }

#define CN_GEN_MAP_START(map, i, i_ty, min, max)                                        \
    i_ty i = min;                                                                       \
    while (i < max) {

#define CN_GEN_MAP_BODY(perm)                                                           \
        if (perm) {

#define CN_GEN_MAP_END(map, i, i_bt, val)                                               \
            cn_map_set(map, cast_##i_bt##_to_cn_integer(i), val)                        \
            i++;\
        }\
    }
