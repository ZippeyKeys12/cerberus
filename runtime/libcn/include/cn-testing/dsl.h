#ifndef CN_GEN_DSL_H
#define CN_GEN_DSL_H

#include <stdio.h>

#include "backtrack.h"


#define CN_GEN_INIT()                                                                   \
    cn_gen_alloc_reset();                                                               \
    if (0) {                                                                            \
    cn_label_bennet_backtrack:                                                          \
        return NULL;                                                                    \
    }

#define CN_GEN_UNIFORM(ty, sz) cn_gen_uniform_##ty(sz)

#define CN_GEN_CALL(...) todo()

#define CN_GEN_ASSIGN(p, offset, addr_ty, value, gen_name, last_var)                    \
    if (!convert_from_cn_bool(cn_bits_u64_lt(offset, cn_gen_alloc_size(p)))) {          \
        cn_gen_backtrack_alloc_set((size_t)offset->val + 1);                            \
        goto cn_label_##last_var##_backtrack;                                           \
    }                                                                                   \
    void *tmp = convert_from_cn_pointer(cn_pointer_add_cn_bits_u64(dst, offset));       \
    *(addr_ty*)tmp = value;                                                             \
    cn_assume_ownership((void*)tmp, sizeof(addr_ty), (char*)gen_name);

#define CN_GEN_LET_BEGIN(backtracks, var)                                               \
    int var##_backtracks = backtracks;                                                  \
    cn_label_##var##_gen:                                                               \
        ;

#define CN_GEN_LET_END(backtracks, ty, var, gen, last_var)                              \
        ty* var = gen;                                                                  \
        if (0) {                                                                        \
        cn_label_##var##_backtrack:                                                     \
            if (var##_backtracks > 0                                                    \
                    && cn_gen_backtrack_assert_contains((char*)#var)) {                 \
                var##_backtracks--;                                                     \
                cn_gen_backtrack_alloc_reset();                                         \
                goto cn_label_##var##_gen;                                              \
            } else {                                                                    \
                goto cn_label_##last_var##_backtrack;                                   \
            }\
        }

// #define CN_GEN_RETURN(val) val

// From: http://jhnet.co.uk/articles/cpp_magic#turning-multiple-expansion-passes-into-recursion

#define EMPTY()
#define DEFER2(m) m EMPTY EMPTY()()

#define EVAL16(...) EVAL8(EVAL8(__VA_ARGS__))
#define EVAL8(...) EVAL4(EVAL4(__VA_ARGS__))
#define EVAL4(...) EVAL2(EVAL2(__VA_ARGS__))
#define EVAL2(...) EVAL1(EVAL1(__VA_ARGS__))
#define EVAL1(...) __VA_ARGS__

#define SECOND(a, b, ...) b

#define IS_PROBE(...) SECOND(__VA_ARGS__, 0)
#define PROBE() ~, 1

#define CAT(a,b) a ## b

#define NOT(x) IS_PROBE(CAT(_NOT_, x))
#define _NOT_0 PROBE()

#define BOOL(x) NOT(NOT(x))

#define IF_ELSE(condition) _IF_ELSE(BOOL(condition))
#define _IF_ELSE(condition) CAT(_IF_, condition)

#define _IF_1(...) __VA_ARGS__ _IF_1_ELSE
#define _IF_0(...)             _IF_0_ELSE

#define _IF_1_ELSE(...)
#define _IF_0_ELSE(...) __VA_ARGS__

#define FIRST(a, ...) a

#define HAS_ARGS(...) BOOL(FIRST(_END_OF_ARGUMENTS_ __VA_ARGS__)())
#define _END_OF_ARGUMENTS_() 0

#define MAP(m, first, ...)           \
  m(first)                           \
  IF_ELSE(HAS_ARGS(__VA_ARGS__))(    \
    DEFER2(_MAP)()(m, __VA_ARGS__)   \
  )(                                 \
    /* Do nothing, just terminate */ \
  )
#define _MAP() MAP

// End from

#define CN_GEN_ASSERT_START(cond)                                                       \
    if (!(cond)) {                                                                      \
        cn_gen_backtrack_reset();

#define _CN_GEN_ASSERT_REC(varname)                                                 \
    cn_gen_backtrack_assert_add((char*)#varname);

#define CN_GEN_ASSERT_REC(varname, ...)                                                 \
    EVAL16(MAP(_CN_GEN_ASSERT_REC, varname, __VA_ARGS__))

#define CN_GEN_ASSERT_END(last_var)                                                     \
       goto cn_label_##last_var##_backtrack;                                            \
    }

#define CN_GEN_ASSERT(cond, last_var, ...) \
    CN_GEN_ASSERT_START(cond) \
    CN_GEN_ASSERT_REC(__VA_ARGS__) \
    CN_GEN_ASSERT_END(last_var)

#define CN_GEN_MAP_BEGIN(map, i, i_ty, min, max)                                        \
    cn_map* map = map_create();                                                         \
    {                                                                                   \
        i_ty* i = min;                                                                  \
        while (convert_from_cn_bool(i_ty##_le(i, max))) {

#define CN_GEN_MAP_BODY(perm)                                                           \
            if (convert_from_cn_bool(perm)) {

#define CN_GEN_MAP_END(map, i, i_ty, max, val)                                          \
                cn_map_set(map, cast_##i_ty##_to_cn_integer(i), val);                   \
            }                                                                           \
            if (convert_from_cn_bool(i_ty##_equality(i, max))) {                        \
                break;                                                                  \
            }                                                                           \
            i_ty##_increment(i);                                                        \
        }                                                                               \
    }

#endif // CN_GEN_DSL_H
