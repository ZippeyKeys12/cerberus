#include "assert.h"

#include <cn-executable/utils.h>
#include <cn-testing/rand.h>
#include <cn-testing/uniform.h>

cn_bits_u8* cn_gen_uniform_cn_bits_u8(cn_bits_i64* sz) {
    cn_bits_u8* p = alloc(sizeof(cn_bits_u8));
    *p = (cn_bits_u8){ .val = (uint8_t)cn_gen_uniform_cn_bits_u64(sz)->val };
    return p;
}

cn_bits_i8* cn_gen_uniform_cn_bits_i8(cn_bits_i64* sz) {
    cn_bits_i8* p = alloc(sizeof(cn_bits_i8));
    *p = (cn_bits_i8){ .val = (int8_t)cn_gen_uniform_cn_bits_u64(sz)->val };
    return p;
}


cn_bits_u16* cn_gen_uniform_cn_bits_u16(cn_bits_i64* sz) {
    cn_bits_u16* p = alloc(sizeof(cn_bits_u16));
    *p = (cn_bits_u16){ .val = (uint16_t)cn_gen_uniform_cn_bits_u64(sz)->val };
    return p;
}


cn_bits_i16* cn_gen_uniform_cn_bits_i16(cn_bits_i64* sz) {
    cn_bits_i16* p = alloc(sizeof(cn_bits_i16));
    *p = (cn_bits_i16){ .val = (int16_t)cn_gen_uniform_cn_bits_u64(sz)->val };
    return p;
}


cn_bits_u32* cn_gen_uniform_cn_bits_u32(cn_bits_i64* sz) {
    cn_bits_u32* p = alloc(sizeof(cn_bits_u32));
    *p = (cn_bits_u32){ .val = (uint32_t)cn_gen_uniform_cn_bits_u64(sz)->val };
    return p;
}


cn_bits_i32* cn_gen_uniform_cn_bits_i32(cn_bits_i64* sz) {
    cn_bits_i32* p = alloc(sizeof(cn_bits_i32));
    *p = (cn_bits_i32){ .val = (int32_t)cn_gen_uniform_cn_bits_u64(sz)->val };
    return p;
}

cn_bits_u64* cn_gen_uniform_cn_bits_u64(cn_bits_i64* sz) {
    uint64_t val = cn_gen_rand();
    if (sz->val != -1) {
        assert(sz->val > 0);
        val %= sz->val;
    }
    // assert(sz->val == -1);

    cn_bits_u64* p = alloc(sizeof(cn_bits_u64));
    *p = (cn_bits_u64){ .val = val };
    return p;
}


cn_bits_i64* cn_gen_uniform_cn_bits_i64(cn_bits_i64* sz) {
    cn_bits_i64* p = alloc(sizeof(cn_bits_i64));
    *p = (cn_bits_i64){ .val = (int64_t)cn_gen_uniform_cn_bits_u64(sz)->val };
    return p;
}
