#include <cn-executable/utils.h>

cn_bits_u8 cn_gen_uniform_cn_bits_u8(cn_bits_i64* sz) {
    return (cn_bits_u8) { .val = (uint8_t*)sz->val };
}

cn_bits_i8 cn_gen_uniform_cn_bits_i8(cn_bits_i64* sz) {
    return (cn_bits_i8) { .val = (int8_t*)sz->val };
}


cn_bits_u16 cn_gen_uniform_cn_bits_u16(cn_bits_i64* sz) {
    return (cn_bits_u16) { .val = (uint16_t*)sz->val };
}


cn_bits_i16 cn_gen_uniform_cn_bits_i16(cn_bits_i64* sz) {
    return (cn_bits_i16) { .val = (int16_t*)sz->val };
}


cn_bits_u32 cn_gen_uniform_cn_bits_u32(cn_bits_i64* sz) {
    return (cn_bits_u32) { .val = (uint32_t*)sz->val };
}


cn_bits_i32 cn_gen_uniform_cn_bits_i32(cn_bits_i64* sz) {
    return (cn_bits_i32) { .val = (int32_t*)sz->val };
}


cn_bits_u64 cn_gen_uniform_cn_bits_u64(cn_bits_i64* sz) {
    return (cn_bits_u64) { .val = (uint64_t*)sz->val };
}


cn_bits_i64 cn_gen_uniform_cn_bits_i64(cn_bits_i64* sz) {
    return (cn_bits_i64) { .val = (int64_t*)sz->val };
}
