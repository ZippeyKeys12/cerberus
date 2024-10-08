#ifndef CN_UNIFORM_H
#define CN_UNIFORM_H

#include <stdlib.h>

#include <cn-executable/utils.h>

cn_bits_u8* cn_gen_uniform_cn_bits_u8(uint64_t sz);
cn_bits_i8* cn_gen_uniform_cn_bits_i8(uint64_t sz);

cn_bits_u16* cn_gen_uniform_cn_bits_u16(uint64_t sz);
cn_bits_i16* cn_gen_uniform_cn_bits_i16(uint64_t sz);

cn_bits_u32* cn_gen_uniform_cn_bits_u32(uint64_t sz);
cn_bits_i32* cn_gen_uniform_cn_bits_i32(uint64_t sz);

cn_bits_u64* cn_gen_uniform_cn_bits_u64(uint64_t sz);
cn_bits_i64* cn_gen_uniform_cn_bits_i64(uint64_t sz);

cn_bits_u8* cn_gen_range_cn_bits_u8(cn_bits_u8* min, cn_bits_u8* max);
cn_bits_i8* cn_gen_range_cn_bits_i8(cn_bits_i8* min, cn_bits_i8* max);

cn_bits_u16* cn_gen_range_cn_bits_u16(cn_bits_u16* min, cn_bits_u16* max);
cn_bits_i16* cn_gen_range_cn_bits_i16(cn_bits_i16* min, cn_bits_i16* max);

cn_bits_u32* cn_gen_range_cn_bits_u32(cn_bits_u32* min, cn_bits_u32* max);
cn_bits_i32* cn_gen_range_cn_bits_i32(cn_bits_i32* min, cn_bits_i32* max);

cn_bits_u64* cn_gen_range_cn_bits_u64(cn_bits_u64* min, cn_bits_u64* max);
cn_bits_i64* cn_gen_range_cn_bits_i64(cn_bits_i64* min, cn_bits_i64* max);

#endif // CN_UNIFORM_H
