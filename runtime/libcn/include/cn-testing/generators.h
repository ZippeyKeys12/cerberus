#ifndef CN_GENERATORS_H
#define CN_GENERATORS_H

#include <stdlib.h>

#include <cn-executable/utils.h>

cn_bits_u8* cn_gen_uniform_cn_bits_u8(cn_bits_i64* sz);
cn_bits_i8* cn_gen_uniform_cn_bits_i8(cn_bits_i64* sz);

cn_bits_u16* cn_gen_uniform_cn_bits_u16(cn_bits_i64* sz);
cn_bits_i16* cn_gen_uniform_cn_bits_i16(cn_bits_i64* sz);

cn_bits_u32* cn_gen_uniform_cn_bits_u32(cn_bits_i64* sz);
cn_bits_i32* cn_gen_uniform_cn_bits_i32(cn_bits_i64* sz);

cn_bits_u64* cn_gen_uniform_cn_bits_u64(cn_bits_i64* sz);
cn_bits_i64 cn_gen_uniform_cn_bits_i64(cn_bits_i64* sz);

cn_pointer* cn_gen_alloc(cn_bits_u64* bytes);

#endif // CN_GENERATORS_H
