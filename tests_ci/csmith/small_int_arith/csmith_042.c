// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_042.c
#include "csmith.h"


static long __undefined;



static int32_t g_2 = 0x53D06CE1L;
static uint32_t g_3 = 0xD69F4288L;



static uint32_t  func_1(void);




static uint32_t  func_1(void)
{ 
    uint8_t l_4 = 0x83L;
    g_3 ^= (g_2 , (-1L));
    return l_4;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_2, "g_2", print_hash_value);
    transparent_crc(g_3, "g_3", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
