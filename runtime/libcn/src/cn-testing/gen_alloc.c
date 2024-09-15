#include "stdlib.h"

#include <cn-executable/utils.h>

#include <cn-testing/alloc.h>

static hash_table* pointer_size_map = 0;

void cn_gen_alloc_reset(void) {
    pointer_size_map = ht_create();
}

cn_pointer* cn_gen_alloc(cn_bits_u64* sz) {
    void* p = alloc(*sz->val);
    ht_set(pointer_size_map, p, (void*)sz);
    return convert_to_cn_pointer(p);
}

cn_bits_u64* cn_gen_alloc_size(cn_pointer* p) {
    uint64_t value = (uint64_t)ht_get(pointer_size_map, p->ptr);
    return convert_to_cn_bits_u64(value);
}
