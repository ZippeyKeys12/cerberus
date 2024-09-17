#include "stdlib.h"

#include <cn-executable/utils.h>

#include <cn-testing/alloc.h>
#include <cn-testing/backtrack.h>

static hash_table* pointer_size_map = 0;

void cn_gen_alloc_reset(void) {
    pointer_size_map = ht_create();
}

cn_pointer* cn_gen_alloc(cn_bits_u64* sz) {
    uint64_t bytes = convert_from_cn_bits_u64(sz);
    if (cn_gen_backtrack_type() == CN_GEN_BACKTRACK_ALLOC) {
        bytes = cn_gen_backtrack_alloc_get();
    }
    void* p = alloc(bytes);
    ht_set(pointer_size_map, p, (void*)(bytes + 1));
    return convert_to_cn_pointer(p);
}

cn_bits_u64* cn_gen_alloc_size(cn_pointer* p) {
    uint64_t value = (uint64_t)ht_get(pointer_size_map, convert_from_cn_pointer(p));
    return convert_to_cn_bits_u64(value - 1);
}
