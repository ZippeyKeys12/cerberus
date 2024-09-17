#include <string.h>

#include <cn-testing/backtrack.h>


static enum cn_gen_backtrack_request type = CN_GEN_BACKTRACK_NONE;

enum cn_gen_backtrack_request cn_gen_backtrack_type(void) {
    return type;
}

struct name_list {
    char* name;
    struct name_list* next;
};

static struct name_list* to_retry = NULL;
static size_t more_alloc_needed = 0;

void cn_gen_backtrack_reset(void) {
    type = CN_GEN_BACKTRACK_NONE;
    to_retry = NULL;
    more_alloc_needed = 0;
}

void cn_gen_backtrack_assert_failure(void) {
    type = CN_GEN_BACKTRACK_ASSERT;
}

void cn_gen_backtrack_relevant_add(char* varname) {
    struct name_list* new_node = (struct name_list*)malloc(sizeof(struct name_list));
    *new_node = (struct name_list){
        .name = varname, .next = 0
    };

    if (to_retry == NULL) {
        to_retry = new_node;
        return;
    }

    struct name_list* curr = to_retry;
    while (curr->next != NULL) {
        curr = curr->next;
    }

    curr->next = new_node;
}

int cn_gen_backtrack_relevant_contains(char* varname) {
    struct name_list* curr = to_retry;
    while (curr != NULL) {
        if (strcmp(varname, curr->name) == 0) {
            return 1;
        }

        curr = curr->next;
    }
    return 0;
}

void cn_gen_backtrack_alloc_set(size_t sz) {
    type = CN_GEN_BACKTRACK_ALLOC;

    more_alloc_needed = sz;
}

size_t cn_gen_backtrack_alloc_get() {
    return more_alloc_needed;
}
