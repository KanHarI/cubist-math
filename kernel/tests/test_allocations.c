/* This test redirects instruction realloc and normalization malloc/realloc.
 * Production allocators and all other test binaries are unchanged. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static bool fail_next;
static unsigned failures;

void *cc_test_realloc(void *pointer, size_t size) {
    if (fail_next) {
        fail_next = false;
        ++failures;
        return NULL;
    }
    return realloc(pointer, size);
}

static cc_entry_id make_entry(cc_kernel *k, bool level, cc_judgement_id type) {
    return level ? cc_instr_level(k) : cc_instr_extend(k, type);
}

/* An entry whose allocation fails is not made. Extend and Level allocate
 * only when one of the instruction store's arrays grows (the entries, the
 * context sets or their items), so entries are made until one does, and
 * that growth fails. */
static void entry_failure(bool level) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id unit = cc_instr_unit(k);
    assert(unit);
    size_t count;
    unsigned before = failures;
    cc_entry_id entry;
    fail_next = true;
    do {
        count = cc_kernel_entry_count(k);
        entry = make_entry(k, level, unit);
    } while (entry && fail_next);
    assert(failures == before + 1 && !fail_next);
    assert(!entry);
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(cc_kernel_entry_count(k) == count);
    cc_kernel_clear_error(k);
    entry = make_entry(k, level, unit);
    assert(entry);
    assert(cc_kernel_entry_count(k) == count + 1);
    /* The kernel keeps no names: every call makes a new entry. */
    cc_entry_id again = make_entry(k, level, unit);
    assert(again && again != entry && cc_kernel_entry_count(k) == count + 2);
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    cc_kernel_free(k);
}

/* A variable's index at the kernel's bound, UINT32_MAX, is a resource
 * error, and the refusal leaves the arena as it was. */
static void index_failure(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    assert(cc_instr_unit(k));
    size_t before, after, bytes;
    cc_kernel_arena(k, &before, &bytes);
    for (unsigned attempt = 0; attempt < 2; ++attempt) {
        assert(!cc_kernel_term(k, CC_BOUND, UINT32_MAX, 0, 0, 0, 0));
        assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
        assert(!strcmp(cc_kernel_error(k), "A variable's index exceeds the kernel's bound."));
        cc_kernel_arena(k, &after, &bytes);
        assert(after == before);
        cc_kernel_clear_error(k);
    }
    assert(cc_kernel_term(k, CC_BOUND, UINT32_MAX - 1, 0, 0, 0, 0));
    assert(cc_instr_point(k));
    cc_kernel_free(k);
}

static bool fail_normal_malloc, fail_normal_realloc;
static unsigned normal_allocations;

void *cc_test_normal_malloc(size_t size) {
    ++normal_allocations;
    if (fail_normal_malloc) {
        fail_normal_malloc = false;
        ++failures;
        return NULL;
    }
    return malloc(size);
}

void *cc_test_normal_realloc(void *pointer, size_t size) {
    ++normal_allocations;
    if (fail_normal_realloc) {
        fail_normal_realloc = false;
        ++failures;
        return NULL;
    }
    return realloc(pointer, size);
}

static void stack_allocation_recovery(cc_kernel *k, cc_term source, cc_term expected,
                                      cc_term (*query)(cc_kernel *, cc_term)) {
    unsigned before = failures;
    fail_normal_malloc = true;
    assert(!query(k, source));
    assert(failures == before + 1 && !fail_normal_malloc);
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(cc_kernel_error(k), "Normalization stack allocation failed."));
    cc_kernel_clear_error(k);
    /* Failing growth must also release the first successfully allocated
     * block, without publishing its unfinished ancestor as a normal form. */
    fail_normal_realloc = true;
    assert(!query(k, source));
    assert(failures == before + 2 && !fail_normal_realloc);
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(cc_kernel_error(k), "Normalization stack allocation failed."));
    cc_kernel_clear_error(k);
    unsigned allocated_before = normal_allocations;
    cc_kernel_set_step_budget(k, 200);
    assert(!query(k, source));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    assert(normal_allocations > allocated_before);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 1000000);
    assert(query(k, source) == expected);
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
}

static void normalization_stack_failure(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id unit = cc_instr_unit(k), type = unit;
    for (unsigned i = 0; i < 400; ++i) {
        type = cc_instr_sum(k, type, unit);
        assert(type);
    }
    cc_judgement_info source;
    assert(cc_kernel_judgement(k, type, &source));
    stack_allocation_recovery(k, source.term, source.term, cc_kernel_normalize);
    cc_kernel_free(k);
}

static void weak_tail_allocation_failure(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id value = cc_instr_point(k);
    cc_judgement_info source, point;
    assert(cc_kernel_judgement(k, value, &point));
    for (unsigned i = 0; i < 400; ++i) {
        value = cc_instr_define(k, value);
        assert(value);
    }
    assert(cc_kernel_judgement(k, value, &source));
    stack_allocation_recovery(k, source.term, point.term, cc_kernel_whnf);
    cc_kernel_free(k);
}

int main(void) {
    entry_failure(false);
    entry_failure(true);
    index_failure();
    normalization_stack_failure();
    weak_tail_allocation_failure();
    puts("allocation failure publication: ok");
    return 0;
}
