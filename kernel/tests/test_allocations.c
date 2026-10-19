/* This test redirects instruction calloc and normalization malloc/realloc.
 * Production allocators and all other test binaries are unchanged. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static bool fail_next;
static unsigned failures;

void *cc_test_calloc(size_t count, size_t size) {
    if (fail_next) {
        fail_next = false;
        ++failures;
        return NULL;
    }
    return calloc(count, size);
}

static void entry_failure(bool level) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_judgement_id unit = cc_instr_unit(k);
    assert(unit);
    size_t count = cc_kernel_entry_count(k);
    unsigned before = failures;
    /* Unit initialized the derivation table. The next calloc in the
     * instruction store allocates the first context-entry index. */
    fail_next = true;
    cc_entry_id entry = level ? cc_instr_level(k, 100) : cc_instr_extend(k, unit, 100);
    assert(failures == before + 1 && !fail_next);
    assert(!entry);
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(cc_kernel_entry_count(k) == count);
    cc_kernel_clear_error(k);
    entry = level ? cc_instr_level(k, 100) : cc_instr_extend(k, unit, 100);
    assert(entry);
    assert(cc_kernel_entry_count(k) == count + 1);
    assert((level ? cc_instr_level(k, 100) : cc_instr_extend(k, unit, 100)) == entry);
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    cc_kernel_free(k);
}

static void symbol_failure(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    assert(cc_instr_unit(k));
    size_t before, after, bytes;
    cc_kernel_arena(k, &before, &bytes);
    for (unsigned attempt = 0; attempt < 2; ++attempt) {
        assert(!cc_kernel_term(k, CC_VAR, UINT32_MAX, 0, 0, 0, 0));
        assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
        cc_kernel_arena(k, &after, &bytes);
        assert(after == before);
        cc_kernel_clear_error(k);
    }
    assert(cc_kernel_fresh_symbol(k));
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
    unsigned before = failures;
    fail_normal_malloc = true;
    assert(!cc_kernel_normalize(k, source.term));
    assert(failures == before + 1 && !fail_normal_malloc);
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(cc_kernel_error(k), "Normalization stack allocation failed."));
    cc_kernel_clear_error(k);
    /* Failing growth must also release the first successfully allocated
     * block, without publishing its unfinished ancestor as a normal form. */
    fail_normal_realloc = true;
    assert(!cc_kernel_normalize(k, source.term));
    assert(failures == before + 2 && !fail_normal_realloc);
    assert(cc_kernel_error_kind(k) == CC_ERROR_RESOURCE);
    assert(!strcmp(cc_kernel_error(k), "Normalization stack allocation failed."));
    cc_kernel_clear_error(k);
    unsigned allocated_before = normal_allocations;
    cc_kernel_set_step_budget(k, 200);
    assert(!cc_kernel_normalize(k, source.term));
    assert(cc_kernel_error_kind(k) == CC_ERROR_BUDGET);
    assert(normal_allocations > allocated_before);
    cc_kernel_clear_error(k);
    cc_kernel_set_step_budget(k, 1000000);
    assert(cc_kernel_normalize(k, source.term) == source.term);
    assert(cc_kernel_error_kind(k) == CC_ERROR_NONE);
    cc_kernel_free(k);
}

int main(void) {
    entry_failure(false);
    entry_failure(true);
    symbol_failure();
    normalization_stack_failure();
    puts("allocation failure publication: ok");
    return 0;
}
