/* Only instructions.c in this test binary redirects calloc here. The
 * production allocator and all other test binaries are unchanged. */
#include "cubical_kernel.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

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

int main(void) {
    entry_failure(false);
    entry_failure(true);
    symbol_failure();
    puts("allocation failure publication: ok");
    return 0;
}
