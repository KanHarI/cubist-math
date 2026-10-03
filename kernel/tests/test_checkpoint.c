#include "term_internal.h"
#include <assert.h>
#include <stdio.h>

/* The term of a judgement. */
static cc_term term_of(cc_kernel *k, cc_judgement_id id) {
    cc_judgement_info info;
    assert(id && cc_kernel_judgement(k, id, &info));
    return info.term;
}

int main(void) {
    cc_kernel *k = cc_kernel_new();
    assert(k);
    cc_kernel_checkpoint(k);
    assert(cc_kernel_commit_checkpoint(k)); /* Empty arena is valid too. */
    /* old := tt : Unit, admitted by Define. */
    cc_term old = term_of(k, cc_instr_define(k, 1, cc_instr_point(k)));
    cc_kernel_checkpoint(k);
    for (unsigned i = 0; i < 1000; ++i)
        assert(cc_kernel_term(k, CC_VAR, 100 + i, 0, 0, 0, 0));
    /* ref := inl(old) : Unit + Unit, using the earlier definition. */
    cc_judgement_id unit = cc_instr_unit(k);
    cc_judgement_id sum = cc_instr_sum(k, unit, unit);
    cc_term ref = term_of(k, cc_instr_define(k, 2, cc_instr_inject(k, sum, cc_instr_lookup(k, old), false)));
    assert(ref && cc_kernel_whnf(k, ref));
    size_t allocated = k->count;
    assert(cc_kernel_commit_checkpoint(k));
    ref = cc_kernel_relocated(k, ref);
    assert(ref && k->count + 900 < allocated);
    /* Both definitions survive the commit: each is looked up again, at its type. */
    cc_judgement_info info;
    assert(cc_kernel_judgement(k, cc_instr_lookup(k, ref), &info) && k->nodes[info.type].kind == CC_SUM);
    assert(cc_kernel_judgement(k, cc_instr_lookup(k, old), &info) && k->nodes[info.type].kind == CC_UNIT);
    cc_kernel_checkpoint(k);
    cc_term rejected = term_of(k, cc_instr_define(k, 3, cc_instr_lookup(k, ref)));
    cc_kernel_rollback(k);
    assert(!cc_kernel_definition(k, rejected, NULL, NULL, NULL));
    assert(cc_instr_lookup(k, ref));
    cc_kernel_free(k);
    puts("Compaction preserves definitions; rollback discards new ones.");
}
