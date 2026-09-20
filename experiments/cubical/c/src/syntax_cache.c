/* Memoize pure operations on the immutable syntax DAG. These are not cached
 * typing judgements: no context or face assumption is elided. Keys include
 * the complete substitution, and collisions merely lose an optimization. */
#include "term_internal.h"

static size_t slot(uint32_t operation, cc_term term, uint32_t name, cc_term value) {
    uint64_t hash = term;
    hash = (hash ^ name) * UINT64_C(1099511628211);
    hash = (hash ^ value) * UINT64_C(1099511628211);
    hash = (hash ^ operation) * UINT64_C(1099511628211);
    return (size_t)(hash % CC_SYNTAX_MEMO_SIZE);
}

bool ck_memo_get(cc_kernel *k, uint32_t operation, cc_term term, uint32_t name,
                 cc_term value, uint64_t *result) {
    if (!k->syntax_memo)
        return false;
    cc_syntax_memo entry = k->syntax_memo[slot(operation, term, name, value)];
    if (entry.operation != operation || entry.term != term ||
        entry.name != name || entry.value != value)
        return false;
    *result = entry.result;
    return true;
}

void ck_memo_put(cc_kernel *k, uint32_t operation, cc_term term, uint32_t name,
                 cc_term value, uint64_t result) {
    if (k->error[0])
        return;
    if (!k->syntax_memo) {
        k->syntax_memo = calloc(CC_SYNTAX_MEMO_SIZE, sizeof *k->syntax_memo);
        if (!k->syntax_memo) {
            ck_fail(k, "Syntax memo allocation failed.");
            return;
        }
    }
    k->syntax_memo[slot(operation, term, name, value)] =
        (cc_syntax_memo){operation, term, name, value, result};
}
