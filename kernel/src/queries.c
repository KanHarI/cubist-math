/* Queries: computation on terms the instructions derived, and the arena's
 * size. A query certifies nothing; its answer is evidence only when an
 * instruction takes it, as Step does. */
#include "term_internal.h"

void cc_kernel_arena(const cc_kernel *k, size_t *nodes, size_t *bytes) {
    *nodes = k ? k->count - 1 : 0;
    *bytes = !k ? 0 : k->capacity * (sizeof(cc_node) + sizeof(cc_term)) +
                      k->definition_capacity * sizeof(cc_definition) +
                      (k->syntax_memo ? CC_SYNTAX_MEMO_SIZE * sizeof(cc_syntax_memo) : 0) +
                      (k->alpha_memo ? CC_ALPHA_MEMO_SIZE * sizeof(cc_alpha_memo) : 0) +
                      (k->alpha_scopes ? CC_ALPHA_MEMO_SIZE * sizeof(cc_alpha_scope) : 0) +
                      (k->interned ? k->intern_capacity * sizeof(cc_term) : 0);
}

cc_term cc_kernel_normalize(cc_kernel *k, cc_term term) {
    if (!k || !term || term >= k->count || k->error[0])
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    return ck_normal(k, term);
}

cc_term cc_kernel_whnf(cc_kernel *k, cc_term term) {
    if (!k || !term || term >= k->count || k->error[0])
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    k->recursion = 0;
    /* A head computed while a nested computation failed is no answer. */
    cc_term head = ck_whnf(k, term);
    return k->error[0] ? 0 : head;
}

/* A face formula with exactly one clause. */
cc_formula_id ck_clause_formula(cc_kernel *k, cc_clause clause) {
    cc_formula phi;
    cc_init(&phi, CC_FACE);
    if (cc_insert(&phi, clause) != CC_OK) {
        cc_clear(&phi);
        ck_fail(k, "Composition face allocation failed.");
        return 0;
    }
    cc_formula_id id = ck_formula(k, &phi);
    cc_clear(&phi);
    return id;
}
