/* Queries: computation on terms the instructions derived, and the arena's
 * size. A query certifies nothing; its answer is evidence only when an
 * instruction takes it, as Step does. */
#include "term_internal.h"

void cc_kernel_arena(const cc_kernel *k, size_t *nodes, size_t *bytes) {
    *nodes = k ? k->count - 1 : 0;
    *bytes = !k ? 0 : k->capacity * (sizeof(cc_node) + 2 * sizeof(cc_term)) +
                      k->definition_capacity * sizeof(cc_definition) +
                      (k->syntax_memo ? CC_SYNTAX_MEMO_SIZE * sizeof(cc_syntax_memo) : 0) +
                      (k->alpha_memo ? CC_ALPHA_MEMO_SIZE * sizeof(cc_alpha_memo) : 0) +
                      (k->alpha_scopes ? CC_ALPHA_MEMO_SIZE * sizeof(cc_alpha_scope) : 0) +
                      (k->interned ? k->intern_capacity * sizeof(cc_term) : 0) +
                      (k->folded_cache ? k->capacity * sizeof(cc_term) : 0);
}

/* No query's answer holds a variable an operation opened: an O(1) check of
 * its `opened` against the query's term (section 3.1). */
static cc_term answer(cc_kernel *k, cc_term term, cc_term result) {
    if (!result || k->error[0])
        return 0;
    if (k->nodes[result].opened > k->nodes[term].opened)
        return ck_fail(k, "A result would hold a variable an operation opened."), 0;
    return result;
}

/* A term with loose indices is refused by normalization itself (normal). */
cc_term cc_kernel_normalize(cc_kernel *k, cc_term term) {
    if (!k || !term || term >= k->count || k->error[0])
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    k->recursion = 0;
    return answer(k, term, ck_normal(k, term));
}

cc_term cc_kernel_normalize_folded(cc_kernel *k, cc_term term) {
    if (!k || !term || term >= k->count || k->error[0])
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    k->recursion = 0;
    return answer(k, term, ck_normal_folded(k, term));
}

/* A term read under binders has loose indices: they are opened with
 * CC_OPENED levels above every level the term holds, its head computed, and
 * the head closed back over the same indices (section 5.1). Nothing reads an
 * entry's type, so a head is the same in every context that binds the
 * term's variables. */
cc_term cc_kernel_whnf(cc_kernel *k, cc_term term) {
    if (!k || !term || term >= k->count || k->error[0])
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    k->recursion = 0;
    uint32_t loose = k->nodes[term].loose, first = k->nodes[term].opened;
    cc_term opened = loose ? ck_open_loose(k, term, first) : term;
    /* A head computed while a nested computation failed is no answer. */
    cc_term head = opened ? ck_whnf(k, opened) : 0;
    if (head && loose)
        head = ck_close_loose(k, head, first, loose);
    return answer(k, term, head);
}

/* The driver's opening of a binder's body with an entry, one binder at a
 * time (section 3.6): refused when the body already mentions the entry,
 * which would make the binder's variable and the entry one. */
cc_term cc_kernel_instantiate(cc_kernel *k, cc_term body, cc_entry_id entry) {
    if (!k || !body || body >= k->count || k->error[0])
        return 0;
    ck_operation(k, CC_WORK_QUERY);
    k->recursion = 0;
    cc_term variable = ck_make(k, CC_CONTEXT, entry, 0, 0, 0, 0);
    if (!variable)
        return 0;
    if (ck_mentions(k, body, entry))
        return ck_fail(k, "A binder's body already mentions the entry it would be opened with."), 0;
    return k->error[0] ? 0 : answer(k, body, ck_instantiate(k, body, variable));
}

/* A face formula with exactly one clause. */
cc_formula_id ck_clause_formula(cc_kernel *k, cc_clause clause) {
    cc_formula phi;
    cc_init(&phi, CC_FACE);
    if (!ck_formula_result(k, cc_insert(&phi, clause), "Composition face allocation failed.")) {
        cc_clear(&phi);
        return 0;
    }
    cc_formula_id id = ck_formula(k, &phi);
    cc_clear(&phi);
    return id;
}

bool cc_kernel_alpha_equal(cc_kernel *k, cc_term left, cc_term right, bool *out) {
    if (!k || !left || !right || left >= k->count || right >= k->count || !out || k->error[0])
        return false;
    ck_operation(k, CC_WORK_QUERY);
    k->recursion = 0;
    bool equal = ck_alpha_equal(k, left, right);
    if (k->error[0]) return false;
    *out = equal;
    return true;
}
