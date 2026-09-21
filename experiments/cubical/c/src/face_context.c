/* Restriction substitutes the same endpoint equations in every hypothesis. */
#include "term_internal.h"

cc_context *ck_restricted_context(cc_kernel *k, const cc_context *ctx,
                                       cc_clause clause, size_t *length) {
    *length = 0;
    for (const cc_context *entry = ctx; entry; entry = entry->previous)
        ++*length;
    if (!*length)
        return NULL;
    cc_context *copy = calloc(*length, sizeof *copy);
    if (!copy) {
        ck_fail(k, "Restricted context allocation failed.");
        return NULL;
    }
    size_t i = 0;
    for (const cc_context *entry = ctx; entry; entry = entry->previous, ++i) {
        copy[i].name = entry->name;
        copy[i].type = ck_restrict(k, entry->type, clause);
        copy[i].previous = i + 1 < *length ? &copy[i + 1] : NULL;
    }
    for (size_t j = *length; j-- > 0;)
        copy[j] = ck_extend(k, copy[j].name, copy[j].type, copy[j].previous);
    return copy;
}

cc_formula_id ck_clause_formula(cc_kernel *k, cc_clause clause) {
    cc_formula phi;
    cc_init(&phi, CC_FACE);
    if (cc_insert(&phi, clause) != CC_OK) {
        cc_clear(&phi);
        ck_fail(k, "Composition face allocation failed.");
        return 0;
    }
    cc_formula_id id = cc_kernel_formula(k, &phi);
    cc_clear(&phi);
    return id;
}

