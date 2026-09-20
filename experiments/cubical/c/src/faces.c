/* Face rules. For a disjunction r of interval monomials:
 *   r=1: at least one monomial has every factor equal to 1;
 *   r=0: every monomial has at least one factor equal to 0.
 * The endpoint equations i=0 and i=1 are disjoint but not exhaustive. */
#include "internal.h"

cc_status cc_endpoint(cc_formula *out, const cc_formula *r, unsigned endpoint) {
    if (out->sort != CC_FACE || r->sort != CC_INTERVAL || endpoint > 1)
        return CC_BAD_INPUT;
    cc_formula candidate, sum;
    cc_init(&candidate, CC_FACE);
    cc_init(&sum, CC_FACE);
    cc_status status = endpoint ? CC_OK : cc_one(&candidate);
    for (size_t i = 0; i < r->length && status == CC_OK; ++i) {
        if (endpoint) {
            status = cc_insert(&candidate, r->clauses[i]);
            continue;
        }
        cc_zero(&sum);
        for (unsigned d = 0; d < CC_DIMENSIONS && status == CC_OK; ++d) {
            uint64_t bit = UINT64_C(1) << d;
            if (r->clauses[i].positive & bit)
                status = cc_insert(&sum, (cc_clause){0, bit});
            if (status == CC_OK && (r->clauses[i].negative & bit))
                status = cc_insert(&sum, (cc_clause){bit, 0});
        }
        if (status == CC_OK)
            status = cc_meet(&candidate, &candidate, &sum);
    }
    if (status == CC_OK)
        cc_publish(out, &candidate);
    cc_clear(&candidate);
    cc_clear(&sum);
    return status;
}

cc_status cc_face_substitute(cc_formula *out, const cc_formula *a,
                             unsigned dimension, const cc_formula *value) {
    if (out->sort != CC_FACE || a->sort != CC_FACE || value->sort != CC_INTERVAL ||
        dimension >= CC_DIMENSIONS) return CC_BAD_INPUT;
    uint64_t bit = UINT64_C(1) << dimension;
    cc_formula candidate, at_zero, at_one, product;
    cc_init(&candidate, CC_FACE);
    cc_init(&at_zero, CC_FACE);
    cc_init(&at_one, CC_FACE);
    cc_init(&product, CC_FACE);
    cc_status status = cc_endpoint(&at_zero, value, 0);
    if (status == CC_OK)
        status = cc_endpoint(&at_one, value, 1);
    for (size_t i = 0; i < a->length && status == CC_OK; ++i) {
        cc_zero(&product);
        cc_clause remainder = {a->clauses[i].positive & ~bit, a->clauses[i].negative & ~bit};
        status = cc_insert(&product, remainder);
        if (status == CC_OK && (a->clauses[i].positive & bit))
            status = cc_meet(&product, &product, &at_one);
        if (status == CC_OK && (a->clauses[i].negative & bit))
            status = cc_meet(&product, &product, &at_zero);
        if (status == CC_OK)
            status = cc_join(&candidate, &candidate, &product);
    }
    if (status == CC_OK)
        cc_publish(out, &candidate);
    cc_clear(&candidate);
    cc_clear(&at_zero);
    cc_clear(&at_one);
    cc_clear(&product);
    return status;
}

cc_status cc_face_entails(const cc_formula *phi, const cc_formula *psi, bool *result) {
    if (phi->sort != CC_FACE || psi->sort != CC_FACE || !result)
        return CC_BAD_INPUT;
    /* A meet implies a disjunction of meets exactly when it contains one of
     * those meets. Checking each clause establishes implication of the DNFs. */
    for (size_t i = 0; i < phi->length; ++i) {
        bool found = false;
        for (size_t j = 0; j < psi->length; ++j)
            if (cc_clause_subset(psi->clauses[j], phi->clauses[i])) {
                found = true;
                break;
            }
        if (!found) {
            *result = false;
            return CC_OK;
        }
    }
    *result = true;
    return CC_OK;
}
