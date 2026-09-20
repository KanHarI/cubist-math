/* Interval rules: reversal exchanges meets/joins and exchanges each dimension
 * with its reversal. It does NOT impose i AND (1-i) = 0. */
#include "internal.h"

cc_status cc_reverse(cc_formula *out, const cc_formula *a) {
    if (out->sort != CC_INTERVAL || a->sort != CC_INTERVAL) return CC_BAD_INPUT;
    cc_formula candidate, sum; cc_init(&candidate, CC_INTERVAL); cc_init(&sum, CC_INTERVAL);
    cc_status status = cc_one(&candidate);
    for (size_t i = 0; i < a->length && status == CC_OK; ++i) {
        cc_zero(&sum);
        for (unsigned d = 0; d < CC_DIMENSIONS && status == CC_OK; ++d) {
            uint64_t bit = UINT64_C(1) << d;
            if (a->clauses[i].positive & bit) status = cc_insert(&sum, (cc_clause){0, bit});
            if (status == CC_OK && (a->clauses[i].negative & bit)) status = cc_insert(&sum, (cc_clause){bit, 0});
        }
        if (status == CC_OK) status = cc_meet(&candidate, &candidate, &sum);
    }
    if (status == CC_OK) cc_publish(out, &candidate);
    cc_clear(&candidate); cc_clear(&sum);
    return status;
}

cc_status cc_interval_substitute(cc_formula *out, const cc_formula *a,
                                 unsigned dimension, const cc_formula *value) {
    if (out->sort != CC_INTERVAL || a->sort != CC_INTERVAL || value->sort != CC_INTERVAL ||
        dimension >= CC_DIMENSIONS) return CC_BAD_INPUT;
    uint64_t bit = UINT64_C(1) << dimension;
    cc_formula candidate, reversed, product;
    cc_init(&candidate, CC_INTERVAL); cc_init(&reversed, CC_INTERVAL); cc_init(&product, CC_INTERVAL);
    cc_status status = cc_reverse(&reversed, value);
    for (size_t i = 0; i < a->length && status == CC_OK; ++i) {
        cc_zero(&product);
        cc_clause remainder = {a->clauses[i].positive & ~bit, a->clauses[i].negative & ~bit};
        status = cc_insert(&product, remainder);
        if (status == CC_OK && (a->clauses[i].positive & bit)) status = cc_meet(&product, &product, value);
        if (status == CC_OK && (a->clauses[i].negative & bit)) status = cc_meet(&product, &product, &reversed);
        if (status == CC_OK) status = cc_join(&candidate, &candidate, &product);
    }
    if (status == CC_OK) cc_publish(out, &candidate);
    cc_clear(&candidate); cc_clear(&reversed); cc_clear(&product);
    return status;
}
