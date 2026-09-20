/* Expose one beta/projection/boundary step, retaining its compact result.
 * Conversion tries structural comparison again before evaluating that result.
 * In particular, a path endpoint can name a huge numeral without computing it.
 */
#include "term_internal.h"

cc_term ck_expose(cc_kernel *k, cc_term term) {
    cc_node n = k->nodes[term];
    if (n.kind == CC_COMP) {
        for (cc_term cursor = n.child[1]; cursor;) {
            cc_node tube = k->nodes[cursor];
            const cc_formula *face = cc_kernel_get_formula(k, tube.payload);
            if (face && face->length == 1 && !face->clauses[0].positive && !face->clauses[0].negative)
                return ck_endpoint_term(k, tube.child[0], n.payload, 1);
            cursor = tube.child[1];
        }
    }
    if (n.kind == CC_PAPP) {
        const cc_formula *arg = cc_kernel_get_formula(k, n.payload);
        if (!arg || !n.child[1] || k->nodes[n.child[1]].kind != CC_PATH)
            return term;
        cc_node type = k->nodes[n.child[1]];
        if (!arg->length)
            return type.child[1];
        if (arg->length == 1 && !arg->clauses[0].positive && !arg->clauses[0].negative)
            return type.child[2];
    }
    if (n.kind == CC_APP) {
        cc_term fn = ck_whnf(k, n.child[0]);
        if (!fn)
            return 0;
        cc_node function = k->nodes[fn];
        if (function.kind == CC_LAM)
            return ck_substitute(k, function.child[1], function.payload, n.child[1]);
    }
    if (n.kind == CC_FST || n.kind == CC_SND) {
        cc_term pair = ck_whnf(k, n.child[0]);
        if (!pair)
            return 0;
        if (k->nodes[pair].kind == CC_PAIR)
            return k->nodes[pair].child[n.kind == CC_FST ? 1 : 2];
    }
    return term;
}
