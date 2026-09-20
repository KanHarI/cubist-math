/* Point and bridge computation for the dependent pushout eliminator.
 * Each result is ordinary syntax. Checked input supplies the bridge's Path
 * annotation; computation introduces no axiom or unchecked witness. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

cc_term ck_pushout_reduce(cc_kernel *k, cc_term term) {
    cc_node n = k->nodes[term];
    if (n.kind == CC_PUSH_PATH) {
        const cc_formula *r = cc_kernel_get_formula(k, n.payload);
        if (!r || r->sort != CC_INTERVAL)
            return ck_fail(k, "Unchecked pushout bridge reached reduction."), 0;
        bool zero = r->length == 0;
        bool one = r->length == 1 && !r->clauses[0].positive && !r->clauses[0].negative;
        if (!zero && !one)
            return term;
        cc_term P = ck_whnf(k, n.child[0]);
        if (!P || k->nodes[P].kind != CC_PUSHOUT)
            return ck_fail(k, "Pushout bridge has no checked span."), 0;
        cc_term map = ck_make(k, zero ? CC_FST : CC_SND, 0, k->nodes[P].child[3], 0, 0, 0);
        return ck_make(k, zero ? CC_PUSH_LEFT : CC_PUSH_RIGHT, 0,
                       n.child[0], app(k, map, n.child[1]), 0, 0);
    }
    cc_node e = k->nodes[n.child[0]];
    cc_term value = ck_whnf(k, n.child[1]);
    if (!value)
        return 0;
    cc_node z = k->nodes[value];
    if (z.kind == CC_PUSH_LEFT || z.kind == CC_PUSH_RIGHT)
        return ck_whnf(k, app(k, e.child[z.kind == CC_PUSH_LEFT ? 1 : 2], z.child[1]));
    if (z.kind == CC_PUSH_PATH) {
        cc_term path = ck_pushout_bridge_type(k, z.child[0], e.child[0], e.child[1], e.child[2], z.child[1]);
        cc_term at = ck_make(k, CC_PAPP, z.payload, app(k, e.child[3], z.child[1]), path, 0, 0);
        return ck_whnf(k, at);
    }
    return term;
}
