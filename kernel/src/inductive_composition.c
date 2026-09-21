/* Constructor computation for sums and W trees.
 * A compatible constructor system composes its arguments. For a W tree, first
 * fill the label in A, then compose the children over B(label). This is the
 * same dependent argument transport used by Sigma/Pi composition. A neutral
 * wall stays neutral; its constructor is never guessed from the starting lid.
 */
#include "term_internal.h"

static bool same_constructors(cc_kernel *k, cc_term system, cc_term_kind kind) {
    for (cc_term cursor = system; cursor;) {
        cc_node tube = k->nodes[cursor];
        cc_term head = ck_whnf(k, tube.child[0]);
        if (!head || k->nodes[head].kind != kind)
            return false;
        cursor = tube.child[1];
    }
    return true;
}

static cc_term arguments(cc_kernel *k, cc_term system, unsigned slot) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    cc_term head = ck_whnf(k, tube.child[0]);
    if (!head)
        return 0;
    cc_term value = k->nodes[head].child[slot];
    cc_term tail = arguments(k, tube.child[1], slot);
    return ck_make(k, CC_TUBE, tube.payload, value, tail, 0, 0);
}

cc_term ck_inductive_composition(cc_kernel *k, cc_term term, cc_term family, cc_term system) {
    cc_node composition = k->nodes[term];
    cc_node type = k->nodes[family];
    unsigned direction = composition.payload;
    cc_term head = ck_whnf(k, composition.child[2]);
    if (!head)
        return 0;
    cc_node base = k->nodes[head];
    if (type.kind == CC_SUM && (base.kind == CC_INL || base.kind == CC_INR) &&
        same_constructors(k, system, base.kind)) {
        unsigned side = base.kind == CC_INL ? 0 : 1;
        cc_term tubes = arguments(k, system, 1);
        cc_term value = ck_make(k, CC_COMP, direction, type.child[side], tubes, base.child[1], 0);
        cc_term target = ck_endpoint_term(k, family, direction, 1);
        return ck_make(k, base.kind, 0, target, value, 0, 0);
    }
    if (type.kind == CC_W && base.kind == CC_SUP && same_constructors(k, system, CC_SUP)) {
        cc_term labels = arguments(k, system, 1);
        cc_formula along;
        cc_init(&along, CC_INTERVAL);
        if (cc_generator(&along, direction, true) != CC_OK)
            return ck_fail(k, "W composition direction allocation failed."), 0;
        cc_term label_line = ck_fill(k, direction, type.child[0], labels, base.child[1], &along);
        cc_clear(&along);
        cc_term label = ck_make(k, CC_COMP, direction, type.child[0], labels, base.child[1], 0);
        cc_term arity = ck_substitute(k, type.child[1], type.payload, label_line);
        uint32_t child_name = ck_fresh_symbol(k);
        cc_term child_family = ck_make(k, CC_PI, child_name, arity, family, 0, 0);
        cc_term children = ck_make(k, CC_COMP, direction, child_family,
                                  arguments(k, system, 2), base.child[2], 0);
        cc_term target = ck_endpoint_term(k, family, direction, 1);
        return ck_make(k, CC_SUP, 0, target, label, children, 0);
    }
    return term;
}
