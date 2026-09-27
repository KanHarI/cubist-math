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

/* ---- Declared data sorts (H1 family F4, specification 3.3) ---------------
 * A constructor's arguments form a telescope, data then positions, which is
 * composed as nested Σ types Σ (x_1 : A_1). … Σ (x_n : A_n). Unit: the Σ rule
 * fills each component before substituting it into the next, and a
 * position's Π type composes by the Π rule, into the sort again. */

bool ck_constructor_application(cc_kernel *k, cc_term term, uint32_t *constructor, cc_term *arguments,
                                uint32_t *count) {
    cc_term reversed[CC_CONSTRUCTOR_ARGUMENTS];
    uint32_t n = 0;
    cc_term head = term;
    while (k->nodes[head].kind == CC_APP) {
        if (n == CC_CONSTRUCTOR_ARGUMENTS)
            return false;
        reversed[n++] = k->nodes[head].child[1];
        head = k->nodes[head].child[0];
    }
    if (k->nodes[head].kind != CC_CON)
        return false;
    *constructor = k->nodes[head].payload;
    for (uint32_t i = 0; i < n; ++i)
        arguments[i] = reversed[n - 1 - i];
    *count = n;
    return true;
}

cc_term ck_telescope(cc_kernel *k, cc_term type, uint32_t count) {
    if (!count)
        return ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    cc_node pi = k->nodes[type];
    if (pi.kind != CC_PI)
        return ck_fail(k, "A constructor's type has fewer arguments than its application."), 0;
    cc_term rest = ck_telescope(k, pi.child[1], count - 1);
    return rest ? ck_make(k, CC_SIGMA, pi.payload, pi.child[0], rest, 0, 0) : 0;
}

cc_term ck_tuple(cc_kernel *k, cc_term telescope, const cc_term *arguments, uint32_t count) {
    if (!count)
        return ck_make(k, CC_POINT, 0, 0, 0, 0, 0);
    cc_node sigma = k->nodes[telescope];
    cc_term rest = ck_tuple(k, ck_substitute(k, sigma.child[1], sigma.payload, arguments[0]), arguments + 1, count - 1);
    return rest ? ck_make(k, CC_PAIR, 0, telescope, arguments[0], rest, 0) : 0;
}

/* Con(c; I) applied to the components of a tuple. */
cc_term ck_apply_components(cc_kernel *k, cc_term instance, uint32_t constructor, cc_term tuple, uint32_t count) {
    cc_term result = ck_make(k, CC_CON, constructor, instance, 0, 0, 0);
    for (uint32_t m = 0; m < count && result; ++m) {
        result = ck_make(k, CC_APP, 0, result, ck_make(k, CC_FST, 0, tuple, 0, 0, 0), 0, 0);
        tuple = ck_make(k, CC_SND, 0, tuple, 0, 0, 0);
    }
    return result;
}

/* comp^i S(as(i)) [φ ↦ u] u_0 at a data sort: when u_0 and every tube are the
 * same constructor, that constructor at as(1) of the composed arguments;
 * otherwise neutral. A neutral tube is never taken for a constructor. */
static cc_term data_sort_composition(cc_kernel *k, cc_term term, cc_term family, cc_term system) {
    cc_node composition = k->nodes[term];
    unsigned direction = composition.payload;
    cc_term head = ck_whnf(k, composition.child[2]);
    if (!head)
        return 0;
    uint32_t constructor = 0, count = 0;
    cc_term arguments[CC_CONSTRUCTOR_ARGUMENTS];
    if (!ck_constructor_application(k, head, &constructor, arguments, &count))
        return term;
    cc_term type = ck_constructor_type(k, family, constructor);
    cc_term telescope = type ? ck_telescope(k, type, count) : 0;
    if (!telescope)
        return 0;
    cc_term tubes = 0;
    for (cc_term cursor = system; cursor; cursor = k->nodes[cursor].child[1]) {
        cc_node tube = k->nodes[cursor];
        cc_term value = ck_whnf(k, tube.child[0]);
        uint32_t own = 0, own_count = 0;
        cc_term own_arguments[CC_CONSTRUCTOR_ARGUMENTS];
        if (!value)
            return 0;
        if (!ck_constructor_application(k, value, &own, own_arguments, &own_count) || own != constructor ||
            own_count != count)
            return term;
        tubes = ck_append_tube(k, tubes, tube.payload, ck_tuple(k, telescope, own_arguments, count));
    }
    cc_term start = ck_tuple(k, ck_endpoint_term(k, telescope, direction, 0), arguments, count);
    cc_term composed = ck_make(k, CC_COMP, direction, telescope, tubes, start, 0);
    return ck_apply_components(k, ck_endpoint_term(k, family, direction, 1), constructor, composed, count);
}

cc_term ck_sort_composition(cc_kernel *k, cc_term term, cc_term family, cc_term system) {
    const cc_signature *s = ck_instance_signature(k, family);
    if (!s)
        return 0;
    if (ck_signature_higher(s)) {
        cc_node n = k->nodes[term];
        return ck_whnf(k, ck_pushout_composition(k, n.payload, family, system, n.child[2]));
    }
    return data_sort_composition(k, term, family, system);
}
