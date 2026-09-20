/* Capture-avoiding substitution. Term variables and dimensions are separate
 * namespaces; a Path binds its dimension in the family, not in its endpoints.
 * A composition binds its direction in the family and tube terms, but not in
 * the face formulas or starting lid. These distinctions are trusted rules. */
#include "term_internal.h"

bool ck_term_binder(cc_term_kind kind) {
    return kind == CC_PI || kind == CC_LAM || kind == CC_SIGMA || kind == CC_W;
}

bool ck_dim_binder(cc_term_kind kind) {
    return kind == CC_PATH || kind == CC_PLAM || kind == CC_COMP;
}

static bool term_free(cc_kernel *k, cc_term term, uint32_t name) {
    if (!term || !ck_tick(k, false))
        return false;
    cc_node n = k->nodes[term];
    if (n.kind == CC_VAR)
        return n.payload == name;
    for (unsigned i = 0; i < ck_arity(n.kind); ++i) {
        if (i == 1 && ck_term_binder(n.kind) && n.payload == name)
            continue;
        if (ck_term_free(k, n.child[i], name))
            return true;
    }
    return false;
}

bool ck_term_free(cc_kernel *k, cc_term term, uint32_t name) {
    uint64_t result;
    if (ck_memo_get(k, 1, term, name, 0, &result))
        return result != 0;
    bool free = term_free(k, term, name);
    ck_memo_put(k, 1, term, name, 0, free);
    return free;
}

static uint64_t formula_names(const cc_formula *f) {
    uint64_t names = 0;
    if (f)
        for (size_t i = 0; i < f->length; ++i)
            names |= f->clauses[i].positive | f->clauses[i].negative;
    return names;
}

static uint64_t free_dims(cc_kernel *k, cc_term term) {
    if (!term || !ck_tick(k, false))
        return 0;
    cc_node n = k->nodes[term];
    uint64_t result = 0;
    if (n.kind == CC_PAPP || n.kind == CC_PUSH_PATH || n.kind == CC_TUBE || n.kind == CC_GLUE_SYSTEM)
        result = formula_names(cc_kernel_get_formula(k, n.payload));
    for (unsigned i = 0; i < ck_arity(n.kind); ++i) {
        uint64_t names = ck_free_dims(k, n.child[i]);
        if (ck_dim_binder(n.kind) && (i == 0 || (i == 1 && n.kind != CC_PATH)) && n.payload < CC_DIMENSIONS)
            names &= ~(UINT64_C(1) << n.payload);
        result |= names;
    }
    return result;
}

uint64_t ck_free_dims(cc_kernel *k, cc_term term) {
    uint64_t result;
    if (ck_memo_get(k, 2, term, 0, 0, &result))
        return result;
    result = free_dims(k, term);
    ck_memo_put(k, 2, term, 0, 0, result);
    return result;
}

unsigned ck_fresh_dimension(cc_kernel *k, uint64_t avoid) {
    for (unsigned d = 0; d < CC_DIMENSIONS; ++d)
        if (!(avoid & (UINT64_C(1) << d)))
            return d;
    ck_fail(k, "Native prototype has exhausted its 64 dimension names.");
    return CC_DIMENSIONS;
}

static cc_term tube_substitute(cc_kernel *, cc_term, unsigned,
                                const cc_formula *, bool, bool);

static cc_term substitute(cc_kernel *k, cc_term term, uint32_t name, cc_term value) {
    if (!term)
        return 0;
    if (!ck_tick(k, false))
        return 0;
    if (!ck_term_free(k, term, name))
        return term;
    cc_node n = k->nodes[term];
    if (n.kind == CC_VAR && n.payload == name)
        return value;
    /* Substituting a TERM can capture free DIMENSIONS in that term too.
     * A lambda returning <i> x must rename i before x := p(i). */
    if (ck_dim_binder(n.kind) && n.payload < CC_DIMENSIONS &&
        (ck_free_dims(k, value) & (UINT64_C(1) << n.payload))) {
        uint64_t avoid = ck_free_dims(k, term) | ck_free_dims(k, value) |
                         (UINT64_C(1) << n.payload);
        unsigned fresh = ck_fresh_dimension(k, avoid);
        cc_formula variable;
        cc_init(&variable, CC_INTERVAL);
        if (cc_generator(&variable, fresh, true) != CC_OK) {
            cc_clear(&variable);
            return ck_fail(k, "Term substitution dimension allocation failed."), 0;
        }
        n.child[0] = ck_dimension_substitute(k, n.child[0], n.payload, &variable);
        if (n.kind == CC_PLAM)
            n.child[1] = ck_dimension_substitute(k, n.child[1], n.payload, &variable);
        if (n.kind == CC_COMP)
            n.child[1] = tube_substitute(k, n.child[1], n.payload, &variable, true, false);
        n.payload = fresh;
        cc_clear(&variable);
    }
    if (ck_term_binder(n.kind) && n.payload != name && ck_term_free(k, value, n.payload)) {
        uint32_t fresh = ck_fresh_symbol(k);
        n.child[1] = ck_substitute(k, n.child[1], n.payload, ck_var(k, fresh));
        n.payload = fresh;
    }
    for (unsigned i = 0; i < ck_arity(n.kind); ++i) {
        if (i == 1 && ck_term_binder(n.kind) && n.payload == name)
            continue;
        n.child[i] = ck_substitute(k, n.child[i], name, value);
    }
    cc_node original = k->nodes[term];
    if (n.payload == original.payload && !memcmp(n.child, original.child, sizeof n.child))
        return term;
    return ck_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], n.child[3]);
}

cc_term ck_substitute(cc_kernel *k, cc_term term, uint32_t name, cc_term value) {
    uint64_t result;
    if (ck_memo_get(k, 3, term, name, value, &result))
        return (cc_term)result;
    cc_term changed = substitute(k, term, name, value);
    if (changed)
        ck_memo_put(k, 3, term, name, value, changed);
    return changed;
}

static cc_term tube_substitute(cc_kernel *k, cc_term term, unsigned dim,
                               const cc_formula *value, bool bodies, bool faces) {
    if (!term)
        return 0;
    if (!ck_tick(k, false))
        return 0;
    cc_node n = k->nodes[term];
    if (n.kind != CC_TUBE)
        return ck_fail(k, "Malformed composition tube list."), 0;
    if (bodies)
        n.child[0] = ck_dimension_substitute(k, n.child[0], dim, value);
    if (faces) {
        const cc_formula *phi = cc_kernel_get_formula(k, n.payload);
        cc_formula changed;
        cc_init(&changed, CC_FACE);
        if (!phi || cc_face_substitute(&changed, phi, dim, value) != CC_OK) {
            cc_clear(&changed);
            return ck_fail(k, "Invalid face substitution."), 0;
        }
        n.payload = cc_kernel_formula(k, &changed);
        cc_clear(&changed);
    }
    n.child[1] = tube_substitute(k, n.child[1], dim, value, bodies, faces);
    return ck_make(k, CC_TUBE, n.payload, n.child[0], n.child[1], 0, 0);
}

cc_term ck_dimension_substitute(cc_kernel *k, cc_term term, unsigned dim,
                                const cc_formula *value) {
    if (!term)
        return 0;
    if (!ck_tick(k, false))
        return 0;
    if (dim >= CC_DIMENSIONS || !value || value->sort != CC_INTERVAL)
        return ck_fail(k, "Invalid dimension substitution."), 0;
    if (!(ck_free_dims(k, term) & (UINT64_C(1) << dim)))
        return term;
    cc_node n = k->nodes[term];
    if (ck_dim_binder(n.kind) && n.payload >= CC_DIMENSIONS)
        return ck_fail(k, "Dimension binder outside native range."), 0;
    if (ck_dim_binder(n.kind) && n.payload != dim &&
        (formula_names(value) & (UINT64_C(1) << n.payload))) {
        unsigned fresh = ck_fresh_dimension(k, ck_free_dims(k, term) | formula_names(value) |
                                           (UINT64_C(1) << dim) | (UINT64_C(1) << n.payload));
        cc_formula variable;
        cc_init(&variable, CC_INTERVAL);
        if (cc_generator(&variable, fresh, true) != CC_OK)
            return ck_fail(k, "Fresh dimension allocation failed."), 0;
        n.child[0] = ck_dimension_substitute(k, n.child[0], n.payload, &variable);
        if (n.kind == CC_PLAM)
            n.child[1] = ck_dimension_substitute(k, n.child[1], n.payload, &variable);
        if (n.kind == CC_COMP)
            n.child[1] = tube_substitute(k, n.child[1], n.payload, &variable, true, false);
        n.payload = fresh;
        cc_clear(&variable);
    }
    if (n.kind == CC_TUBE)
        return tube_substitute(k, term, dim, value, true, true);
    for (unsigned i = 0; i < ck_arity(n.kind); ++i) {
        if (n.kind == CC_COMP && i == 1) {
            n.child[i] = tube_substitute(k, n.child[i], dim, value, n.payload != dim, true);
            continue;
        }
        bool bound = ck_dim_binder(n.kind) && (i == 0 || (n.kind == CC_PLAM && i == 1));
        if (!(bound && n.payload == dim))
            n.child[i] = ck_dimension_substitute(k, n.child[i], dim, value);
    }
    if (n.kind == CC_GLUE_SYSTEM) {
        const cc_formula *face = cc_kernel_get_formula(k, n.payload);
        cc_formula changed;
        cc_init(&changed, CC_FACE);
        if (!face || cc_face_substitute(&changed, face, dim, value) != CC_OK) {
            cc_clear(&changed);
            return ck_fail(k, "Invalid Glue face substitution."), 0;
        }
        n.payload = cc_kernel_formula(k, &changed);
        cc_clear(&changed);
    }
    if (n.kind == CC_PAPP || n.kind == CC_PUSH_PATH) {
        const cc_formula *arg = cc_kernel_get_formula(k, n.payload);
        cc_formula changed;
        cc_init(&changed, CC_INTERVAL);
        if (!arg || cc_interval_substitute(&changed, arg, dim, value) != CC_OK) {
            cc_clear(&changed);
            return ck_fail(k, "Invalid interval substitution."), 0;
        }
        n.payload = cc_kernel_formula(k, &changed);
        cc_clear(&changed);
    }
    cc_node original = k->nodes[term];
    if (n.payload == original.payload && !memcmp(n.child, original.child, sizeof n.child))
        return term;
    return ck_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], n.child[3]);
}

cc_term ck_endpoint_term(cc_kernel *k, cc_term term, unsigned dim, unsigned endpoint) {
    cc_formula value;
    cc_init(&value, CC_INTERVAL);
    if (endpoint && cc_one(&value) != CC_OK) {
        cc_clear(&value);
        return ck_fail(k, "Endpoint allocation failed."), 0;
    }
    cc_term result = ck_dimension_substitute(k, term, dim, &value);
    cc_clear(&value);
    return result;
}

cc_term ck_restrict(cc_kernel *k, cc_term term, cc_clause face) {
    for (unsigned dim = 0; dim < CC_DIMENSIONS; ++dim) {
        uint64_t bit = UINT64_C(1) << dim;
        if (face.positive & bit)
            term = ck_endpoint_term(k, term, dim, 1);
        if (face.negative & bit)
            term = ck_endpoint_term(k, term, dim, 0);
    }
    return term;
}

cc_formula_id ck_interval_variable(cc_kernel *k, unsigned dim) {
    cc_formula f;
    cc_init(&f, CC_INTERVAL);
    cc_formula_id result = 0;
    if (cc_generator(&f, dim, true) == CC_OK)
        result = cc_kernel_formula(k, &f);
    else
        ck_fail(k, "Invalid interval variable.");
    cc_clear(&f);
    return result;
}

cc_formula_id ck_endpoint_face(cc_kernel *k, unsigned dim, unsigned endpoint) {
    cc_formula f;
    cc_init(&f, CC_FACE);
    cc_formula_id result = 0;
    if (cc_generator(&f, dim, endpoint != 0) == CC_OK)
        result = cc_kernel_formula(k, &f);
    else
        ck_fail(k, "Invalid face variable.");
    cc_clear(&f);
    return result;
}
