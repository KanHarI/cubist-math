/* Definitional equality first compares folded syntax, then demanded heads. Interval
 * normal forms remain De Morgan expressions; endpoint tests are face formulas.
 * An unbound name must never be identified with a binder on the other side. */
#include "term_internal.h"

enum comparison_mode { FOLDED, EXPOSE, COMPUTE, CONGRUENCE, HINTED };

typedef struct alpha_binding {
    uint32_t left, right;
    uint64_t scope;
    bool identity;
    const struct alpha_binding *previous;
} alpha_binding;

static size_t comparison_slot(uint64_t hash) {
    /* Arena handles and binder names are sequential. Mix their high bits too,
     * rather than letting the power-of-two table discard them outright. */
    hash ^= hash >> 33;
    hash *= UINT64_C(0xff51afd7ed558ccd);
    hash ^= hash >> 33;
    return (size_t)(hash % CC_ALPHA_MEMO_SIZE);
}

static alpha_binding bind(cc_kernel *k, uint32_t left, uint32_t right,
                           const alpha_binding *previous) {
    uint64_t parent = previous ? previous->scope : 0;
    size_t slot = comparison_slot((parent * UINT64_C(1099511628211) ^ left) *
                                 UINT64_C(1099511628211) ^ right);
    if (!k->alpha_scopes)
        k->alpha_scopes = calloc(CC_ALPHA_MEMO_SIZE, sizeof *k->alpha_scopes);
    cc_alpha_scope *entry = k->alpha_scopes ? &k->alpha_scopes[slot] : NULL;
    uint64_t scope;
    if (entry && entry->scope && entry->parent == parent && entry->left == left && entry->right == right) {
        scope = entry->scope;
    } else {
        if (k->next_alpha_scope == UINT64_MAX)
            ck_fail(k, "Alpha-comparison scope counter exhausted.");
        scope = k->next_alpha_scope == UINT64_MAX ? UINT64_MAX : ++k->next_alpha_scope;
        if (entry) *entry = (cc_alpha_scope){left, right, parent, scope};
    }
    return (alpha_binding){left, right, scope,
        left == right && (!previous || previous->identity), previous};
}

static size_t alpha_slot(cc_term left, cc_term right, uint64_t terms, uint64_t dims) {
    uint64_t hash = (uint64_t)left * UINT64_C(1099511628211);
    hash = (hash ^ right) * UINT64_C(1099511628211);
    hash = (hash ^ terms) * UINT64_C(1099511628211);
    hash = (hash ^ dims) * UINT64_C(1099511628211);
    return comparison_slot(hash);
}

static const alpha_binding *bound(const alpha_binding *env, uint32_t name, bool right) {
    for (; env; env = env->previous)
        if ((right ? env->right : env->left) == name)
            return env;
    return NULL;
}

static bool same_name(uint32_t a, uint32_t b, const alpha_binding *env) {
    const alpha_binding *left = bound(env, a, false);
    const alpha_binding *right = bound(env, b, true);
    return left || right ? left && left == right : a == b;
}

static bool clause_included(cc_clause a, cc_clause b, const alpha_binding *dims) {
    for (unsigned i = 0; i < CC_DIMENSIONS; ++i) {
        uint64_t bit = UINT64_C(1) << i;
        for (unsigned endpoint = 0; endpoint < 2; ++endpoint) {
            if (!((endpoint ? a.positive : a.negative) & bit))
                continue;
            bool found = false;
            for (unsigned j = 0; j < CC_DIMENSIONS; ++j)
                if (((endpoint ? b.positive : b.negative) & (UINT64_C(1) << j)) && same_name(i, j, dims)) {
                    found = true;
                    break;
                }
            if (!found)
                return false;
        }
    }
    return true;
}

static bool formula_equal(cc_kernel *k, uint32_t a, uint32_t b, const alpha_binding *dims) {
    const cc_formula *left = cc_kernel_get_formula(k, a);
    const cc_formula *right = cc_kernel_get_formula(k, b);
    if (!left || !right || left->sort != right->sort || left->length != right->length)
        return false;
    for (size_t i = 0; i < left->length; ++i) {
        bool found = false;
        /* A binder renaming is bijective. Forward inclusion plus equal
         * literal counts therefore establishes equality of the clauses. */
        for (size_t j = 0; j < right->length; ++j) {
            unsigned l = 0, r = 0;
            for (unsigned d = 0; d < CC_DIMENSIONS; ++d) {
                uint64_t bit = UINT64_C(1) << d;
                l += (left->clauses[i].positive & bit) != 0;
                l += (left->clauses[i].negative & bit) != 0;
                r += (right->clauses[j].positive & bit) != 0;
                r += (right->clauses[j].negative & bit) != 0;
            }
            if (l == r && clause_included(left->clauses[i], right->clauses[j], dims)) {
                found = true;
                break;
            }
        }
        if (!found)
            return false;
    }
    return true;
}

static bool alpha(cc_kernel *, cc_term, cc_term, const alpha_binding *, const alpha_binding *, enum comparison_mode);

/* Peel applications without evaluating their arguments or function bodies. */
static cc_term application_head(cc_kernel *k, cc_term term) {
    while (k->nodes[term].kind == CC_APP)
        term = k->nodes[term].child[0];
    return term;
}

/* Beta-reduce only explicit lambda heads, without unfolding constants. */
static cc_term beta_application_head(cc_kernel *k, cc_term term) {
    if (++k->recursion > 512 || !ck_tick(k, false)) {
        --k->recursion;
        ck_fail(k, "Application beta depth exceeded.");
        return 0;
    }
    cc_node n = k->nodes[term];
    cc_term result = term;
    if (n.kind == CC_APP) {
        cc_term fn = beta_application_head(k, n.child[0]);
        if (!fn) {
            result = 0;
        } else if (k->nodes[fn].kind == CC_LAM) {
            cc_node lambda = k->nodes[fn];
            cc_term body = ck_substitute(k, lambda.child[1], lambda.payload, n.child[1]);
            result = body ? beta_application_head(k, body) : 0;
        } else if (fn != n.child[0]) {
            result = ck_make(k, CC_APP, 0, fn, n.child[1], 0, 0);
        }
    }
    --k->recursion;
    return result;
}

/* Unfold exactly the selected head definition, then discharge the lambdas
 * already supplied with arguments. Older definitions inside its body stay
 * folded so a shared head can be recognized before further computation. */
static cc_term unfold_application_head(cc_kernel *k, cc_term term) {
    if (++k->recursion > 512) {
        --k->recursion;
        ck_fail(k, "Application spine depth exceeded.");
        return 0;
    }
    cc_node n = k->nodes[term];
    cc_term result = term;
    if (n.kind == CC_DEFREF) {
        if (!n.payload || n.payload >= k->definition_count) {
            ck_fail(k, "Unknown definition in application comparison.");
            result = 0;
        } else {
            result = beta_application_head(k, k->definitions[n.payload].value);
        }
    } else if (n.kind == CC_APP) {
        cc_term fn = unfold_application_head(k, n.child[0]);
        if (!fn) {
            result = 0;
        } else if (k->nodes[fn].kind == CC_LAM) {
            cc_node lambda = k->nodes[fn];
            result = ck_substitute(k, lambda.child[1], lambda.payload, n.child[1]);
        } else {
            result = ck_make(k, CC_APP, 0, fn, n.child[1], 0, 0);
        }
    }
    --k->recursion;
    return result;
}

static bool has_unfolding_hint(const cc_kernel *k, cc_node head) {
    if (head.kind == CC_DEFREF)
        for (size_t i = 0; i < k->unfolding_hint_count; ++i)
            if (k->unfolding_hints[i] == head.payload)
                return true;
    return false;
}

/* A preliminary comparison unfolds only requested definitions. Other heads
 * remain folded, allowing a wrapper to reveal a common opaque computation. */
static cc_term hinted_head(cc_kernel *k, cc_term term) {
    for (unsigned step = 0; step < 128 && term && !k->error[0]; ++step) {
        cc_term before = term;
        term = beta_application_head(k, term);
        if (!term)
            return 0;
        cc_term head = application_head(k, term);
        if (has_unfolding_hint(k, k->nodes[head])) {
            term = unfold_application_head(k, term);
        } else {
            cc_node n = k->nodes[term];
            if (n.kind == CC_PAPP || n.kind == CC_COMP || n.kind == CC_HCOMP || n.kind == CC_TRANS)
                term = ck_expose(k, term);
            else if (n.kind == CC_FST || n.kind == CC_SND) {
                if (++k->recursion > 512) {
                    --k->recursion;
                    ck_fail(k, "Hinted projection depth exceeded.");
                    return 0;
                }
                cc_term pair = hinted_head(k, n.child[0]);
                --k->recursion;
                if (!pair)
                    return 0;
                if (k->nodes[pair].kind == CC_PAIR)
                    term = k->nodes[pair].child[n.kind == CC_FST ? 1 : 2];
                else if (pair != n.child[0])
                    term = ck_make(k, n.kind, 0, pair, 0, 0, 0);
            }
        }
        if (term == before)
            break;
    }
    return term;
}

static bool tube_alpha(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                       const alpha_binding *outer_dims, const alpha_binding *inner_dims, enum comparison_mode mode) {
    if (!a || !b)
        return a == b;
    cc_node left = k->nodes[a], right = k->nodes[b];
    if (left.kind != CC_TUBE || right.kind != CC_TUBE)
        return false;
    return formula_equal(k, left.payload, right.payload, outer_dims) &&
           alpha(k, left.child[0], right.child[0], terms, inner_dims, mode) &&
           tube_alpha(k, left.child[1], right.child[1], terms, outer_dims, inner_dims, mode);
}

static bool alpha_inner(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                         const alpha_binding *dims, enum comparison_mode mode) {
    if (!ck_tick(k, false))
        return false;
    if (!a || !b)
        return a == b;
    if (a == b && (!terms || terms->identity) && (!dims || dims->identity))
        return true;
    if (mode != FOLDED && alpha(k, a, b, terms, dims, FOLDED))
        return true;
    if (mode == COMPUTE && k->unfolding_hint_count && alpha(k, a, b, terms, dims, HINTED))
        return true;
    if (mode == HINTED) {
        cc_term left = hinted_head(k, a);
        cc_term right = hinted_head(k, b);
        if (!left || !right)
            return false;
        if (left != a || right != b)
            return alpha(k, left, right, terms, dims, HINTED);
    }
    if (mode == COMPUTE && alpha(k, a, b, terms, dims, EXPOSE))
        return true;
    if (mode == EXPOSE) {
        /* Delta expansion is separate from evaluation. An alias for a compact
         * numeral can already match its checked expression after one step. */
        cc_node left = k->nodes[a], right = k->nodes[b];
        if (left.kind == CC_DEFREF || right.kind == CC_DEFREF) {
            if (left.kind == CC_DEFREF) {
                if (!left.payload || left.payload >= k->definition_count)
                    return ck_fail(k, "Unknown definition in conversion.");
                a = k->definitions[left.payload].value;
            }
            if (right.kind == CC_DEFREF) {
                if (!right.payload || right.payload >= k->definition_count)
                    return ck_fail(k, "Unknown definition in conversion.");
                b = k->definitions[right.payload].value;
            }
            return alpha(k, a, b, terms, dims, EXPOSE);
        }
    }
    if (mode == EXPOSE) {
        cc_term exposed_a = ck_expose(k, a);
        cc_term exposed_b = ck_expose(k, b);
        if (!exposed_a || !exposed_b)
            return false;
        if (exposed_a != a || exposed_b != b)
            return alpha(k, exposed_a, exposed_b, terms, dims, EXPOSE);
    }
    if (mode == COMPUTE) {
        cc_term old_a, old_b;
        do {
            old_a = a;
            if (k->nodes[a].kind == CC_DEFREF)
                a = k->definitions[k->nodes[a].payload].value;
            else
                a = ck_expose(k, a);
        } while (a && a != old_a && ck_tick(k, false));
        do {
            old_b = b;
            if (k->nodes[b].kind == CC_DEFREF)
                b = k->definitions[k->nodes[b].payload].value;
            else
                b = ck_expose(k, b);
        } while (b && b != old_b && ck_tick(k, false));
        if (!a || !b || k->error[0])
            return false;
        /* Congruence can compare small arguments of a shared computation
         * before evaluating its potentially enormous result. */
        if (alpha(k, a, b, terms, dims, CONGRUENCE))
            return true;
        a = ck_whnf(k, a);
        b = ck_whnf(k, b);
    }
    if (!a || !b)
        return false;
    cc_node left = k->nodes[a], right = k->nodes[b];
    enum comparison_mode children_mode = mode == CONGRUENCE ? COMPUTE : mode;
    if (left.kind != right.kind) {
        /* Pair eta also belongs to the selective pass: otherwise a folded
         * (fst p, snd p) versus p comparison would force unrelated definitions
         * to unfold before reaching the existing eta rule below. */
        bool hinted_pair = mode == HINTED && (left.kind == CC_PAIR || right.kind == CC_PAIR);
        if (mode != COMPUTE && !hinted_pair)
            return false;
        /* Function eta is checked here, without reducing lambda bodies merely
         * to discover their shape during weak-head inspection. */
        if (left.kind == CC_LAM) {
            uint32_t fresh = ck_fresh_symbol(k);
            cc_term applied = ck_make(k, CC_APP, 0, b, ck_var(k, fresh), 0, 0);
            alpha_binding binding = bind(k, left.payload, fresh, terms);
            return alpha(k, left.child[1], applied, &binding, dims, children_mode);
        }
        if (right.kind == CC_LAM) {
            uint32_t fresh = ck_fresh_symbol(k);
            cc_term applied = ck_make(k, CC_APP, 0, a, ck_var(k, fresh), 0, 0);
            alpha_binding binding = bind(k, fresh, right.payload, terms);
            return alpha(k, applied, right.child[1], &binding, dims, children_mode);
        }
        if (left.kind == CC_PLAM || right.kind == CC_PLAM) {
            bool on_left = left.kind == CC_PLAM;
            cc_node line = on_left ? left : right;
            cc_term other = on_left ? b : a;
            uint64_t avoid = ck_free_dims(k, a) | ck_free_dims(k, b);
            for (const alpha_binding *entry = dims; entry; entry = entry->previous)
                avoid |= (UINT64_C(1) << entry->left) | (UINT64_C(1) << entry->right);
            unsigned direction = ck_fresh_dimension(k, avoid);
            if (direction >= CC_DIMENSIONS)
                return false;
            cc_formula_id argument = ck_interval_variable(k, direction);
            cc_formula variable;
            cc_init(&variable, CC_INTERVAL);
            if (cc_copy(&variable, cc_kernel_get_formula(k, argument)) != CC_OK)
                return ck_fail(k, "Path eta dimension allocation failed.");
            cc_term body = ck_dimension_substitute(k, line.child[1], line.payload, &variable);
            cc_clear(&variable);
            cc_term annotation = ck_make(k, CC_PATH, line.payload, line.child[0],
                ck_endpoint_term(k, line.child[1], line.payload, 0),
                ck_endpoint_term(k, line.child[1], line.payload, 1), 0);
            cc_term applied = ck_make(k, CC_PAPP, argument, other, annotation, 0, 0);
            alpha_binding binding = bind(k, direction, direction, dims);
            return on_left ? alpha(k, body, applied, terms, &binding, COMPUTE) :
                             alpha(k, applied, body, terms, &binding, COMPUTE);
        }
        /* Typed surjective pairing: compare a pair with the two projections
         * of the other term. This also handles components that only expose
         * their projection after reduction; it does not normalize unused data. */
        if (left.kind == CC_PAIR) {
            cc_term first = ck_make(k, CC_FST, 0, b, 0, 0, 0);
            cc_term second = ck_make(k, CC_SND, 0, b, 0, 0, 0);
            return alpha(k, left.child[1], first, terms, dims, children_mode) &&
                   alpha(k, left.child[2], second, terms, dims, children_mode);
        }
        if (right.kind == CC_PAIR) {
            cc_term first = ck_make(k, CC_FST, 0, a, 0, 0, 0);
            cc_term second = ck_make(k, CC_SND, 0, a, 0, 0, 0);
            return alpha(k, first, right.child[1], terms, dims, children_mode) &&
                   alpha(k, second, right.child[2], terms, dims, children_mode);
        }
        return false;
    }
    if (left.kind == CC_U || left.kind == CC_DEFREF)
        return left.payload == right.payload;
    if (left.kind == CC_VAR)
        return same_name(left.payload, right.payload, terms);
    if (ck_term_binder(left.kind)) {
        alpha_binding binding = bind(k, left.payload, right.payload, terms);
        return alpha(k, left.child[0], right.child[0], terms, dims, children_mode) &&
               alpha(k, left.child[1], right.child[1], &binding, dims, children_mode);
    }
    if (ck_dim_binder(left.kind)) {
        alpha_binding binding = bind(k, left.payload, right.payload, dims);
        if (!alpha(k, left.child[0], right.child[0], terms, left.kind == CC_HCOMP ? dims : &binding, children_mode))
            return false;
        if (left.kind == CC_PLAM)
            return alpha(k, left.child[1], right.child[1], terms, &binding, children_mode);
        if (left.kind == CC_COMP || left.kind == CC_HCOMP)
            return tube_alpha(k, left.child[1], right.child[1], terms, dims, &binding, children_mode) &&
                   alpha(k, left.child[2], right.child[2], terms, dims, children_mode);
        return alpha(k, left.child[1], right.child[1], terms, dims, children_mode) &&
               alpha(k, left.child[2], right.child[2], terms, dims, children_mode);
    }
    if ((left.kind == CC_GLUE_SYSTEM || left.kind == CC_TUBE) && !formula_equal(k, left.payload, right.payload, dims))
        return false;
    if (left.kind == CC_PUSH_PATH && !formula_equal(k, left.payload, right.payload, dims))
        return false;
    if (left.kind == CC_PAPP)
        return formula_equal(k, left.payload, right.payload, dims) &&
               alpha(k, left.child[0], right.child[0], terms, dims, children_mode);
    for (unsigned i = 0; i < ck_arity(left.kind); ++i)
        if (!alpha(k, left.child[i], right.child[i], terms, dims, children_mode))
            return false;
    return true;
}

static bool alpha(cc_kernel *k, cc_term a, cc_term b, const alpha_binding *terms,
                   const alpha_binding *dims, enum comparison_mode mode) {
    if (++k->recursion > 512) {
        --k->recursion;
        return ck_fail(k, "Native conversion recursion depth exceeded.");
    }
    uint64_t term_scope = terms && !terms->identity ? terms->scope : 0;
    uint64_t dimension_scope = dims && !dims->identity ? dims->scope : 0;
    size_t slot = alpha_slot(a, b, term_scope, dimension_scope);
    if (a && b && k->alpha_memo) {
        cc_alpha_memo entry = k->alpha_memo[slot];
        if (entry.left == a && entry.right == b && entry.term_scope == term_scope &&
            entry.dimension_scope == dimension_scope && (entry.equal || mode == FOLDED)) {
            --k->recursion;
            return ck_tick(k, false) && entry.equal;
        }
    }
    bool equal = alpha_inner(k, a, b, terms, dims, mode);
    /* Success is definitional equality regardless of the reduction strategy.
     * A failed folded comparison says nothing about equality after reduction;
     * failures from other strategies (including hints) are never retained. */
    if ((equal || mode == FOLDED) && a && b && !k->error[0]) {
        if (!k->alpha_memo) {
            k->alpha_memo = calloc(CC_ALPHA_MEMO_SIZE, sizeof *k->alpha_memo);
            if (!k->alpha_memo)
                ck_fail(k, "Alpha-comparison memo allocation failed.");
        }
        if (k->alpha_memo)
            k->alpha_memo[slot] = (cc_alpha_memo){a, b, term_scope, dimension_scope, equal};
    }
    --k->recursion;
    return !k->error[0] && equal;
}

cc_term cc_kernel_rename(cc_kernel *k, cc_term term, bool dimension, uint32_t from, uint32_t to) {
    if (!k || k->error[0] || !term || term >= k->count)
        return 0;
    k->budget = k->operation_budget;
    k->recursion = 0;
    if (!dimension)
        return ck_substitute(k, term, from, ck_var(k, to));
    if (from >= CC_DIMENSIONS || to >= CC_DIMENSIONS)
        return ck_fail(k, "Dimension outside the native range."), 0;
    cc_formula point;
    cc_init(&point, CC_INTERVAL);
    cc_term renamed = cc_generator(&point, to, true) == CC_OK ? ck_dimension_substitute(k, term, from, &point) : 0;
    cc_clear(&point);
    return renamed;
}

bool cc_kernel_convertible(cc_kernel *k, cc_term a, cc_term b, uint64_t steps) {
    if (!k || k->error[0] || !a || !b || a >= k->count || b >= k->count)
        return false;
    k->budget = steps && steps < k->operation_budget ? steps : k->operation_budget;
    k->recursion = 0;
    return ck_convertible(k, a, b);
}

/* Syntactic equality up to bound names and interval algebra: nothing is
 * reduced or unfolded. The instruction kernel uses only this. */
bool ck_alpha_equal(cc_kernel *k, cc_term a, cc_term b) {
    return alpha(k, a, b, NULL, NULL, FOLDED);
}

/* Cumulativity without conversion: universes by level, and Π or Σ with
 * identical domains and cumulative codomains. */
bool ck_syntactic_cumulative(cc_kernel *k, cc_term actual, cc_term expected) {
    if (ck_alpha_equal(k, actual, expected))
        return true;
    if (k->error[0] || !actual || !expected)
        return false;
    cc_node left = k->nodes[actual], right = k->nodes[expected];
    if (left.kind == CC_U && right.kind == CC_U)
        return left.payload <= right.payload;
    if ((left.kind == CC_PI || left.kind == CC_SIGMA) && left.kind == right.kind &&
        ck_alpha_equal(k, left.child[0], right.child[0])) {
        cc_term variable = ck_var(k, ck_fresh_symbol(k));
        return ck_syntactic_cumulative(k, ck_substitute(k, left.child[1], left.payload, variable),
                                       ck_substitute(k, right.child[1], right.payload, variable));
    }
    return false;
}

bool ck_convertible(cc_kernel *k, cc_term a, cc_term b) {
    /* Prefer the folded checked structure. Equal closed references never
     * need their bodies evaluated, even inside larger matching types. */
    if (alpha(k, a, b, NULL, NULL, FOLDED))
        return true;
    return !k->error[0] && alpha(k, a, b, NULL, NULL, COMPUTE);
}

/* Cumulativity is directed typing, not definitional equality. A function or
 * dependent pair over the same domain remains valid when its result universe
 * is raised. Closing this rule under Pi/Sigma is necessary for substitution:
 * instantiating B : U1 with B : U0 can turn a checked family A -> U1 into a
 * lambda whose most precise inferred type is A -> U0.
 *
 * Domains must be definitionally equal. In particular this rule cannot widen
 * a function's accepted arguments, identify universes, or resize downward. */
static bool cumulative(cc_kernel *k, cc_term actual, cc_term expected) {
    if (++k->recursion > 512) {
        --k->recursion;
        return ck_fail(k, "Cumulative comparison recursion depth exceeded.");
    }
    bool accepted = ck_convertible(k, actual, expected);
    if (!accepted && !k->error[0]) {
        actual = ck_whnf(k, actual);
        expected = ck_whnf(k, expected);
        if (actual && expected) {
            cc_node left = k->nodes[actual];
            cc_node right = k->nodes[expected];
            if (left.kind == CC_U && right.kind == CC_U) {
                accepted = left.payload <= right.payload;
            } else if ((left.kind == CC_PI || left.kind == CC_SIGMA) &&
                       left.kind == right.kind &&
                       ck_convertible(k, left.child[0], right.child[0])) {
                /* Compare codomains under one common fresh variable. Both
                 * types have already been checked; no new assumption is
                 * approved by this comparison. */
                cc_term variable = ck_var(k, ck_fresh_symbol(k));
                cc_term left_body = ck_substitute(k, left.child[1], left.payload, variable);
                cc_term right_body = ck_substitute(k, right.child[1], right.payload, variable);
                accepted = cumulative(k, left_body, right_body);
            }
        }
    }
    --k->recursion;
    return accepted && !k->error[0];
}

bool ck_expect(cc_kernel *k, cc_term actual, cc_term expected) {
    ++k->trace_mute;
    bool agree = cumulative(k, actual, expected);
    --k->trace_mute;
    ck_trace(k, CC_TRACE_CONVERT, actual, expected, agree);
    if (agree)
        return true;
    if (!k->error[0]) {
        k->mismatch_found = actual;
        k->mismatch_expected = expected;
    }
    return ck_fail_as(k, CC_ERROR_MISMATCH, "Type mismatch.");
}
