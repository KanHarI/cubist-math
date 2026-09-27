/* Elimination of declared types (H1 family F5, specification 3.6, 3.7, 5.6).
 * An eliminator's clause types are computed by substitution, with no
 * reduction: displayed types over the constructor's cube, whose boundaries
 * show each position by its displayed variable and each earlier constructor
 * by its clause. Iota reuses the same display, with each position shown by
 * its value λ ys. elim^C(q(ys)), and instantiates it at the arguments. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

static cc_term var(cc_kernel *k, uint32_t symbol) {
    return ck_var(k, symbol);
}

/* The display of 3.6 at an instance: the positions of one constructor, each
 * shown by a term (a displayed variable, or in Iota its value), and the
 * clauses of the earlier constructors. */
typedef struct {
    cc_kernel *k;
    const cc_signature *signature;
    cc_term instance, motive;
    const cc_term *clauses;
    uint32_t earlier, positions;
    uint32_t position_symbols[CC_CONSTRUCTOR_ARGUMENTS];
    cc_term shown[CC_CONSTRUCTOR_ARGUMENTS];
} display;

static cc_term displayed(display *d, cc_term cube, cc_term y, unsigned depth);
static cc_term shown_boundary(display *d, cc_term e, unsigned depth);

/* ⟦E⟧': under a positional argument's arity binders. */
static cc_term shown_positional(display *d, cc_term e, unsigned depth) {
    cc_node n = d->k->nodes[e];
    if (n.kind != CC_LAM)
        return shown_boundary(d, e, depth + 1);
    cc_term body = shown_positional(d, n.child[1], depth + 1);
    return body ? ck_make(d->k, CC_LAM, n.payload, n.child[0], body, 0, 0) : 0;
}

/* ⟦E⟧: q_j(us) is q̄_j(us), c_m(us, Es') is m_m(us, Es', ⟦Es'⟧'), and path
 * application and abstraction are kept, with their carried types displayed. */
static cc_term shown_boundary(display *d, cc_term e, unsigned depth) {
    cc_kernel *k = d->k;
    if (depth > 256)
        return ck_fail(k, "A boundary is nested too deeply."), 0;
    cc_node n = k->nodes[e];
    if (n.kind == CC_PLAM) {
        cc_term family = displayed(d, n.child[0], n.child[1], depth + 1);
        cc_term body = shown_boundary(d, n.child[1], depth + 1);
        return family && body ? ck_make(k, CC_PLAM, n.payload, family, body, 0, 0) : 0;
    }
    if (n.kind == CC_PAPP) {
        cc_term type = displayed(d, n.child[1], n.child[0], depth + 1);
        cc_term path = shown_boundary(d, n.child[0], depth + 1);
        return type && path ? ck_make(k, CC_PAPP, n.payload, path, type, 0, 0) : 0;
    }
    cc_term arguments[CC_CONSTRUCTOR_ARGUMENTS];
    uint32_t count = 0;
    cc_term head = e;
    while (k->nodes[head].kind == CC_APP) {
        if (count == CC_CONSTRUCTOR_ARGUMENTS)
            return ck_fail(k, "A boundary applies a constructor to too many arguments."), 0;
        arguments[count++] = k->nodes[head].child[1];
        head = k->nodes[head].child[0];
    }
    cc_node h = k->nodes[head];
    if (h.kind == CC_VAR)
        for (uint32_t j = 0; j < d->positions; ++j)
            if (d->position_symbols[j] == h.payload) {
                cc_term result = d->shown[j];
                for (uint32_t a = count; a-- > 0 && result;)
                    result = app(k, result, arguments[a]);
                return result;
            }
    if (h.kind == CC_CON && h.payload < d->earlier) {
        const cc_constructor *c = &d->signature->constructors[h.payload];
        if (count != c->data + c->positions)
            return ck_fail(k, "A boundary applies an earlier constructor to all its arguments."), 0;
        cc_term result = d->clauses[h.payload];
        for (uint32_t a = count; a-- > 0 && result;)
            result = app(k, result, arguments[a]);
        for (uint32_t p = c->positions; p-- > 0 && result;) {
            cc_term shown = shown_positional(d, arguments[p], depth + 1);
            result = shown ? app(k, result, shown) : 0;
        }
        return result;
    }
    return ck_fail(k, "A boundary is not a constructor expression."), 0;
}

/* C̄(y): M(y) over the sort, PathP(i. C̄(y @ i), ⟦E⟧, ⟦E'⟧) over a path type. */
static cc_term displayed(display *d, cc_term cube, cc_term y, unsigned depth) {
    cc_kernel *k = d->k;
    if (depth > 256)
        return ck_fail(k, "A cube is nested too deeply."), 0;
    if (cube == d->instance || (k->nodes[cube].kind == CC_SORT && ck_alpha_equal(k, cube, d->instance)))
        return app(k, d->motive, y);
    cc_node c = k->nodes[cube];
    if (c.kind != CC_PATH)
        return ck_fail(k, "A cube is the sort or a path type over it."), 0;
    cc_term at = ck_make(k, CC_PAPP, ck_interval_variable(k, c.payload), y, cube, 0, 0);
    cc_term family = displayed(d, c.child[0], at, depth + 1);
    cc_term left = shown_boundary(d, c.child[1], depth + 1);
    cc_term right = shown_boundary(d, c.child[2], depth + 1);
    return family && left && right ? ck_make(k, CC_PATH, c.payload, family, left, right, 0) : 0;
}

/* The parts of ClauseType_k over variables: the arguments ts, qs, the
 * displayed positions q̄s and the displayed result R̄(c). */
typedef struct {
    uint32_t count, data, positions, dimensions;
    uint32_t symbols[CC_CONSTRUCTOR_ARGUMENTS];
    cc_term domains[CC_CONSTRUCTOR_ARGUMENTS];
    uint32_t shown_symbols[CC_CONSTRUCTOR_ARGUMENTS];
    cc_term shown_domains[CC_CONSTRUCTOR_ARGUMENTS];
    cc_term cube;        /* R */
    cc_term constructed; /* c_k(as)(ts, qs) */
} clause_parts;

/* A position's type Π (ys : As). C: its arity binders and its cube. */
static uint32_t arity(cc_kernel *k, cc_term type, uint32_t *symbols, cc_term *domains, cc_term *cube) {
    uint32_t n = 0;
    while (k->nodes[type].kind == CC_PI && n < CC_CONSTRUCTOR_ARGUMENTS) {
        symbols[n] = k->nodes[type].payload;
        domains[n++] = k->nodes[type].child[0];
        type = k->nodes[type].child[1];
    }
    *cube = type;
    return n;
}

static bool parts(cc_kernel *k, display *d, cc_term instance, cc_term motive, const cc_term *clauses,
                  uint32_t constructor, clause_parts *out) {
    const cc_signature *s = ck_instance_signature(k, instance);
    if (!s)
        return false;
    if (constructor >= s->constructor_count)
        return ck_fail(k, "The signature has no such constructor.");
    const cc_constructor *c = &s->constructors[constructor];
    cc_term type = ck_constructor_type(k, instance, constructor);
    if (!type)
        return false;
    *out = (clause_parts){.count = c->data + c->positions, .data = c->data, .positions = c->positions,
                          .dimensions = c->dimensions};
    cc_term constructed = ck_make(k, CC_CON, constructor, instance, 0, 0, 0);
    for (uint32_t m = 0; m < out->count; ++m) {
        cc_node pi = k->nodes[type];
        if (pi.kind != CC_PI)
            return ck_fail(k, "A constructor's type has fewer arguments than it takes.");
        out->symbols[m] = pi.payload;
        out->domains[m] = pi.child[0];
        constructed = app(k, constructed, var(k, pi.payload));
        type = pi.child[1];
    }
    out->cube = type;
    out->constructed = constructed;
    *d = (display){.k = k, .signature = s, .instance = instance, .motive = motive, .clauses = clauses,
                   .earlier = constructor, .positions = c->positions};
    for (uint32_t j = 0; j < c->positions; ++j) {
        d->position_symbols[j] = out->symbols[c->data + j];
        out->shown_symbols[j] = ck_fresh_symbol(k);
        d->shown[j] = var(k, out->shown_symbols[j]);
    }
    /* Q̄_j := Π (ys : As). C̄_j(q_j(ys)). */
    for (uint32_t j = 0; j < c->positions && !k->error[0]; ++j) {
        uint32_t ys[CC_CONSTRUCTOR_ARGUMENTS];
        cc_term as[CC_CONSTRUCTOR_ARGUMENTS], cube = 0;
        uint32_t n = arity(k, out->domains[c->data + j], ys, as, &cube);
        cc_term y = var(k, d->position_symbols[j]);
        for (uint32_t a = 0; a < n; ++a)
            y = app(k, y, var(k, ys[a]));
        cc_term shown = displayed(d, cube, y, 0);
        for (uint32_t a = n; a-- > 0 && shown;)
            shown = ck_make(k, CC_PI, ys[a], as[a], shown, 0, 0);
        out->shown_domains[j] = shown;
    }
    return !k->error[0];
}

cc_term ck_clause_type(cc_kernel *k, cc_term instance, cc_term motive, const cc_term *clauses, uint32_t constructor) {
    display d;
    clause_parts p;
    if (!parts(k, &d, instance, motive, clauses, constructor, &p))
        return 0;
    cc_term type = displayed(&d, p.cube, p.constructed, 0);
    for (uint32_t j = p.positions; j-- > 0 && type;)
        type = ck_make(k, CC_PI, p.shown_symbols[j], p.shown_domains[j], type, 0, 0);
    for (uint32_t m = p.count; m-- > 0 && type;)
        type = ck_make(k, CC_PI, p.symbols[m], p.domains[m], type, 0, 0);
    return type;
}

/* elim^C(y), with D = C̄(y): elim(y) over the sort, and ⟨i⟩ elim^{C'}(y @ i)
 * over a path type, whose family is D's. */
static cc_term lifted(cc_kernel *k, cc_term eliminator, cc_term instance, cc_term cube, cc_term shown, cc_term y) {
    if (cube == instance || (k->nodes[cube].kind == CC_SORT && ck_alpha_equal(k, cube, instance)))
        return app(k, eliminator, y);
    cc_node c = k->nodes[cube], s = k->nodes[shown];
    if (c.kind != CC_PATH || s.kind != CC_PATH || c.payload != s.payload)
        return ck_fail(k, "A position's displayed cube does not follow its cube."), 0;
    cc_term at = ck_make(k, CC_PAPP, ck_interval_variable(k, c.payload), y, cube, 0, 0);
    cc_term body = lifted(k, eliminator, instance, c.child[0], s.child[0], at);
    return body ? ck_make(k, CC_PLAM, c.payload, s.child[0], body, 0, 0) : 0;
}

/* elim_{M, ms}(c_k(as)(ts, qs) @ rs) ⟶ m_k(ts, qs, q̄s) @ rs (3.7), with
 * q̄_j := λ ys. elim^{C_j}(q_j(ys)) and the annotations of R̄. When weak, the
 * argument is first taken to its weak head, and an hcomp eliminates by 3.7's
 * rule for formal composition. */
cc_term ck_eliminate(cc_kernel *k, cc_term eliminator, cc_term argument, bool weak, bool *reduced) {
    *reduced = false;
    cc_term value = weak ? ck_whnf(k, argument) : argument;
    if (!value)
        return 0;
    if (weak && k->nodes[value].kind == CC_HCOMP) {
        *reduced = true;
        return ck_pushout_eliminate_hcomp(k, eliminator, value);
    }
    cc_formula_id formulas[CC_CONSTRUCTOR_DIMENSIONS];
    uint32_t depth = 0;
    cc_term head = value;
    while (k->nodes[head].kind == CC_PAPP) {
        if (depth == CC_CONSTRUCTOR_DIMENSIONS)
            return app(k, eliminator, value);
        formulas[depth++] = k->nodes[head].payload;
        head = k->nodes[head].child[0];
    }
    for (uint32_t l = 0; l < depth / 2; ++l) {
        cc_formula_id swap = formulas[l];
        formulas[l] = formulas[depth - 1 - l];
        formulas[depth - 1 - l] = swap;
    }
    uint32_t constructor = 0, count = 0;
    cc_term arguments[CC_CONSTRUCTOR_ARGUMENTS];
    if (!ck_constructor_application(k, head, &constructor, arguments, &count))
        return app(k, eliminator, value);
    cc_term con = head;
    while (k->nodes[con].kind == CC_APP)
        con = k->nodes[con].child[0];
    cc_term instance = k->nodes[con].child[0];
    cc_node e = k->nodes[eliminator];
    cc_term clauses[CC_SIGNATURE_CONSTRUCTORS];
    uint32_t clause_count = 0;
    for (cc_term cursor = e.child[1]; cursor && clause_count < CC_SIGNATURE_CONSTRUCTORS;
         cursor = k->nodes[cursor].child[1])
        clauses[clause_count++] = k->nodes[cursor].child[0];
    const cc_signature *s = ck_instance_signature(k, instance);
    if (!s)
        return 0;
    if (constructor >= clause_count || constructor >= s->constructor_count)
        return app(k, eliminator, value);
    display d;
    clause_parts p;
    if (!parts(k, &d, instance, e.child[0], clauses, constructor, &p))
        return 0;
    if (count != p.count || depth != p.dimensions)
        return app(k, eliminator, value);
    /* The positions shown by their values, over the argument variables. */
    for (uint32_t j = 0; j < p.positions; ++j) {
        uint32_t ys[CC_CONSTRUCTOR_ARGUMENTS];
        cc_term as[CC_CONSTRUCTOR_ARGUMENTS], cube = 0;
        uint32_t n = arity(k, p.domains[p.data + j], ys, as, &cube);
        cc_term y = var(k, d.position_symbols[j]);
        for (uint32_t a = 0; a < n; ++a)
            y = app(k, y, var(k, ys[a]));
        cc_term shown = displayed(&d, cube, y, 0);
        cc_term value_j = shown ? lifted(k, eliminator, instance, cube, shown, y) : 0;
        for (uint32_t a = n; a-- > 0 && value_j;)
            value_j = ck_make(k, CC_LAM, ys[a], as[a], value_j, 0, 0);
        if (!value_j)
            return 0;
        d.shown[j] = value_j;
    }
    cc_term reduct = clauses[constructor];
    for (uint32_t m = 0; m < p.count; ++m)
        reduct = app(k, reduct, var(k, p.symbols[m]));
    for (uint32_t j = 0; j < p.positions; ++j)
        reduct = app(k, reduct, d.shown[j]);
    cc_term type = depth ? displayed(&d, p.cube, p.constructed, 0) : 0;
    /* At the arguments: the variables are the constructor type's own, fresh. */
    for (uint32_t m = 0; m < p.count && reduct; ++m) {
        reduct = ck_substitute(k, reduct, p.symbols[m], arguments[m]);
        if (depth)
            type = type ? ck_substitute(k, type, p.symbols[m], arguments[m]) : 0;
    }
    if (!reduct || (depth && !type))
        return 0;
    *reduced = true;
    return depth ? ck_apply_at(k, reduct, type, formulas, depth) : reduct;
}

/* ---- Instructions ----------------------------------------------------------- */

static bool eliminator_fact(cc_kernel *k, cc_judgement_id id, cc_fact *out, uint32_t *given) {
    if (!id || id >= cc_kernel_judgement_count(k))
        return ck_fail(k, "Unknown judgement.");
    cc_judgement_info info;
    if (!cc_kernel_judgement(k, id, &info) || info.kind != CC_FACT_ELIMINATOR)
        return ck_fail(k, "Expected an eliminator in progress.");
    *out = k->facts[id];
    *given = (uint32_t)out->pending;
    return true;
}

/* The clauses so far, in order, from an eliminator's reversed list. */
static uint32_t clauses_of(cc_kernel *k, cc_term reversed, cc_term *out) {
    cc_term backwards[CC_SIGNATURE_CONSTRUCTORS];
    uint32_t n = 0;
    for (cc_term cursor = reversed; cursor && n < CC_SIGNATURE_CONSTRUCTORS; cursor = k->nodes[cursor].child[1])
        backwards[n++] = k->nodes[cursor].child[0];
    for (uint32_t i = 0; i < n; ++i)
        out[i] = backwards[n - 1 - i];
    return n;
}

/* The next clause's type, or, with every clause given, Π (z : I). M(z). */
static cc_term expected(cc_kernel *k, cc_term instance, cc_term motive, const cc_term *clauses, uint32_t given) {
    const cc_signature *s = ck_instance_signature(k, instance);
    if (!s)
        return 0;
    if (given < s->constructor_count)
        return ck_clause_type(k, instance, motive, clauses, given);
    uint32_t z = ck_fresh_symbol(k);
    return ck_make(k, CC_PI, z, instance, app(k, motive, var(k, z)), 0, 0);
}

static cc_judgement_id in_progress(cc_kernel *k, cc_term instance, cc_term motive, cc_term reversed, uint32_t given,
                                   uint32_t context) {
    const cc_signature *s = ck_instance_signature(k, instance);
    cc_term clauses[CC_SIGNATURE_CONSTRUCTORS];
    uint32_t n = clauses_of(k, reversed, clauses);
    cc_term type = s ? expected(k, instance, motive, clauses, n) : 0;
    uint32_t index = s ? k->nodes[instance].payload : 0;
    cc_term term = type ? ck_make(k, CC_ELIM, index, motive, reversed, 0, 0) : 0;
    cc_judgement_id id = term ? ck_instr_publish(k, CC_FACT_ELIMINATOR, term, instance, type, context) : 0;
    if (id)
        k->facts[id].pending = given;
    return id;
}

cc_judgement_id cc_instr_eliminator(cc_kernel *k, cc_judgement_id motive_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_ELIMINATOR, .premise = {motive_id}}, NULL, 0, &found))
        return found;
    cc_fact m = {0};
    if (!ck_instr_premise(k, motive_id, CC_FACT_TYPING, &m))
        return 0;
    cc_node family = k->nodes[m.type];
    if (family.kind != CC_PI || k->nodes[family.child[1]].kind != CC_U || k->nodes[family.child[0]].kind != CC_SORT)
        return ck_fail(k, "An eliminator's motive is a family of types over an instance of a declared type: "
                          "Π (z : S(as)). U(l)."), 0;
    if (!ck_instance_signature(k, family.child[0]))
        return 0;
    return in_progress(k, family.child[0], m.term, 0, 0, m.context);
}

cc_judgement_id cc_instr_eliminator_clause(cc_kernel *k, cc_judgement_id eliminator, cc_judgement_id clause) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_ELIMINATOR_CLAUSE, .premise = {eliminator, clause}},
                        NULL, 0, &found))
        return found;
    cc_fact e = {0}, c = {0};
    uint32_t given = 0, context = 0;
    if (!eliminator_fact(k, eliminator, &e, &given) || !ck_instr_premise(k, clause, CC_FACT_TYPING, &c))
        return 0;
    const cc_signature *s = ck_instance_signature(k, e.other);
    if (!s)
        return 0;
    if (given >= s->constructor_count)
        return ck_fail(k, "The eliminator has a clause for every constructor; close it."), 0;
    /* The clause's type is ClauseType_k, compared as written (3.6). */
    if (!ck_alpha_equal(k, c.type, e.type)) {
        if (!k->error[0]) {
            k->mismatch_found = c.type;
            k->mismatch_expected = e.type;
            ck_fail_as(k, CC_ERROR_MISMATCH, "The clause's type is not the constructor's clause type: its "
                                             "boundaries must be the displayed boundaries of 3.6.");
        }
        return 0;
    }
    cc_node elim = k->nodes[e.term];
    cc_term reversed = ck_make(k, CC_LIST, 0, c.term, elim.child[1], 0, 0);
    if (!reversed || !ck_instr_merge(k, e.context, c.context, &context))
        return 0;
    return in_progress(k, e.other, elim.child[0], reversed, given + 1, context);
}

cc_judgement_id cc_instr_eliminator_close(cc_kernel *k, cc_judgement_id eliminator) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_ELIMINATOR_CLOSE, .premise = {eliminator}}, NULL, 0, &found))
        return found;
    cc_fact e = {0};
    uint32_t given = 0;
    if (!eliminator_fact(k, eliminator, &e, &given))
        return 0;
    const cc_signature *s = ck_instance_signature(k, e.other);
    if (!s)
        return 0;
    if (given < s->constructor_count)
        return ck_fail(k, "The eliminator lacks a clause: every constructor, the squash included, needs one."), 0;
    cc_node elim = k->nodes[e.term];
    cc_term clauses[CC_SIGNATURE_CONSTRUCTORS];
    uint32_t n = clauses_of(k, elim.child[1], clauses);
    cc_term list = 0;
    for (uint32_t i = n; i-- > 0 && !k->error[0];)
        list = ck_make(k, CC_LIST, 0, clauses[i], list, 0, 0);
    cc_term term = ck_make(k, CC_ELIM, elim.payload, elim.child[0], list, 0, 0);
    return term ? ck_instr_publish(k, CC_FACT_TYPING, term, 0, e.type, e.context) : 0;
}
