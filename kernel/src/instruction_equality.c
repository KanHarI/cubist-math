/* Equality instructions: reflexivity, the sides of an equality, symmetry,
 * transitivity, conversion along an equality, cumulativity, eta, and the
 * targeted steps and replacements at a highlighted position. The machinery
 * they share is in instructions.c. */
#include "term_internal.h"

/* ---- Equality ----------------------------------------------------------- */

cc_judgement_id cc_instr_refl(cc_kernel *k, cc_judgement_id typing_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_REFL, .premise = {typing_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0};
    if (!ck_instr_premise(k, typing_id, CC_FACT_TYPING, &t))
        return 0;
    return ck_instr_publish(k, CC_FACT_EQUALITY, t.term, t.term, t.type, t.context);
}

/* Both sides of an equality have its type. */
cc_judgement_id cc_instr_side(cc_kernel *k, cc_judgement_id equality, unsigned side) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SIDE, .premise = {equality}, .operand = {side}}, NULL, 0, &found))
        return found;
    cc_fact e = {0};
    if (!ck_instr_premise(k, equality, CC_FACT_EQUALITY, &e))
        return 0;
    if (side > 1)
        return ck_fail(k, "An equality has sides 0 and 1."), 0;
    return ck_instr_typing(k, side ? e.other : e.term, e.type, e.context);
}

cc_judgement_id cc_instr_symmetry(cc_kernel *k, cc_judgement_id equality) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SYMMETRY, .premise = {equality}}, NULL, 0, &found))
        return found;
    cc_fact e = {0};
    if (!ck_instr_premise(k, equality, CC_FACT_EQUALITY, &e))
        return 0;
    return ck_instr_publish(k, CC_FACT_EQUALITY, e.other, e.term, e.type, e.context);
}

cc_judgement_id cc_instr_transitivity(cc_kernel *k, cc_judgement_id first, cc_judgement_id second) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_TRANSITIVITY, .premise = {first, second}}, NULL, 0, &found))
        return found;
    cc_fact a = {0}, b = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, first, CC_FACT_EQUALITY, &a) || !ck_instr_premise(k, second, CC_FACT_EQUALITY, &b) ||
        !ck_instr_same(k, b.term, a.other, "The equalities do not meet.") ||
        !ck_instr_same(k, b.type, a.type, "The equalities are at different types.") ||
        !ck_instr_merge(k, a.context, b.context, &context))
        return 0;
    return ck_instr_publish(k, CC_FACT_EQUALITY, a.term, b.other, a.type, context);
}

cc_judgement_id cc_instr_convert(cc_kernel *k, cc_judgement_id typing_id, cc_judgement_id equality) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_CONVERT, .premise = {typing_id, equality}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, e = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, typing_id, CC_FACT_TYPING, &t) || !ck_instr_premise(k, equality, CC_FACT_EQUALITY, &e) ||
        !ck_instr_universe(k, e.type, &level) || !ck_instr_same(k, t.type, e.term, "The equality does not start at the judgement's type.") ||
        !ck_instr_merge(k, t.context, e.context, &context))
        return 0;
    return ck_instr_typing(k, t.term, e.other, context);
}

cc_judgement_id cc_instr_lift(cc_kernel *k, cc_judgement_id typing_id, cc_judgement_id type_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_LIFT, .premise = {typing_id, type_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, b = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, typing_id, CC_FACT_TYPING, &t) || !ck_instr_premise(k, type_id, CC_FACT_TYPING, &b) ||
        !ck_instr_universe(k, b.type, &level))
        return 0;
    if (!ck_syntactic_cumulative(k, t.type, b.term)) {
        if (k->error[0])
            return 0;
        k->mismatch_found = t.type;
        k->mismatch_expected = b.term;
        return ck_fail_as(k, CC_ERROR_MISMATCH, "The type is not included in the target type."), 0;
    }
    if (!ck_instr_merge(k, t.context, b.context, &context))
        return 0;
    return ck_instr_typing(k, t.term, b.term, context);
}

/* The pieces of a Glue eta expansion: the term itself on each face of the
 * Glue type's system, in its order. On its face the term has the face's
 * type, as the Glue type is that type there. */
static cc_term eta_pieces(cc_kernel *k, cc_term system, cc_term term) {
    if (!system || k->error[0])
        return 0;
    cc_node piece = k->nodes[system];
    cc_term rest = eta_pieces(k, piece.child[2], term);
    return k->error[0] ? 0 : ck_instr_make(k, CC_TUBE, piece.payload, term, rest, 0, 0);
}

cc_judgement_id cc_instr_eta(cc_kernel *k, cc_judgement_id typing_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_ETA, .premise = {typing_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0};
    if (!ck_instr_premise(k, typing_id, CC_FACT_TYPING, &t))
        return 0;
    cc_node type = k->nodes[t.type];
    cc_term expanded = 0;
    /* λ (x : A). t x, built directly: t is locally closed, and x is index 0. */
    cc_term variable = ck_instr_make(k, CC_BOUND, 0, 0, 0, 0, 0);
    if (type.kind == CC_PI) {
        expanded = ck_instr_make(k, CC_LAM, 0, type.child[0], ck_instr_app(k, t.term, variable), 0, 0);
    } else if (type.kind == CC_LPI) {
        expanded = ck_instr_make(k, CC_LLAM, 0, type.child[0], ck_instr_make(k, CC_LAPP, 0, t.term, variable, 0, 0), 0, 0);
    } else if (type.kind == CC_SIGMA) {
        expanded = ck_instr_make(k, CC_PAIR, 0, t.type, ck_instr_make(k, CC_FST, 0, t.term, 0, 0, 0), ck_instr_make(k, CC_SND, 0, t.term, 0, 0, 0), 0);
    } else if (type.kind == CC_PATH) {
        unsigned fresh = ck_fresh_dimension(k, ck_free_dims(k, t.term) | ck_free_dims(k, t.type));
        if (fresh >= CC_DIMENSIONS)
            return 0;
        cc_formula point;
        cc_init(&point, CC_INTERVAL);
        cc_formula_id argument = ck_formula_result(k, cc_generator(&point, fresh, true), "Interval allocation failed.")
            ? ck_formula(k, &point) : 0;
        cc_term family = argument ? ck_dimension_substitute(k, type.child[0], type.payload, &point) : 0;
        cc_clear(&point);
        if (!family)
            return 0;
        expanded = ck_instr_make(k, CC_PLAM, fresh, family, ck_instr_make(k, CC_PAPP, argument, t.term, t.type, 0, 0), 0, 0);
    } else if (type.kind == CC_GLUE) {
        cc_term pieces = eta_pieces(k, type.child[1], t.term);
        if (k->error[0])
            return 0;
        expanded = ck_instr_make(k, CC_GLUE_TERM, 0, t.type, ck_instr_make(k, CC_UNGLUE, 0, t.type, t.term, 0, 0), pieces, 0);
    } else {
        return ck_fail(k, "Eta needs a term of a Π, level Π, Σ, path or Glue type."), 0;
    }
    return ck_instr_publish(k, CC_FACT_EQUALITY, t.term, expanded, t.type, t.context);
}

/* ---- Positions ---------------------------------------------------------- */

/* A node on the way down to a highlighted subterm, and the child taken. */
typedef struct {
    cc_node node;
    unsigned child;
} crossing;

/* Whether a child is under the node's binder: 1 for a term binder, 2 for a
 * dimension binder, 3 for a composition's tubes, where only terms are bound. */
static unsigned bound_under(cc_term_kind kind, unsigned child) {
    if (ck_term_binder(kind)) return child == 1 ? 1 : 0;
    if (kind == CC_PLAM) return 2;
    if (kind == CC_PATH || kind == CC_TRANS) return child == 0 ? 2 : 0;
    if (kind == CC_COMP) return child == 0 ? 2 : child == 1 ? 3 : 0;
    if (kind == CC_HCOMP) return child == 1 ? 3 : 0;
    return 0;
}

static cc_term locate(cc_kernel *k, cc_term term, const uint8_t *position, size_t depth, crossing *crossed) {
    if (depth && !position)
        return ck_fail(k, "Missing position."), 0;
    for (size_t i = 0; i < depth; ++i) {
        cc_node n = k->nodes[term];
        unsigned child = position[i];
        if (child >= ck_arity(n.kind) || !n.child[child])
            return ck_fail(k, "The position leaves the term."), 0;
        if (crossed)
            crossed[i] = (crossing){n, child};
        term = n.child[child];
    }
    return term;
}

static cc_term rebuild(cc_kernel *k, cc_term term, const uint8_t *position, size_t depth, cc_term replacement) {
    if (!depth || !replacement)
        return replacement;
    if (!ck_enter(k, "Position depth exceeded."))
        return 0;
    cc_node n = k->nodes[term];
    n.child[position[0]] = rebuild(k, n.child[position[0]], position + 1, depth - 1, replacement);
    ck_leave(k);
    if (!n.child[position[0]])
        return 0;
    return ck_instr_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], n.child[3]);
}

static bool interval_constant(const cc_formula *f, unsigned *endpoint) {
    if (!f->length) { *endpoint = 0; return true; }
    if (f->length == 1 && !f->clauses[0].positive && !f->clauses[0].negative) { *endpoint = 1; return true; }
    return false;
}

/* One contraction at the highlighted node, or zero with an error. */
static cc_term contract(cc_kernel *k, cc_term term, cc_step_rule rule) {
    cc_node n = k->nodes[term];
    switch (rule) {
    case CC_STEP_BETA:
        if (n.kind == CC_APP && k->nodes[n.child[0]].kind == CC_LAM) {
            cc_node lambda = k->nodes[n.child[0]];
            return ck_instantiate(k, lambda.child[1], n.child[1]);
        }
        if (n.kind == CC_LAPP && k->nodes[n.child[0]].kind == CC_LLAM) {
            cc_node lambda = k->nodes[n.child[0]];
            return ck_level_instantiate(k, lambda.child[1], n.child[1]);
        }
        return ck_fail(k, "Beta needs a lambda applied to an argument, or a level lambda to a level."), 0;
    case CC_STEP_DELTA:
        if (n.kind == CC_DEFREF && n.payload && n.payload < k->definition_count)
            return k->definitions[n.payload].value;
        return ck_fail(k, "Delta needs a definition."), 0;
    case CC_STEP_IOTA: {
        cc_node head;
        switch (n.kind) {
        case CC_SUMREC:
            head = k->nodes[n.child[3]];
            if (head.kind == CC_INL || head.kind == CC_INR)
                return ck_instr_app(k, n.child[head.kind == CC_INL ? 1 : 2], head.child[1]);
            break;
        case CC_UNITREC:
            if (k->nodes[n.child[2]].kind == CC_POINT)
                return n.child[1];
            break;
        case CC_FST: case CC_SND:
            head = k->nodes[n.child[0]];
            if (head.kind == CC_PAIR)
                return head.child[n.kind == CC_FST ? 1 : 2];
            break;
        case CC_APP: {
            /* A declared type's eliminator on a constructor, at dimensions
             * or not (3.7). */
            if (k->nodes[n.child[0]].kind == CC_ELIM) {
                bool reduced = false;
                cc_term result = ck_eliminate(k, n.child[0], n.child[1], false, &reduced);
                if (reduced || !result)
                    return result;
            }
            break;
        }
        default:
            break;
        }
        return ck_fail(k, "Iota needs an eliminator or projection applied to a constructor."), 0;
    }
    case CC_STEP_PATH: {
        const cc_formula *argument = n.kind == CC_PAPP ? cc_kernel_get_formula(k, n.payload) : NULL;
        if (!argument)
            return ck_fail(k, "A path step needs a path application."), 0;
        cc_node path = k->nodes[n.child[0]];
        if (path.kind == CC_PLAM) {
            cc_formula point;
            cc_init(&point, CC_INTERVAL);
            if (!ck_formula_result(k, cc_copy(&point, argument), "Interval copy failed."))
                return 0;
            cc_term result = ck_dimension_substitute(k, path.child[1], path.payload, &point);
            cc_clear(&point);
            return result;
        }
        unsigned endpoint;
        cc_node type = n.child[1] ? k->nodes[n.child[1]] : (cc_node){0};
        if (type.kind == CC_PATH && interval_constant(argument, &endpoint))
            return type.child[endpoint ? 2 : 1];
        return ck_fail(k, "A path step needs a path lambda, or an endpoint of the annotated type."), 0;
    }
    case CC_STEP_NORMALIZE:
        return ck_normal(k, term);
    case CC_STEP_WHNF:
        return ck_whnf(k, term);
    case CC_STEP_FACE:
        /* comp^i A [1 ↦ u, …] a0 is u(1), and so is hcomp: the first rule of
         * the term checker's composition reduction, alone. */
        if (n.kind == CC_COMP || n.kind == CC_HCOMP) {
            for (cc_term cursor = n.child[1]; cursor; cursor = k->nodes[cursor].child[1]) {
                cc_node tube = k->nodes[cursor];
                const cc_formula *face = cc_kernel_get_formula(k, tube.payload);
                if (face && face->sort == CC_FACE && face->length == 1 && !face->clauses[0].positive &&
                    !face->clauses[0].negative)
                    return ck_endpoint_term(k, tube.child[0], n.payload, 1);
            }
        }
        if (n.kind == CC_TRANS && n.child[1]) {
            const cc_formula *face = cc_kernel_get_formula(k, k->nodes[n.child[1]].payload);
            if (face && face->length == 1 && !face->clauses[0].positive && !face->clauses[0].negative)
                return n.child[2];
        }
        return ck_fail(k, "A face step needs a composition with a tube on a face that holds."), 0;
    case CC_STEP_GLUE: {
        /* Glue eta where a piece is the base's restriction only after
         * reduction, which Whnf leaves: the side conditions normalized, and
         * nothing else (term_normalize.c). */
        cc_term base = n.kind == CC_GLUE_TERM ? ck_glue_step(k, term) : term;
        if (!base || base != term)
            return base;
        return ck_fail(k, "A Glue step needs glue [φ ↦ t] (unglue b) whose two Glue types agree, and whose t is b on φ, "
                          "after normalization."), 0;
    }
    case CC_STEP_SPLIT:
        if (n.kind == CC_COMP || n.kind == CC_HCOMP) {
            cc_term system = ck_clause_tubes(k, n.child[1], true);
            if (k->error[0])
                return 0;
            if (system != n.child[1])
                return ck_make(k, n.kind, n.payload, n.child[0], system, n.child[2], n.child[3]);
        }
        return ck_fail(k, "A split step needs a composition with a tube on a face of several clauses, or on the face 0."), 0;
    }
    return ck_fail(k, "Unknown step rule."), 0;
}

/* The sides of a judgement: 0 its term, 1 the other side of an equality,
 * 2 its type. Rewriting any side by a definitional equality keeps the
 * judgement valid: a term by subject reduction, a type because a reduct
 * (or a convertible, well-typed replacement) of a type is a type. */
static bool judgement(cc_kernel *k, cc_judgement_id id, unsigned side, cc_fact *out, cc_term *root) {
    if (!id || id >= k->fact_count)
        return ck_fail(k, "Unknown judgement.");
    *out = k->facts[id];
    if (out->kind == CC_FACT_SYSTEM)
        return ck_fail(k, "A composition system is closed by Comp before it is rewritten.");
    /* A declared type's judgements in progress carry state that only their
     * own instructions advance: a rewritten copy would not. */
    if (out->kind != CC_FACT_TYPING && out->kind != CC_FACT_EQUALITY)
        return ck_fail(k, "An open signature or an instance in progress is continued by its own instructions, "
                          "not rewritten.");
    if (side > 2 || (side == 1 && out->kind != CC_FACT_EQUALITY))
        return ck_fail(k, "A judgement has sides 0 (term), 2 (type), and 1 for an equality's other term.");
    *root = side == 0 ? out->term : side == 1 ? out->other : out->type;
    return true;
}

static cc_judgement_id republish(cc_kernel *k, cc_fact f, unsigned side, cc_term changed, uint32_t context) {
    if (side == 0) f.term = changed;
    else if (side == 1) f.other = changed;
    else f.type = changed;
    return ck_instr_publish(k, f.kind, f.term, f.other, f.type, context);
}

cc_judgement_id cc_instr_step(cc_kernel *k, cc_judgement_id id, unsigned side,
                              const uint8_t *position, size_t depth, cc_step_rule rule) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_STEP, .premise = {id}, .operand = {side, rule}}, position, depth, &found))
        return found;
    cc_fact e = {0};
    cc_term root = 0;
    if (!judgement(k, id, side, &e, &root))
        return 0;
    cc_term target = locate(k, root, position, depth, NULL);
    if (!target)
        return 0;
    /* Under binders, the target's loose indices are opened with CC_OPENED
     * levels, one for each binder it uses: its judgement holds no opened
     * level, so they take 0, 1, …, the outermost first. The contraction is
     * closed back over the same indices (section 3.3). */
    uint32_t loose = k->nodes[target].loose;
    cc_term opened = ck_open_loose(k, target, 0);
    cc_term contracted = opened ? contract(k, opened, rule) : 0;
    cc_term closed = contracted ? ck_close_loose(k, contracted, 0, loose) : 0;
    cc_term changed = closed ? rebuild(k, root, position, depth, closed) : 0;
    if (!changed)
        return 0;
    return republish(k, e, side, changed, e.context);
}

/* A term whose free dimensions matter at a depth of the path: the two sides
 * of the replacing equality at the bottom, and the type of each entry the
 * caller supplied at its binder, where it is that binder's domain. */
typedef struct {
    cc_term term;
    size_t depth;
} scoped_term;

/* Whether a dimension binder below `from` and above `to` binds the same
 * dimension again. */
static bool shadowed(const crossing *crossed, size_t from, size_t to, uint32_t name) {
    for (size_t m = from + 1; m < to; ++m) {
        unsigned kind = bound_under(crossed[m].node.kind, crossed[m].child);
        if ((kind == 2 || kind == 3) && crossed[m].node.payload == name)
            return true;
    }
    return false;
}

/* Whether the dimension a dimension binder on the path binds is free in a
 * term below it. */
static bool needed(cc_kernel *k, const crossing *crossed, size_t at, const scoped_term *terms, size_t count) {
    uint32_t name = crossed[at].node.payload;
    for (size_t t = 0; t < count; ++t) {
        if (terms[t].depth <= at || shadowed(crossed, at, terms[t].depth, name))
            continue;
        if (name < CC_DIMENSIONS && (ck_free_dims(k, terms[t].term) & (UINT64_C(1) << name)))
            return true;
    }
    return false;
}

static cc_entry_id dimension_entry(const cc_kernel *k, uint32_t set, uint32_t index) {
    cc_context_set s = k->context_sets[set];
    for (uint32_t i = 0; i < s.count; ++i) {
        cc_entry_id id = k->context_items[s.offset + i];
        if (k->entries[id].dimension && k->entries[id].index == index)
            return id;
    }
    return 0;
}

static bool in_context(const cc_kernel *k, uint32_t set, cc_entry_id id) {
    cc_context_set s = k->context_sets[set];
    for (uint32_t i = 0; i < s.count; ++i)
        if (k->context_items[s.offset + i] == id)
            return true;
    return false;
}

/* Whether an entry of `set` other than the given ones depends on one of
 * them: is one of them in its own context. */
static bool keeps_dependent(const cc_kernel *k, uint32_t set, const cc_entry_id *entries, size_t count) {
    cc_context_set s = k->context_sets[set];
    for (uint32_t i = 0; i < s.count; ++i) {
        cc_entry_id kept = k->context_items[s.offset + i];
        bool given = false;
        for (size_t b = 0; b < count && !given; ++b)
            given = entries[b] == kept;
        for (size_t b = 0; b < count && !given; ++b)
            if (entries[b] && in_context(k, k->entries[kept].context, entries[b]))
                return true;
    }
    return false;
}

/* The entries of a replacement (section 3.6): for each term or level binder
 * the position crosses, outermost first, an entry or 0. Each given entry is
 * of its binder's kind, new to the rewritten judgement's context, given once,
 * and at its binder's domain opened with the entries outside it. `values`
 * receives what opens each binder: its entry's CC_CONTEXT, or for a binder
 * given none a placeholder, CC_OPENED of the binder's ordinal, which no
 * judgement holds, so that a term that still uses that binder is known in
 * O(1) by its `opened`. */
static bool binder_entries(cc_kernel *k, const crossing *crossed, size_t depth, const cc_entry_id *entries,
                           size_t count, uint32_t rewritten, cc_term *values, scoped_term *terms, size_t *scoped) {
    size_t binders = 0;
    for (size_t at = 0; at < depth; ++at)
        binders += bound_under(crossed[at].node.kind, crossed[at].child) == 1;
    if (count != binders)
        return ck_fail(k, "A replacement takes an entry, or 0, for each term or level binder its position crosses.");
    for (size_t at = 0, b = 0; at < depth; ++at) {
        if (bound_under(crossed[at].node.kind, crossed[at].child) != 1)
            continue;
        cc_entry_id id = entries[b];
        if (!id) {
            values[b] = ck_make(k, CC_OPENED, (uint32_t)b, 0, 0, 0, 0);
            if (!values[b])
                return false;
            ++b;
            continue;
        }
        bool level = crossed[at].node.kind == CC_LPI || crossed[at].node.kind == CC_LLAM;
        if (id >= k->entry_count || k->entries[id].face || k->entries[id].dimension ||
            k->entries[id].level_variable != level)
            return ck_fail(k, "A replacement takes a level entry for a level binder, and a term entry for a term binder.");
        for (size_t other = 0; other < b; ++other)
            if (entries[other] == id)
                return ck_fail(k, "A replacement gives one entry to two of its binders.");
        if (in_context(k, rewritten, id))
            return ck_fail(k, "A replacement's entry for a binder is already in the rewritten judgement's context.");
        /* The domain, under the binders outside it, opened with what opens
         * them: the innermost of those is index 0. */
        cc_term outer[1024] = {0};
        for (size_t m = 0; m < b; ++m)
            outer[m] = values[b - 1 - m];
        cc_term domain = ck_instantiate_all(k, crossed[at].node.child[0], outer, (uint32_t)b);
        if (!domain)
            return false;
        if (k->nodes[domain].opened)
            return ck_fail(k, "A replacement's entry for a binder has a type that needs an outer binder given no entry.");
        if (!ck_instr_same(k, k->entries[id].type, domain, "A replacement's entry for a binder is not at the binder's domain."))
            return false;
        values[b] = ck_make(k, CC_CONTEXT, id, 0, 0, 0, 0);
        if (!values[b])
            return false;
        terms[(*scoped)++] = (scoped_term){k->entries[id].type, at};
        ++b;
    }
    return true;
}

/* The binder entries are part of the derivation (section 3.7): the same
 * replacement with other entries is another derivation. */
cc_judgement_id cc_instr_replace(cc_kernel *k, cc_judgement_id id, unsigned side,
                                 const uint8_t *position, size_t depth, cc_judgement_id by,
                                 const cc_entry_id *entries, size_t count) {
    cc_judgement_id found;
    if (!ck_instr_begin_entries(k, (cc_derivation){.rule = CC_INSTR_REPLACE, .premise = {id, by}, .operand = {side}},
                                position, depth, entries, count, &found))
        return found;
    cc_fact e = {0}, inner = {0};
    cc_term root = 0;
    if (!judgement(k, id, side, &e, &root) || !ck_instr_premise(k, by, CC_FACT_EQUALITY, &inner))
        return 0;
    crossing *crossed = depth ? malloc(depth * sizeof *crossed) : NULL;
    scoped_term *terms = malloc((2 * depth + 2) * sizeof *terms);
    cc_entry_id *removed = depth ? malloc(depth * sizeof *removed) : NULL;
    cc_term *values = depth ? malloc(depth * sizeof *values) : NULL;
    cc_judgement_id result = 0;
    if ((depth && (!crossed || !removed || !values)) || !terms) {
        ck_fail_as(k, CC_ERROR_RESOURCE, "Replacement allocation failed.");
        goto done;
    }
    cc_term target = locate(k, root, position, depth, crossed);
    if (!target)
        goto done;
    /* The entries for the binders crossed, checked, and the target opened
     * with them: a binder it uses must have one. */
    size_t count_scoped = 2, discharged = 0;
    terms[0] = (scoped_term){inner.term, depth};
    terms[1] = (scoped_term){inner.other, depth};
    if (!binder_entries(k, crossed, depth, entries, count, e.context, values, terms, &count_scoped))
        goto done;
    {
        cc_term reversed[1024] = {0};
        for (size_t b = 0; b < count; ++b)
            reversed[b] = values[count - 1 - b];
        target = ck_instantiate_all(k, target, reversed, (uint32_t)count);
    }
    if (!target)
        goto done;
    if (k->nodes[target].opened) {
        ck_fail(k, "A replacement gives no entry to a binder its occurrence uses.");
        goto done;
    }
    if (!ck_instr_same(k, target, inner.term, "The highlighted subterm is not the equality's left side."))
        goto done;
    /* A path application's annotation is the path type its endpoints are
     * read from (boundary reduction included): it stays one. */
    if (depth && crossed[depth - 1].node.kind == CC_PAPP && crossed[depth - 1].child == 1 &&
        k->nodes[inner.other].kind != CC_PATH) {
        ck_fail(k, "A path application's annotation is replaced only by a path type.");
        goto done;
    }
    /* The entries given are discharged. From the innermost binder out, a
     * dimension binder whose dimension the replacement or an entry's type
     * uses must correspond to a dimension entry of the replacing equality,
     * which is discharged too. */
    for (size_t b = 0; b < count; ++b)
        if (entries[b])
            removed[discharged++] = entries[b];
    for (size_t at = depth; at-- > 0;) {
        unsigned kind = bound_under(crossed[at].node.kind, crossed[at].child);
        if (kind < 2 || !needed(k, crossed, at, terms, count_scoped))
            continue;
        if (kind == 3) {
            ck_fail(k, "Replacing a subterm that uses a composition's dimension is not supported.");
            goto done;
        }
        cc_entry_id dimension = dimension_entry(k, inner.context, crossed[at].node.payload);
        if (!dimension) {
            ck_fail(k, "The replacing equality lacks an entry for a bound name it uses.");
            goto done;
        }
        for (size_t r = 0; r < discharged; ++r)
            if (removed[r] == dimension) {
                ck_fail(k, "One entry would be bound twice on the path.");
                goto done;
            }
        removed[discharged++] = dimension;
    }
    /* The replacement, with the entries given abstracted: the innermost
     * binder's is index 0 at the position. */
    cc_term replacement = inner.other;
    for (size_t b = count; b-- > 0 && replacement;)
        if (entries[b])
            replacement = ck_abstract_at(k, replacement, entries[b], (uint32_t)(count - 1 - b));
    if (!replacement)
        goto done;
    /* No entry the equality keeps may depend on a binder's entry, which it
     * discharges (section 3.6, condition 5). */
    if (keeps_dependent(k, inner.context, entries, count)) {
        ck_fail(k, "A replacement's equality keeps an entry that depends on a binder's entry.");
        goto done;
    }
    uint32_t context = 0;
    cc_term changed = rebuild(k, root, position, depth, replacement);
    if (!changed || !ck_instr_discharge(k, inner.context, removed, discharged, &context) || !ck_instr_merge(k, e.context, context, &context))
        goto done;
    result = republish(k, e, side, changed, context);
done:
    free(crossed);
    free(terms);
    free(removed);
    free(values);
    return result;
}
