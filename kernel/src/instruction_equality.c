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
    if (type.kind == CC_PI) {
        uint32_t name = ck_fresh_symbol(k);
        expanded = ck_instr_make(k, CC_LAM, name, type.child[0], ck_instr_app(k, t.term, ck_var(k, name)), 0, 0);
    } else if (type.kind == CC_LPI) {
        uint32_t name = ck_fresh_symbol(k);
        expanded = ck_instr_make(k, CC_LLAM, name, type.child[0], ck_instr_make(k, CC_LAPP, 0, t.term, ck_var(k, name), 0, 0), 0, 0);
    } else if (type.kind == CC_SIGMA) {
        expanded = ck_instr_make(k, CC_PAIR, 0, t.type, ck_instr_make(k, CC_FST, 0, t.term, 0, 0, 0), ck_instr_make(k, CC_SND, 0, t.term, 0, 0, 0), 0);
    } else if (type.kind == CC_PATH) {
        unsigned fresh = ck_fresh_dimension(k, ck_free_dims(k, t.term) | ck_free_dims(k, t.type));
        if (fresh >= CC_DIMENSIONS)
            return 0;
        cc_formula point;
        cc_init(&point, CC_INTERVAL);
        cc_formula_id argument = cc_generator(&point, fresh, true) == CC_OK ? ck_formula(k, &point) : 0;
        cc_term family = argument ? ck_dimension_substitute(k, type.child[0], type.payload, &point) : 0;
        cc_clear(&point);
        if (!family)
            return ck_fail(k, "Interval allocation failed."), 0;
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
    if (++k->recursion > 1024)
        return ck_fail(k, "Position depth exceeded."), 0;
    cc_node n = k->nodes[term];
    n.child[position[0]] = rebuild(k, n.child[position[0]], position + 1, depth - 1, replacement);
    --k->recursion;
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
            return ck_substitute(k, lambda.child[1], lambda.payload, n.child[1]);
        }
        if (n.kind == CC_LAPP && k->nodes[n.child[0]].kind == CC_LLAM) {
            cc_node lambda = k->nodes[n.child[0]];
            return ck_level_instantiate(k, lambda.child[1], lambda.payload, n.child[1]);
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
            if (cc_copy(&point, argument) != CC_OK)
                return ck_fail(k, "Interval copy failed."), 0;
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
    cc_term changed = target ? rebuild(k, root, position, depth, contract(k, target, rule)) : 0;
    if (!changed)
        return 0;
    return republish(k, e, side, changed, e.context);
}

/* A term whose free names matter at a depth of the path: the two sides of
 * the replacing equality at the bottom, and the type of each discharged
 * entry at its binder, where it is that binder's domain. */
typedef struct {
    cc_term term;
    size_t depth;
} scoped_term;

static bool shadowed(const crossing *crossed, size_t from, size_t to, unsigned kind, uint32_t name) {
    for (size_t m = from + 1; m < to; ++m)
        if (bound_under(crossed[m].node.kind, crossed[m].child) == kind && crossed[m].node.payload == name)
            return true;
    return false;
}

static bool needed(cc_kernel *k, const crossing *crossed, size_t at, const scoped_term *terms, size_t count) {
    unsigned kind = bound_under(crossed[at].node.kind, crossed[at].child);
    uint32_t name = crossed[at].node.payload;
    for (size_t t = 0; t < count; ++t) {
        if (terms[t].depth <= at || shadowed(crossed, at, terms[t].depth, kind == 3 ? 2 : kind, name))
            continue;
        bool free = kind == 1 ? ck_term_free(k, terms[t].term, name)
                              : name < CC_DIMENSIONS && (ck_free_dims(k, terms[t].term) & (UINT64_C(1) << name));
        if (free)
            return true;
    }
    return false;
}

static cc_entry_id context_entry(const cc_kernel *k, uint32_t set, uint32_t symbol, bool dimension) {
    cc_context_set s = k->context_sets[set];
    for (uint32_t i = 0; i < s.count; ++i) {
        cc_entry_id id = k->context_items[s.offset + i];
        if (k->entries[id].dimension == dimension && k->entries[id].symbol == symbol)
            return id;
    }
    return 0;
}

cc_judgement_id cc_instr_replace(cc_kernel *k, cc_judgement_id id, unsigned side,
                                 const uint8_t *position, size_t depth, cc_judgement_id by) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_REPLACE, .premise = {id, by}, .operand = {side}}, position, depth, &found))
        return found;
    cc_fact e = {0}, inner = {0};
    cc_term root = 0;
    if (!judgement(k, id, side, &e, &root) || !ck_instr_premise(k, by, CC_FACT_EQUALITY, &inner))
        return 0;
    crossing *crossed = depth ? malloc(depth * sizeof *crossed) : NULL;
    scoped_term *terms = malloc((depth + 2) * sizeof *terms);
    cc_entry_id *removed = depth ? malloc(depth * sizeof *removed) : NULL;
    cc_judgement_id result = 0;
    if ((depth && (!crossed || !removed)) || !terms) {
        ck_fail(k, "Replacement allocation failed.");
        goto done;
    }
    cc_term target = locate(k, root, position, depth, crossed);
    if (!target || !ck_instr_same(k, target, inner.term, "The highlighted subterm is not the equality's left side."))
        goto done;
    /* A path application's annotation is the path type its endpoints are
     * read from (boundary reduction included): it stays one. */
    if (depth && crossed[depth - 1].node.kind == CC_PAPP && crossed[depth - 1].child == 1 &&
        k->nodes[inner.other].kind != CC_PATH) {
        ck_fail(k, "A path application's annotation is replaced only by a path type.");
        goto done;
    }
    /* From the innermost binder out: a binder whose name the replacement
     * uses must correspond to an entry of the replacing equality with the
     * binder's type; that entry is discharged, and its type's names are in
     * turn looked up further out. */
    size_t count = 2, discharged = 0;
    terms[0] = (scoped_term){inner.term, depth};
    terms[1] = (scoped_term){inner.other, depth};
    for (size_t at = depth; at-- > 0;) {
        unsigned kind = bound_under(crossed[at].node.kind, crossed[at].child);
        if (!kind || !needed(k, crossed, at, terms, count))
            continue;
        if (kind == 3) {
            ck_fail(k, "Replacing a subterm that uses a composition's dimension is not supported.");
            goto done;
        }
        cc_entry_id id = context_entry(k, inner.context, crossed[at].node.payload, kind == 2);
        if (!id) {
            ck_fail(k, "The replacing equality lacks an entry for a bound name it uses.");
            goto done;
        }
        for (size_t r = 0; r < discharged; ++r)
            if (removed[r] == id) {
                ck_fail(k, "One entry would be bound twice on the path.");
                goto done;
            }
        if (kind == 1) {
            if (!ck_instr_same(k, k->entries[id].type, crossed[at].node.child[0], "The entry and the binder have different types."))
                goto done;
            terms[count++] = (scoped_term){k->entries[id].type, at};
        }
        removed[discharged++] = id;
    }
    uint32_t context = 0;
    cc_term changed = rebuild(k, root, position, depth, inner.other);
    if (!changed || !ck_instr_discharge(k, inner.context, removed, discharged, &context) || !ck_instr_merge(k, e.context, context, &context))
        goto done;
    result = republish(k, e, side, changed, context);
done:
    free(crossed);
    free(terms);
    free(removed);
    return result;
}
