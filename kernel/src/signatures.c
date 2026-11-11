/* Declared types (H1): the signature table and the admission instructions,
 * families F1 and F6 of docs/roadmaps/hott/h1-signature-specification.md
 * (section 5). A signature is admitted one constructor at a time. Every check
 * is syntactic, on terms as written, as every instruction's is: the normal
 * form of sections 1.1-1.6, strict positivity by construction, and the
 * classification of universe parameters into erased and recorded ones.
 *
 * The admission telescope is the universe parameters, the term parameters,
 * the sort and the constructors. While a signature is open, an entry the
 * caller supplies stands for each, typed and kept apart as section 3.6 of
 * docs/roadmaps/kernel/locally-nameless-kernel.md requires. A constructor
 * type is derived by ordinary instructions in a context of those entries, so
 * the kernel checks here only that the context is the signature's and that
 * the type has the normal form, and stores it closed over the telescope.
 * Nothing here reduces a term. */
#include "term_internal.h"

static bool fail(cc_kernel *k, const char *message) { return ck_fail(k, message); }

static cc_node node(const cc_kernel *k, cc_term t) { return k->nodes[t]; }

/* ---- The extension gate (F6) --------------------------------------------- */

void cc_kernel_set_extensions(cc_kernel *k, unsigned flags) {
    if (k) k->extensions = flags & CC_EXTENSION_H1;
}

unsigned cc_kernel_extensions(const cc_kernel *k) { return k ? k->extensions : 0; }

/* ---- The table ------------------------------------------------------------ */

static void release(cc_signature *s) {
    free(s->entries);
    free(s->parameter_types);
    free(s->constructors);
    *s = (cc_signature){0};
}

void ck_signatures_free(cc_kernel *k) {
    for (size_t i = 1; i < k->signature_count; ++i)
        release(&k->signatures[i]);
    free(k->signatures);
    k->signatures = NULL;
    k->signature_count = k->signature_capacity = 0;
}

void ck_signatures_checkpoint(cc_kernel *k) {
    k->checkpoint_signatures = k->signature_count;
    for (size_t i = 1; i < k->signature_count; ++i) {
        k->signatures[i].checkpoint_constructors = k->signatures[i].constructor_count;
        k->signatures[i].checkpoint_admitted = k->signatures[i].admitted;
    }
}

/* Signatures opened since the checkpoint go; one opened before it returns to
 * its state then, since the constructors and closing since refer to syntax
 * that the rollback discards. */
void ck_signatures_rollback(cc_kernel *k) {
    if (!k->checkpoint_signatures)
        return;
    for (size_t i = k->checkpoint_signatures; i < k->signature_count; ++i)
        release(&k->signatures[i]);
    k->signature_count = k->checkpoint_signatures;
    for (size_t i = 1; i < k->signature_count; ++i) {
        k->signatures[i].constructor_count = k->signatures[i].checkpoint_constructors;
        k->signatures[i].admitted = k->signatures[i].checkpoint_admitted;
    }
}

/* Whether a signature was opened or extended since the checkpoint and is
 * still open: its latest judgement is one that a commit truncates. One left
 * open from before the checkpoint, and untouched since, keeps its judgement. */
bool ck_signatures_open(const cc_kernel *k) {
    for (size_t i = 1; i < k->signature_count; ++i) {
        const cc_signature *s = &k->signatures[i];
        if (!s->admitted && (i >= k->checkpoint_signatures || s->constructor_count != s->checkpoint_constructors))
            return true;
    }
    return false;
}

static cc_signature *new_signature(cc_kernel *k, uint32_t *index) {
    if (!k->signature_count)
        k->signature_count = 1;
    if (k->signature_count >= UINT32_MAX)
        return ck_fail_as(k, CC_ERROR_RESOURCE, "Signature table exhausted."), NULL;
    if (k->signature_count == k->signature_capacity || !k->signatures) {
        size_t next = k->signature_capacity ? 2 * k->signature_capacity : 16;
        cc_signature *grown = realloc(k->signatures, next * sizeof *grown);
        if (!grown)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Signature table allocation failed."), NULL;
        k->signatures = grown;
        k->signature_capacity = next;
    }
    *index = (uint32_t)k->signature_count;
    cc_signature *s = &k->signatures[k->signature_count++];
    *s = (cc_signature){0};
    return s;
}

static bool add_constructor(cc_kernel *k, cc_signature *s, cc_constructor c) {
    if (s->constructor_count >= CC_SIGNATURE_CONSTRUCTORS)
        return ck_fail_as(k, CC_ERROR_RESOURCE, "A signature has too many constructors.");
    if (s->constructor_count == s->constructor_capacity) {
        uint32_t next = s->constructor_capacity ? 2 * s->constructor_capacity : 8;
        cc_constructor *grown = realloc(s->constructors, next * sizeof *grown);
        if (!grown)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Constructor table allocation failed.");
        s->constructors = grown;
        s->constructor_capacity = next;
    }
    s->constructors[s->constructor_count++] = c;
    return true;
}


/* ---- The normal form (sections 1.2-1.5) ---------------------------------- */

/* A constructor type is checked as derived, over the admission entries: the
 * sort, the earlier constructors and the parameters are CC_CONTEXT of their
 * entries, and the constructor's own arguments are its Π binders' indices.
 * A position is known by its argument's de Bruijn level, the number of
 * arguments before it, and records its arity length, so that a boundary
 * applies each to exactly its arity. `binders` is the number of term
 * binders between the constructor type's root and the term at hand. */
typedef struct {
    cc_kernel *k;
    const cc_signature *signature;
    uint32_t constructors;             /* the earlier constructors: 0 .. constructors - 1 */
    cc_entry_id self;                  /* the new constructor's entry, or 0 */
    uint32_t position_levels[CC_CONSTRUCTOR_ARGUMENTS], position_arities[CC_CONSTRUCTOR_ARGUMENTS];
    uint32_t positions;
} shape;

/* Whether a node, met under `binders` binders, is a position's variable. */
static bool is_position(const shape *sh, cc_node n, uint32_t binders, uint32_t *arity) {
    if (n.kind != CC_BOUND || n.payload >= binders)
        return false;
    uint32_t level = binders - 1 - n.payload;
    for (uint32_t i = 0; i < sh->positions; ++i)
        if (sh->position_levels[i] == level) { if (arity) *arity = sh->position_arities[i]; return true; }
    return false;
}

static bool is_constructor(const shape *sh, cc_node n, uint32_t *which) {
    if (n.kind != CC_CONTEXT)
        return false;
    for (uint32_t i = 0; i < sh->constructors; ++i)
        if (sh->signature->constructors[i].entry == n.payload) { if (which) *which = i; return true; }
    return false;
}

static bool is_sort(const shape *sh, cc_node n) {
    return n.kind == CC_CONTEXT && n.payload == sh->signature->sort_entry;
}

/* Whether t, under `binders` binders, mentions the sort, an earlier
 * constructor or a position: the names a data type, an arity and a data
 * term may not mention. */
static bool mentions(shape *sh, cc_term t, uint32_t binders) {
    cc_kernel *k = sh->k;
    if (ck_mentions(k, t, sh->signature->sort_entry))
        return true;
    for (uint32_t i = 0; i < sh->constructors; ++i)
        if (ck_mentions(k, t, sh->signature->constructors[i].entry)) return true;
    for (uint32_t i = 0; i < sh->positions; ++i)
        if (ck_index_occurs(k, t, binders - 1 - sh->position_levels[i])) return true;
    return false;
}

static bool endpoint(shape *sh, cc_term e, unsigned depth, uint32_t binders);
static bool cube(shape *sh, cc_term c, uint32_t *dimensions, unsigned guard, unsigned nesting, uint32_t binders);

/* E' ::= E | λ (y : A). E', a positional argument under its arity's binders. */
static bool positional(shape *sh, cc_term e, unsigned depth, uint32_t binders) {
    cc_kernel *k = sh->k;
    if (depth > 256)
        return ck_fail_as(k, CC_ERROR_RESOURCE, "A boundary is nested too deeply.");
    cc_node n = node(k, e);
    if (n.kind != CC_LAM)
        return endpoint(sh, e, depth + 1, binders);
    if (mentions(sh, n.child[0], binders))
        return fail(k, "A binder's type in a boundary mentions the sort, a constructor or a position (section 1.4).");
    return positional(sh, n.child[1], depth + 1, binders + 1);
}

/* A type a boundary carries: a path abstraction's family or a path
 * application's annotation, which must be a cube over the sort. */
static bool carried(shape *sh, cc_term type, unsigned depth, uint32_t binders) {
    cc_kernel *k = sh->k;
    if (!type)
        return true;
    cc_term end = type;
    for (unsigned guard = 0; node(k, end).kind == CC_PATH && guard <= CC_CONSTRUCTOR_DIMENSIONS; ++guard)
        end = node(k, end).child[0];
    if (!is_sort(sh, node(k, end)))
        return fail(k, "A path abstraction or application in a boundary carries a type that is not a cube over the "
                       "sort (section 1.4).");
    uint32_t ignored = 0;
    return cube(sh, type, &ignored, 0, depth, binders);
}

static bool data_term(shape *sh, cc_term t, uint32_t binders) {
    if (mentions(sh, t, binders))
        return fail(sh->k, "A boundary applies a position or constructor to data terms only: terms that mention "
                           "no sort, constructor or position (section 1.4).");
    return true;
}

/* E ::= q_j(us) | c_m(us, Es') | E @ r | ⟨i⟩ E: constructor expressions over
 * the positions and the earlier constructors. No composition, transport or
 * other operation of the sort occurs (Q3), in the expression or in the types
 * it carries: a path abstraction's family and a path application's
 * annotation, whose endpoints the path step exposes, are cubes as well. */
static bool endpoint(shape *sh, cc_term e, unsigned depth, uint32_t binders) {
    cc_kernel *k = sh->k;
    if (depth > 256)
        return ck_fail_as(k, CC_ERROR_RESOURCE, "A boundary is nested too deeply.");
    if (!ck_tick(k))
        return false;
    cc_node n = node(k, e);
    if (n.kind == CC_PLAM)
        return carried(sh, n.child[0], depth + 1, binders) && endpoint(sh, n.child[1], depth + 1, binders);
    if (n.kind == CC_PAPP)
        return carried(sh, n.child[1], depth + 1, binders) && endpoint(sh, n.child[0], depth + 1, binders);
    if (n.kind == CC_COMP || n.kind == CC_HCOMP || n.kind == CC_TRANS)
        return fail(k, "A boundary may not contain a composition, hcomp or transport (section 1.4, Q3).");
    cc_term arguments[CC_CONSTRUCTOR_ARGUMENTS];
    uint32_t count = 0;
    cc_term head = e;
    while (node(k, head).kind == CC_APP) {
        if (count == CC_CONSTRUCTOR_ARGUMENTS)
            return fail(k, "A boundary applies a constructor to too many arguments.");
        arguments[count++] = node(k, head).child[1];
        head = node(k, head).child[0];
    }
    cc_node h = node(k, head);
    uint32_t arity = 0, which = 0;
    if (is_position(sh, h, binders, &arity)) {
        if (count != arity)
            return fail(k, "A boundary applies a position to exactly its arity (section 1.4).");
        for (uint32_t i = 0; i < count; ++i)
            if (!data_term(sh, arguments[i], binders)) return false;
        return true;
    }
    if (is_constructor(sh, h, &which)) {
        const cc_constructor *c = &sh->signature->constructors[which];
        if (count != c->data + c->positions)
            return fail(k, "A boundary applies an earlier constructor to all its data and positions (section 1.4).");
        /* Arguments were collected innermost last: argument i is count - 1 - i. */
        for (uint32_t i = 0; i < count; ++i) {
            cc_term argument = arguments[count - 1 - i];
            if (i < c->data ? !data_term(sh, argument, binders) : !positional(sh, argument, depth + 1, binders))
                return false;
        }
        return true;
    }
    if (sh->self && h.kind == CC_CONTEXT && h.payload == sh->self)
        return fail(k, "A constructor's boundary names the constructor itself (section 1.5).");
    return fail(k, "A boundary must be a constructor expression: a position or an earlier constructor, applied, "
                   "or a path application or abstraction of one (section 1.4).");
}

/* C ::= s | Path(i; C, E, E): a cube over the sort, of depth the number of
 * path binders. Nesting counts the boundaries it sits in. */
static bool cube(shape *sh, cc_term c, uint32_t *dimensions, unsigned guard, unsigned nesting, uint32_t binders) {
    cc_kernel *k = sh->k;
    if (guard > CC_CONSTRUCTOR_DIMENSIONS)
        return ck_fail_as(k, CC_ERROR_RESOURCE, "A constructor has too many dimensions, or a position too deep a cube.");
    if (nesting > 256)
        return ck_fail_as(k, CC_ERROR_RESOURCE, "A boundary is nested too deeply.");
    cc_node n = node(k, c);
    if (is_sort(sh, n)) {
        *dimensions = 0;
        return true;
    }
    if (n.kind == CC_PATH) {
        uint32_t inner = 0;
        if (!cube(sh, n.child[0], &inner, guard + 1, nesting, binders) || !endpoint(sh, n.child[1], nesting, binders) ||
            !endpoint(sh, n.child[2], nesting, binders))
            return false;
        *dimensions = inner + 1;
        return true;
    }
    return fail(k, "A position's type and a constructor's result end in the sort, or in an iterated path type over "
                   "it (section 1.2).");
}

/* T ::= Π (ts : Ds). Π (qs : Qs). R, data first. A domain that mentions the
 * sort, a constructor or an earlier position is a position, Π (ys : As). C;
 * any other is data. Argument j is bound at level j. */
static bool constructor_shape(shape *sh, cc_term t, cc_constructor *out) {
    cc_kernel *k = sh->k;
    uint32_t data = 0, binders = 0;
    bool positions = false;
    while (node(k, t).kind == CC_PI) {
        cc_node n = node(k, t);
        if (data + sh->positions >= CC_CONSTRUCTOR_ARGUMENTS)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "A constructor has too many arguments.");
        if (mentions(sh, n.child[0], binders)) {
            cc_term body = n.child[0];
            uint32_t arity = 0, depth = 0;
            while (node(k, body).kind == CC_PI) {
                cc_node binder = node(k, body);
                if (mentions(sh, binder.child[0], binders + arity))
                    return fail(k, "A position's arity mentions the sort, a constructor or a position: the sort "
                                   "occurs only at the end of a position (section 1.3).");
                if (++arity > CC_CONSTRUCTOR_ARGUMENTS)
                    return ck_fail_as(k, CC_ERROR_RESOURCE, "A position's arity is too long.");
                body = binder.child[1];
            }
            if (!cube(sh, body, &depth, 0, 0, binders + arity))
                return false;
            sh->position_levels[sh->positions] = binders;
            sh->position_arities[sh->positions++] = arity;
            positions = true;
        } else {
            if (positions)
                return fail(k, "A data argument follows a position; the kernel requires all data first (section 1.2).");
            ++data;
        }
        t = n.child[1];
        ++binders;
    }
    uint32_t dimensions = 0;
    if (!cube(sh, t, &dimensions, 0, 0, binders))
        return false;
    out->data = data;
    out->positions = sh->positions;
    out->dimensions = dimensions;
    return true;
}

/* ---- Admission (F1) -------------------------------------------------------- */

static bool signature_fact(cc_kernel *k, cc_judgement_id id, cc_fact *fact, uint32_t *index, cc_signature **s) {
    if (!id || id >= k->fact_count)
        return fail(k, "Unknown judgement.");
    if (k->facts[id].kind != CC_FACT_SIGNATURE)
        return fail(k, "Expected a signature judgement.");
    *fact = k->facts[id];
    *index = node(k, fact->term).payload;
    if (!*index || *index >= k->signature_count)
        return fail(k, "The signature judgement names no signature.");
    *s = &k->signatures[*index];
    if ((*s)->admitted)
        return fail(k, "The signature is already admitted; an admitted signature never changes.");
    if (fact->pending != (*s)->constructor_count)
        return fail(k, "Only the signature's latest judgement continues it.");
    return true;
}

/* The end of a type after its Π telescope, and how many binders that is. */
static cc_term codomain_end(const cc_kernel *k, cc_term t, uint32_t *binders) {
    *binders = 0;
    while (node(k, t).kind == CC_PI) {
        t = node(k, t).child[1];
        ++*binders;
    }
    return t;
}

/* Whether a parameter type, at depth `depth` of the former's prenex, ends
 * in exactly U(x_j), x_j the j-th universe parameter: a determining
 * occurrence of x_j (section 1.1). */
static bool determines(const cc_kernel *k, cc_term type, uint32_t depth, uint32_t j) {
    uint32_t binders = 0;
    cc_node end = node(k, codomain_end(k, type, &binders));
    if (end.kind != CC_U)
        return false;
    cc_node level = node(k, end.child[0]);
    return level.kind == CC_BOUND && level.payload < depth + binders && depth + binders - 1 - level.payload == j;
}

/* An entry of the store that is a live term or level entry, of the kind
 * given. */
static bool entry_of_kind(cc_kernel *k, cc_entry_id id, bool level) {
    return id && id < k->entry_count && !k->entries[id].face && !k->entries[id].dimension &&
           k->entries[id].level_variable == level;
}

cc_judgement_id cc_instr_signature_begin(cc_kernel *k, cc_judgement_id former_id, uint32_t modifier,
                                         const cc_entry_id *parameters, size_t count, cc_entry_id sort,
                                         uint32_t recorded) {
    /* Each admission is a new sort (Q10), and the gate and the table change:
     * never the cached result of an identical call. Its parameters' entries
     * are recorded with it, and its sort's entry is its first operand. */
    if (!ck_instr_begin_stateful(k, (cc_derivation){.rule = CC_INSTR_SIGNATURE_BEGIN, .premise = {former_id},
                                                    .operand = {sort, recorded}, .entry = modifier}, parameters, count))
        return 0;
    if (!(k->extensions & CC_EXTENSION_H1))
        return fail(k, "Declared types (H1) are switched off in this kernel; CC_EXTENSION_H1 switches them on."), 0;
    cc_fact f = {0};
    if (!ck_instr_premise(k, former_id, CC_FACT_TYPING, &f))
        return 0;
    if (f.context)
        return fail(k, "A signature's former type must be closed."), 0;
    if (modifier > CC_TRUNCATION_MAX + 2)
        return ck_fail_as(k, CC_ERROR_RESOURCE, "A truncation level is at most the kernel's bound."), 0;
    /* The prenex: Π (xs < ω). Π (ps : Ps). U(ℓ). */
    cc_term types[CC_SIGNATURE_PARAMETERS];
    uint32_t levels = 0, parameter_count = 0;
    cc_term t = f.term;
    while (node(k, t).kind == CC_LPI) {
        cc_node n = node(k, t);
        if (levels == CC_SIGNATURE_LEVELS)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "A signature has too many universe parameters."), 0;
        cc_node bound = node(k, n.child[0]);
        if (bound.kind != CC_LBOUND || bound.payload != 1)
            return fail(k, "A signature's universe parameters range below UU0: x < ω."), 0;
        ++levels;
        t = n.child[1];
    }
    while (node(k, t).kind == CC_PI) {
        cc_node n = node(k, t);
        if (parameter_count == CC_SIGNATURE_PARAMETERS)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "A signature has too many parameters."), 0;
        types[parameter_count++] = n.child[0];
        t = n.child[1];
    }
    if (node(k, t).kind != CC_U)
        return fail(k, "A signature's former type is Π (xs < ω). Π (ps : Ps). U(ℓ)."), 0;
    cc_term level = node(k, t).child[0];
    uint32_t total = levels + parameter_count;
    if (count != total || (count && !parameters))
        return fail(k, "A signature takes one entry for each of its former's parameters."), 0;
    /* Each parameter's entry is of its binder's kind and at its binder's
     * domain, opened with the entries before it; all are distinct, and the
     * sort's apart from them (section 3.6). */
    cc_term opened_with[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS] = {0};
    for (uint32_t i = 0; i < total; ++i) {
        bool universe = i < levels;
        if (!entry_of_kind(k, parameters[i], universe))
            return fail(k, universe ? "A signature's universe parameter takes a level entry."
                                    : "A signature's term parameter takes a term entry."), 0;
        for (uint32_t j = 0; j < i; ++j)
            if (parameters[j] == parameters[i])
                return fail(k, "A signature's entries are pairwise distinct, the sort's apart from its parameters'."), 0;
        if (!universe) {
            cc_term values[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS] = {0};
            for (uint32_t m = 0; m < i; ++m)
                values[m] = opened_with[i - 1 - m];
            cc_term expected = ck_instantiate_all(k, types[i - levels], values, i);
            if (!expected)
                return 0;
            if (!ck_alpha_equal(k, k->entries[parameters[i]].type, expected)) {
                if (!k->error[0])
                    fail(k, "A parameter entry's type is not the signature's.");
                return 0;
            }
        }
        opened_with[i] = ck_make(k, CC_CONTEXT, parameters[i], 0, 0, 0, 0);
        if (!opened_with[i])
            return 0;
    }
    if (!entry_of_kind(k, sort, false))
        return fail(k, "A signature's sort takes a term entry."), 0;
    for (uint32_t i = 0; i < total; ++i)
        if (parameters[i] == sort)
            return fail(k, "A signature's entries are pairwise distinct, the sort's apart from its parameters'."), 0;
    {
        cc_term values[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS] = {0};
        for (uint32_t m = 0; m < total; ++m)
            values[m] = opened_with[total - 1 - m];
        cc_term universe = ck_universe(k, ck_instantiate_all(k, level, values, total));
        if (!universe)
            return 0;
        if (!ck_alpha_equal(k, k->entries[sort].type, universe)) {
            if (!k->error[0])
                fail(k, "The sort entry's type is not the signature's universe.");
            return 0;
        }
    }
    if (levels < 32 && (recorded >> levels))
        return fail(k, "The classification marks a universe parameter the signature does not have."), 0;
    /* An erased parameter is read at an instance from a term parameter whose
     * type ends in exactly U(x) (section 1.1). */
    for (uint32_t j = 0; j < levels; ++j) {
        if (recorded & (UINT32_C(1) << j))
            continue;
        bool determined = false;
        for (uint32_t i = 0; i < parameter_count && !determined; ++i)
            determined = determines(k, types[i], levels + i, j);
        if (!determined)
            return fail(k, "An erased universe parameter needs a determining occurrence: a parameter whose type ends in "
                           "U(x) (section 1.1). Otherwise it is recorded."), 0;
    }
    uint32_t index = 0;
    cc_signature *s = new_signature(k, &index);
    if (!s)
        return 0;
    s->entries = malloc((total ? total : 1) * sizeof *s->entries);
    s->parameter_types = malloc((parameter_count ? parameter_count : 1) * sizeof *s->parameter_types);
    if (!s->entries || !s->parameter_types) {
        release(s);
        --k->signature_count;
        return ck_fail_as(k, CC_ERROR_RESOURCE, "Signature allocation failed."), 0;
    }
    /* A signature without parameters may come with null arrays, which memcpy
     * may not be passed even for no bytes. */
    if (total)
        memcpy(s->entries, parameters, total * sizeof *parameters);
    if (parameter_count)
        memcpy(s->parameter_types, types, parameter_count * sizeof *types);
    s->modifier = modifier;
    s->sort_entry = sort;
    s->level_count = levels;
    s->parameter_count = parameter_count;
    s->recorded = recorded;
    s->former = f.term;
    s->level = level;
    cc_term sort_term = ck_make(k, CC_SORT, index, 0, 0, 0, 0);
    cc_judgement_id id = sort_term ? ck_instr_publish(k, CC_FACT_SIGNATURE, sort_term, 0, f.term, 0) : 0;
    /* The entries were copied into the store: the caller's array is not kept. */
    k->pending_entries = NULL;
    k->pending.entry_count = 0;
    if (!id) {
        release(s);
        --k->signature_count;
    }
    return id;
}

/* Whether an entry stands for part of an open signature's telescope: a
 * parameter, the sort, or an earlier constructor. */
static bool in_telescope(const cc_signature *s, cc_entry_id id) {
    if (id == s->sort_entry)
        return true;
    for (uint32_t j = 0; j < s->level_count + s->parameter_count; ++j)
        if (s->entries[j] == id) return true;
    for (uint32_t j = 0; j < s->constructor_count; ++j)
        if (s->constructors[j].entry == id) return true;
    return false;
}

/* Every entry of a constructor type's context is the signature's: a universe
 * or term parameter's entry, the sort entry, or an earlier constructor's
 * entry, each of which was typed when it was supplied. */
static bool admission_context(cc_kernel *k, const cc_signature *s, uint32_t context, cc_entry_id self) {
    cc_context_set set = k->context_sets[context];
    for (uint32_t i = 0; i < set.count; ++i) {
        cc_entry_id id = k->context_items[set.offset + i];
        cc_entry e = k->entries[id];
        if (e.dimension)
            return fail(k, "A constructor type's context holds a dimension entry.");
        if (id == self)
            return fail(k, "A constructor's type names the constructor itself (section 1.5).");
        if (!in_telescope(s, id))
            return fail(k, "A constructor type's context holds an entry that is not the signature's: a later "
                           "constructor, or a name from outside the signature (section 1.5).");
    }
    return true;
}

/* A constructor type over the admission entries, closed over the telescope
 * of levels, parameters, sort and the first `constructors` constructors:
 * each entry abstracted, the innermost at index 0, and nothing left open. */
static cc_term closed_type(cc_kernel *k, const cc_signature *s, cc_term type, uint32_t constructors) {
    uint32_t base = 0;
    for (uint32_t m = constructors; m-- > 0 && type;)
        type = ck_abstract_at(k, type, s->constructors[m].entry, base++);
    if (type) type = ck_abstract_at(k, type, s->sort_entry, base++);
    for (uint32_t j = s->level_count + s->parameter_count; j-- > 0 && type;)
        type = ck_abstract_at(k, type, s->entries[j], base++);
    if (type && k->nodes[type].contexts)
        return fail(k, "A constructor type mentions an entry outside its signature's telescope."), 0;
    return type;
}

/* An open signature's level, U's at the end of its former, over its
 * parameters' entries: the stored level opened with them. */
static cc_term open_level(cc_kernel *k, const cc_signature *s) {
    uint32_t total = s->level_count + s->parameter_count;
    cc_term values[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS] = {0};
    for (uint32_t m = 0; m < total; ++m)
        if (!(values[m] = ck_make(k, CC_CONTEXT, s->entries[total - 1 - m], 0, 0, 0, 0)))
            return 0;
    return ck_instantiate_all(k, s->level, values, total);
}

cc_judgement_id cc_instr_signature_constructor(cc_kernel *k, cc_judgement_id signature_id, cc_judgement_id type_id,
                                               cc_entry_id entry) {
    if (!ck_instr_begin_stateful(k, (cc_derivation){.rule = CC_INSTR_SIGNATURE_CONSTRUCTOR,
                                                    .premise = {signature_id, type_id}, .entry = entry}, NULL, 0))
        return 0;
    cc_fact sf = {0}, tf = {0};
    uint32_t index = 0;
    cc_signature *s = NULL;
    if (!signature_fact(k, signature_id, &sf, &index, &s) || !ck_instr_premise(k, type_id, CC_FACT_TYPING, &tf))
        return 0;
    cc_term level = open_level(k, s);
    if (!level)
        return 0;
    if (node(k, tf.type).kind != CC_U || !ck_level_equal(k, node(k, tf.type).child[0], level)) {
        if (!k->error[0])
            fail(k, "A constructor type is derived in the signature's universe U(ℓ); lift it there first.");
        return 0;
    }
    /* The constructor's entry is new to the telescope, a term entry at the
     * constructor's type (section 3.6). */
    if (!entry_of_kind(k, entry, false))
        return fail(k, "A constructor takes a term entry."), 0;
    if (in_telescope(s, entry))
        return fail(k, "A constructor's entry is already in its signature's telescope."), 0;
    if (!ck_alpha_equal(k, k->entries[entry].type, tf.term)) {
        if (!k->error[0])
            fail(k, "A constructor entry's type is not that constructor's.");
        return 0;
    }
    if (!admission_context(k, s, tf.context, entry))
        return 0;
    shape sh = {.k = k, .signature = s, .constructors = s->constructor_count, .self = entry};
    cc_constructor c = {.entry = entry};
    if (!constructor_shape(&sh, tf.term, &c))
        return 0;
    for (uint32_t j = 0; j < s->level_count; ++j)
        if (!(s->recorded & (UINT32_C(1) << j)) && ck_mentions(k, tf.term, s->entries[j]))
            return fail(k, "A constructor type mentions an erased universe parameter; only a recorded one may occur "
                           "there (section 1.1)."), 0;
    c.type = k->error[0] ? 0 : closed_type(k, s, tf.term, s->constructor_count);
    if (!c.type || !add_constructor(k, s, c))
        return 0;
    cc_judgement_id id = ck_instr_publish(k, CC_FACT_SIGNATURE, sf.term, 0, sf.type, 0);
    if (!id) {
        --s->constructor_count;
        return 0;
    }
    k->facts[id].pending = s->constructor_count;
    return id;
}

/* The squash of trunc(n) (section 1.6): with B_0 := s and
 * B_{j+1} := Path(B_j, y_j, z_j), it takes y_j, z_j : B_j for j from 0 to
 * n + 1 and gives B_{n+2}(y_{n+1}, z_{n+1}). Its dimension j is index j. It
 * is built over the sort's entry, checked as any other constructor type, and
 * closed over the telescope: y_j is the argument at level 2j and z_j at
 * 2j + 1, so under d binders they are indices d - 1 - 2j and d - 2 - 2j. */
static cc_term cube_at(cc_kernel *k, cc_entry_id sort, uint32_t j, uint32_t binders) {
    cc_term b = ck_make(k, CC_CONTEXT, sort, 0, 0, 0, 0);
    for (uint32_t i = 0; i < j && b; ++i)
        b = ck_make(k, CC_PATH, i, b, ck_make(k, CC_BOUND, binders - 1 - 2 * i, 0, 0, 0, 0),
                    ck_make(k, CC_BOUND, binders - 2 - 2 * i, 0, 0, 0, 0), 0);
    return b;
}

static cc_term squash_type(cc_kernel *k, const cc_signature *s) {
    uint32_t steps = s->modifier;          /* n + 2 */
    cc_term b = cube_at(k, s->sort_entry, steps, 2 * steps);
    for (uint32_t j = steps; j-- > 0 && b;) {
        b = ck_make(k, CC_PI, 0, cube_at(k, s->sort_entry, j, 2 * j + 1), b, 0, 0);
        b = b ? ck_make(k, CC_PI, 0, cube_at(k, s->sort_entry, j, 2 * j), b, 0, 0) : 0;
    }
    return b;
}

uint32_t cc_instr_signature_close(cc_kernel *k, cc_judgement_id signature_id) {
    if (!ck_instr_ready(k))
        return 0;
    cc_fact sf = {0};
    uint32_t index = 0;
    cc_signature *s = NULL;
    if (!signature_fact(k, signature_id, &sf, &index, &s))
        return 0;
    if (s->modifier != CC_UNTRUNCATED) {
        cc_constructor c = {.generated = true};
        cc_term open = squash_type(k, s);
        shape sh = {.k = k, .signature = s, .constructors = s->constructor_count};
        /* The generated type is checked like any other: a sanity check. */
        if (!open || !constructor_shape(&sh, open, &c))
            return 0;
        c.type = closed_type(k, s, open, s->constructor_count);
        if (!c.type || !add_constructor(k, s, c))
            return 0;
    }
    s->admitted = true;
    return index;
}

/* ---- Instances and constructors (F2) --------------------------------------- */

static uint32_t recorded_count(const cc_signature *s) {
    uint32_t n = 0;
    for (uint32_t j = 0; j < s->level_count; ++j)
        n += (s->recorded >> j) & 1u;
    return n;
}

static cc_term cons(cc_kernel *k, cc_term item, cc_term next) { return ck_make(k, CC_LIST, 0, item, next, 0, 0); }

/* A list's items in order; a list in progress is kept reversed. */
static uint32_t items(const cc_kernel *k, cc_term list, cc_term *out, uint32_t max, bool reversed) {
    uint32_t n = 0;
    for (; list && n < max; list = node(k, list).child[1])
        out[n++] = node(k, list).child[0];
    if (reversed)
        for (uint32_t i = 0; i < n / 2; ++i) { cc_term t = out[i]; out[i] = out[n - 1 - i]; out[n - 1 - i] = t; }
    return n;
}

static cc_term list_of(cc_kernel *k, const cc_term *xs, uint32_t n) {
    cc_term list = 0;
    for (uint32_t i = n; i-- > 0 && !k->error[0];)
        list = cons(k, xs[i], list);
    return list;
}

/* The admitted signature an instance term names. */
static bool admitted_signature(cc_kernel *k, cc_term sort, uint32_t *index, cc_signature **s) {
    cc_node n = node(k, sort);
    if (n.kind != CC_SORT || !n.payload || n.payload >= k->signature_count)
        return fail(k, "Expected an instance of a declared type.");
    *index = n.payload;
    *s = &k->signatures[*index];
    if (!(*s)->admitted)
        return fail(k, "Only an admitted signature has instances.");
    return true;
}

/* A term over a prefix of the admission telescope, instantiated in one pass:
 * `values` in telescope order, outermost first, so the last is index 0.
 * With level values among them, every level of the result is taken to
 * normal form, as level instantiation does (G0 §2.8). */
static cc_term at_telescope(cc_kernel *k, cc_term term, const cc_term *values, uint32_t count, bool levels) {
    cc_term reversed[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS + CC_SIGNATURE_CONSTRUCTORS + 1] = {0};
    for (uint32_t i = 0; i < count; ++i)
        reversed[i] = values[count - 1 - i];
    cc_term result = ck_instantiate_all(k, term, reversed, count);
    return result && levels ? ck_canonical_levels(k, result) : result;
}

/* An instance is complete: read the erased levels, check each parameter
 * against the telescope, and publish S{ls}(as) : U(ℓ[ρ]) (section 3.1). */
static cc_judgement_id complete_instance(cc_kernel *k, uint32_t index, const cc_term *levels, const cc_term *as,
                                         const cc_term *types, uint32_t context) {
    const cc_signature *s = &k->signatures[index];
    cc_term rho[CC_SIGNATURE_LEVELS] = {0};
    for (uint32_t j = 0, r = 0; j < s->level_count; ++j) {
        if (s->recorded & (UINT32_C(1) << j)) {
            rho[j] = levels[r++];
            continue;
        }
        /* The determining occurrence: the first parameter whose type ends in
         * exactly U(x_j); the level is read at the end of its judgement's type. */
        for (uint32_t i = 0; i < s->parameter_count && !rho[j]; ++i) {
            if (!determines(k, s->parameter_types[i], s->level_count + i, j))
                continue;
            uint32_t binders = 0;
            cc_node found = node(k, codomain_end(k, types[i], &binders));
            if (found.kind != CC_U)
                return fail(k, "A parameter's type does not end in a universe where the signature's does."), 0;
            uint32_t ignored = 0;
            if (!ck_instr_finite_level(k, found.child[0], &rho[j], &ignored))
                return 0;
        }
        if (!rho[j])
            return fail(k, "An erased universe parameter has no determining occurrence."), 0;
    }
    /* The telescope's values so far: the levels, then the parameters. */
    cc_term values[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS] = {0};
    for (uint32_t j = 0; j < s->level_count; ++j)
        values[j] = rho[j];
    for (uint32_t i = 0; i < s->parameter_count; ++i) {
        cc_term expected = at_telescope(k, s->parameter_types[i], values, s->level_count + i, s->level_count > 0);
        if (!expected)
            return 0;
        if (!ck_alpha_equal(k, types[i], expected)) {
            if (k->error[0])
                return 0;
            bool reading = false;
            for (uint32_t j = 0; j < s->level_count && !reading; ++j)
                reading = !(s->recorded & (UINT32_C(1) << j)) && determines(k, s->parameter_types[i], s->level_count + i, j);
            k->mismatch_found = types[i];
            k->mismatch_expected = expected;
            return ck_fail_as(k, CC_ERROR_MISMATCH, reading
                ? "A parameter reads an erased universe parameter at another level than an earlier one; lift the lower "
                  "parameter first."
                : "A parameter's type is not the signature's telescope at the earlier parameters."), 0;
        }
        values[s->level_count + i] = as[i];
    }
    cc_term level = at_telescope(k, s->level, values, s->level_count + s->parameter_count, s->level_count > 0);
    cc_term canonical = 0;
    uint32_t level_context = 0;
    /* The sort's own level may be of any tier, as a fixed signature's in UU0
     * is; only the levels read and given are finite. */
    if (!level || !ck_instr_level(k, level, false, &canonical, &level_context) ||
        !ck_instr_merge(k, context, level_context, &context))
        return 0;
    cc_term term = ck_make(k, CC_SORT, index, list_of(k, as, s->parameter_count), list_of(k, levels, recorded_count(s)), 0, 0);
    return term ? ck_instr_publish(k, CC_FACT_TYPING, term, 0, ck_universe(k, canonical), context) : 0;
}

/* An instance in progress: kind 5, whose term is Sort(index) with the
 * parameters and levels so far, reversed; other, the parameters' types,
 * reversed; pending, the levels supplied and, above bit 32, the parameters. */
static cc_judgement_id instance_step(cc_kernel *k, uint32_t index, cc_term params, cc_term levels, cc_term types,
                                     uint32_t context, uint32_t level_count, uint32_t parameter_count) {
    const cc_signature *s = &k->signatures[index];
    if (level_count == recorded_count(s) && parameter_count == s->parameter_count) {
        cc_term ls[CC_SIGNATURE_LEVELS], as[CC_SIGNATURE_PARAMETERS], ts[CC_SIGNATURE_PARAMETERS];
        items(k, levels, ls, CC_SIGNATURE_LEVELS, true);
        items(k, params, as, CC_SIGNATURE_PARAMETERS, true);
        items(k, types, ts, CC_SIGNATURE_PARAMETERS, true);
        return complete_instance(k, index, ls, as, ts, context);
    }
    cc_term term = ck_make(k, CC_SORT, index, params, levels, 0, 0);
    cc_judgement_id id = term ? ck_instr_publish(k, CC_FACT_INSTANCE, term, types, s->former, context) : 0;
    if (id)
        k->facts[id].pending = level_count | (uint64_t)parameter_count << 32;
    return id;
}

cc_judgement_id cc_instr_sort_begin(cc_kernel *k, uint32_t index) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SORT_BEGIN, .operand = {index}}, NULL, 0, &found))
        return found;
    if (!index || index >= k->signature_count || !k->signatures[index].admitted)
        return fail(k, "Only an admitted signature has instances."), 0;
    return instance_step(k, index, 0, 0, 0, 0, 0, 0);
}

static bool instance_fact(cc_kernel *k, cc_judgement_id id, cc_fact *f, uint32_t *index, cc_signature **s,
                          uint32_t *levels, uint32_t *parameters) {
    if (!id || id >= k->fact_count)
        return fail(k, "Unknown judgement.");
    if (k->facts[id].kind != CC_FACT_INSTANCE)
        return fail(k, "Expected an instance in progress.");
    *f = k->facts[id];
    if (!admitted_signature(k, f->term, index, s))
        return false;
    *levels = (uint32_t)(f->pending & 0xffffffffu);
    *parameters = (uint32_t)(f->pending >> 32);
    return true;
}


cc_judgement_id cc_instr_sort_level(cc_kernel *k, cc_judgement_id instance, cc_term level) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SORT_LEVEL, .premise = {instance}, .operand = {level}},
                        NULL, 0, &found))
        return found;
    cc_fact f = {0};
    uint32_t index = 0, levels = 0, parameters = 0, context = 0;
    cc_signature *s = NULL;
    if (!instance_fact(k, instance, &f, &index, &s, &levels, &parameters))
        return 0;
    if (parameters || levels >= recorded_count(s))
        return fail(k, "An instance takes its recorded levels first, one for each recorded universe parameter."), 0;
    cc_term canonical = 0;
    if (!ck_instr_finite_level(k, level, &canonical, &context) || !ck_instr_merge(k, f.context, context, &context))
        return 0;
    cc_node sort = node(k, f.term);
    return instance_step(k, index, sort.child[0], cons(k, canonical, sort.child[1]), f.other, context,
                         levels + 1, parameters);
}

cc_judgement_id cc_instr_sort_parameter(cc_kernel *k, cc_judgement_id instance, cc_judgement_id parameter) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SORT_PARAMETER, .premise = {instance, parameter}},
                        NULL, 0, &found))
        return found;
    cc_fact f = {0}, p = {0};
    uint32_t index = 0, levels = 0, parameters = 0, context = 0;
    cc_signature *s = NULL;
    if (!instance_fact(k, instance, &f, &index, &s, &levels, &parameters) ||
        !ck_instr_premise(k, parameter, CC_FACT_TYPING, &p))
        return 0;
    if (levels < recorded_count(s))
        return fail(k, "An instance takes its recorded levels before its parameters."), 0;
    if (parameters >= s->parameter_count)
        return fail(k, "The instance already has all its parameters."), 0;
    if (!ck_instr_merge(k, f.context, p.context, &context))
        return 0;
    cc_node sort = node(k, f.term);
    return instance_step(k, index, cons(k, p.term, sort.child[0]), sort.child[1],
                         cons(k, p.type, f.other), context, levels, parameters + 1);
}

/* T_k[recorded levels, parameters, s := I, c_m := Con(m; I)] (3.2), for an
 * instance term I of an admitted signature, whatever its parameters are: the
 * stored type, closed over the admission telescope, instantiated in one
 * pass. An erased level occurs in no constructor type, so its value is
 * never put in: the constant 0 stands for it. */
cc_term ck_constructor_type(cc_kernel *k, cc_term instance, uint32_t constructor) {
    uint32_t index = 0;
    cc_signature *s = NULL;
    if (!admitted_signature(k, instance, &index, &s))
        return 0;
    if (constructor >= s->constructor_count)
        return fail(k, "The signature has no such constructor."), 0;
    cc_node sort = node(k, instance);
    cc_term levels[CC_SIGNATURE_LEVELS], as[CC_SIGNATURE_PARAMETERS];
    uint32_t level_count = items(k, sort.child[1], levels, CC_SIGNATURE_LEVELS, false);
    uint32_t parameter_count = items(k, sort.child[0], as, CC_SIGNATURE_PARAMETERS, false);
    if (level_count != recorded_count(s) || parameter_count != s->parameter_count)
        return fail(k, "The instance's parameters and levels are not the signature's."), 0;
    cc_term values[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS + CC_SIGNATURE_CONSTRUCTORS + 1] = {0};
    uint32_t n = 0;
    cc_term erased = s->recorded == (s->level_count < 32 ? (UINT32_C(1) << s->level_count) - 1 : UINT32_MAX)
        ? 0 : ck_level_constant(k, 0, 0);
    for (uint32_t j = 0, r = 0; j < s->level_count; ++j)
        values[n++] = s->recorded & (UINT32_C(1) << j) ? levels[r++] : erased;
    for (uint32_t i = 0; i < s->parameter_count; ++i)
        values[n++] = as[i];
    values[n++] = instance;
    for (uint32_t m = 0; m < constructor; ++m)
        if (!(values[n++] = ck_make(k, CC_CON, m, instance, 0, 0, 0)))
            return 0;
    return k->error[0] ? 0 : at_telescope(k, s->constructors[constructor].type, values, n, recorded_count(s) > 0);
}

const cc_signature *ck_instance_signature(cc_kernel *k, cc_term instance) {
    uint32_t index = 0;
    cc_signature *s = NULL;
    return admitted_signature(k, instance, &index, &s) ? s : NULL;
}

/* A higher sort has a constructor with dimensions, or a truncation (3.4). */
bool ck_signature_higher(const cc_signature *s) {
    if (s->modifier != CC_UNTRUNCATED)
        return true;
    for (uint32_t c = 0; c < s->constructor_count; ++c)
        if (s->constructors[c].dimensions) return true;
    return false;
}

cc_judgement_id cc_instr_construct(cc_kernel *k, cc_judgement_id instance, uint32_t constructor) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_CONSTRUCT, .premise = {instance}, .operand = {constructor}},
                        NULL, 0, &found))
        return found;
    cc_fact f = {0};
    if (!ck_instr_premise(k, instance, CC_FACT_TYPING, &f))
        return 0;
    cc_term type = ck_constructor_type(k, f.term, constructor);
    cc_term term = type ? ck_make(k, CC_CON, constructor, f.term, 0, 0, 0) : 0;
    return type && term ? ck_instr_publish(k, CC_FACT_TYPING, term, 0, type, f.context) : 0;
}

/* ---- Reading the table ---------------------------------------------------- */

size_t cc_kernel_signature_count(const cc_kernel *k) { return k && k->signature_count ? k->signature_count : 1; }

bool cc_kernel_signature(const cc_kernel *k, uint32_t index, cc_signature_info *info) {
    if (!k || !info || !index || index >= k->signature_count)
        return false;
    const cc_signature *s = &k->signatures[index];
    *info = (cc_signature_info){s->admitted, s->experimental, s->modifier, s->level_count,
                                s->parameter_count, s->constructor_count, s->recorded, s->former, s->level};
    return true;
}

bool cc_kernel_signature_constructor(const cc_kernel *k, uint32_t index, uint32_t constructor,
                                     cc_constructor_info *info) {
    if (!k || !info || !index || index >= k->signature_count)
        return false;
    const cc_signature *s = &k->signatures[index];
    if (constructor >= s->constructor_count)
        return false;
    const cc_constructor *c = &s->constructors[constructor];
    *info = (cc_constructor_info){c->data, c->positions, c->dimensions, c->type, c->generated};
    return true;
}
