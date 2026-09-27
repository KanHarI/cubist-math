/* Declared types (H1): the signature table and the admission instructions,
 * families F1 and F6 of docs/roadmaps/h1-signature-specification.md
 * (section 5). A signature is admitted one constructor at a time. Every check
 * is syntactic, on terms as written, as every instruction's is: the normal
 * form of sections 1.1-1.6, strict positivity by construction, and the
 * classification of universe parameters into erased and recorded ones.
 *
 * Admission symbols are the universe parameters, the term parameters, the
 * sort and the constructors. A constructor type is derived by ordinary
 * instructions in a context of entries named by those symbols, so the kernel
 * checks here only that the context is the signature's and that the type has
 * the normal form. Nothing here reduces a term. */
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
    free(s->symbols);
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
        return fail(k, "Signature table exhausted."), NULL;
    if (k->signature_count == k->signature_capacity || !k->signatures) {
        size_t next = k->signature_capacity ? 2 * k->signature_capacity : 16;
        cc_signature *grown = realloc(k->signatures, next * sizeof *grown);
        if (!grown)
            return fail(k, "Signature table allocation failed."), NULL;
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
        return fail(k, "A signature has too many constructors.");
    if (s->constructor_count == s->constructor_capacity) {
        uint32_t next = s->constructor_capacity ? 2 * s->constructor_capacity : 8;
        cc_constructor *grown = realloc(s->constructors, next * sizeof *grown);
        if (!grown)
            return fail(k, "Constructor table allocation failed.");
        s->constructors = grown;
        s->constructor_capacity = next;
    }
    s->constructors[s->constructor_count++] = c;
    return true;
}

/* ---- The normal form (sections 1.2-1.5) ---------------------------------- */

/* A constructor type is checked with the positions bound so far and the
 * constructors before it. Positions record their arity lengths, so that a
 * boundary applies each to exactly its arity. */
typedef struct {
    cc_kernel *k;
    const cc_signature *signature;
    uint32_t constructors;             /* the earlier constructors: 0 .. constructors - 1 */
    uint32_t self;                     /* the new constructor's symbol */
    uint32_t position_symbols[CC_CONSTRUCTOR_ARGUMENTS], position_arities[CC_CONSTRUCTOR_ARGUMENTS];
    uint32_t positions;
} shape;

static bool is_position(const shape *sh, uint32_t symbol, uint32_t *arity) {
    for (uint32_t i = 0; i < sh->positions; ++i)
        if (sh->position_symbols[i] == symbol) { if (arity) *arity = sh->position_arities[i]; return true; }
    return false;
}

static bool is_constructor(const shape *sh, uint32_t symbol, uint32_t *which) {
    for (uint32_t i = 0; i < sh->constructors; ++i)
        if (sh->signature->constructors[i].symbol == symbol) { if (which) *which = i; return true; }
    return false;
}

/* The names a binder inside a constructor type may not take: they would
 * shadow the signature's, and the checks below read names syntactically. */
static bool reserved(const shape *sh, uint32_t symbol) {
    const cc_signature *s = sh->signature;
    if (symbol == s->sort_symbol || symbol == sh->self)
        return true;
    for (uint32_t i = 0; i < s->level_count + s->parameter_count; ++i)
        if (s->symbols[i] == symbol) return true;
    return is_constructor(sh, symbol, NULL) || is_position(sh, symbol, NULL);
}

/* Whether t mentions the sort, an earlier constructor or a position: the
 * names a data type, an arity and a data term may not mention. */
static bool mentions(shape *sh, cc_term t) {
    cc_kernel *k = sh->k;
    if (ck_term_free(k, t, sh->signature->sort_symbol))
        return true;
    for (uint32_t i = 0; i < sh->constructors; ++i)
        if (ck_term_free(k, t, sh->signature->constructors[i].symbol)) return true;
    for (uint32_t i = 0; i < sh->positions; ++i)
        if (ck_term_free(k, t, sh->position_symbols[i])) return true;
    return false;
}

static bool endpoint(shape *sh, cc_term e, unsigned depth);

/* E' ::= E | λ (y : A). E', a positional argument under its arity's binders. */
static bool positional(shape *sh, cc_term e, unsigned depth) {
    cc_kernel *k = sh->k;
    if (depth > 256)
        return fail(k, "A boundary is nested too deeply.");
    cc_node n = node(k, e);
    if (n.kind != CC_LAM)
        return endpoint(sh, e, depth + 1);
    if (reserved(sh, n.payload))
        return fail(k, "A binder in a boundary reuses a name of the signature.");
    if (mentions(sh, n.child[0]))
        return fail(k, "A binder's type in a boundary mentions the sort, a constructor or a position (section 1.4).");
    return positional(sh, n.child[1], depth + 1);
}

static bool data_term(shape *sh, cc_term t) {
    if (mentions(sh, t))
        return fail(sh->k, "A boundary applies a position or constructor to data terms only: terms that mention "
                           "no sort, constructor or position (section 1.4).");
    return true;
}

/* E ::= q_j(us) | c_m(us, Es') | E @ r | ⟨i⟩ E: constructor expressions over
 * the positions and the earlier constructors. No composition, transport or
 * other operation of the sort occurs (Q3). */
static bool endpoint(shape *sh, cc_term e, unsigned depth) {
    cc_kernel *k = sh->k;
    if (depth > 256)
        return fail(k, "A boundary is nested too deeply.");
    cc_node n = node(k, e);
    if (n.kind == CC_PLAM)
        return endpoint(sh, n.child[1], depth + 1);
    if (n.kind == CC_PAPP)
        return endpoint(sh, n.child[0], depth + 1);
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
    if (h.kind == CC_VAR && is_position(sh, h.payload, &arity)) {
        if (count != arity)
            return fail(k, "A boundary applies a position to exactly its arity (section 1.4).");
        for (uint32_t i = 0; i < count; ++i)
            if (!data_term(sh, arguments[i])) return false;
        return true;
    }
    if (h.kind == CC_VAR && is_constructor(sh, h.payload, &which)) {
        const cc_constructor *c = &sh->signature->constructors[which];
        if (count != c->data + c->positions)
            return fail(k, "A boundary applies an earlier constructor to all its data and positions (section 1.4).");
        /* Arguments were collected innermost last: argument i is count - 1 - i. */
        for (uint32_t i = 0; i < count; ++i) {
            cc_term argument = arguments[count - 1 - i];
            if (i < c->data ? !data_term(sh, argument) : !positional(sh, argument, depth + 1))
                return false;
        }
        return true;
    }
    if (h.kind == CC_VAR && h.payload == sh->self)
        return fail(k, "A constructor's boundary names the constructor itself (section 1.5).");
    return fail(k, "A boundary must be a constructor expression: a position or an earlier constructor, applied, "
                   "or a path application or abstraction of one (section 1.4).");
}

/* C ::= s | Path(i; C, E, E): a cube over the sort, of depth the number of
 * path binders. */
static bool cube(shape *sh, cc_term c, uint32_t *depth, unsigned guard) {
    cc_kernel *k = sh->k;
    if (guard > CC_CONSTRUCTOR_DIMENSIONS)
        return fail(k, "A constructor has too many dimensions, or a position too deep a cube.");
    cc_node n = node(k, c);
    if (n.kind == CC_VAR && n.payload == sh->signature->sort_symbol) {
        *depth = 0;
        return true;
    }
    if (n.kind == CC_PATH) {
        uint32_t inner = 0;
        if (!cube(sh, n.child[0], &inner, guard + 1) || !endpoint(sh, n.child[1], 0) || !endpoint(sh, n.child[2], 0))
            return false;
        *depth = inner + 1;
        return true;
    }
    return fail(k, "A position's type and a constructor's result end in the sort, or in an iterated path type over "
                   "it (section 1.2).");
}

/* T ::= Π (ts : Ds). Π (qs : Qs). R, data first. A domain that mentions the
 * sort, a constructor or an earlier position is a position, Π (ys : As). C;
 * any other is data. */
static bool constructor_shape(shape *sh, cc_term t, cc_constructor *out) {
    cc_kernel *k = sh->k;
    uint32_t data = 0;
    bool positions = false;
    while (node(k, t).kind == CC_PI) {
        cc_node n = node(k, t);
        if (reserved(sh, n.payload))
            return fail(k, "A constructor's argument reuses a name of the signature.");
        if (data + sh->positions >= CC_CONSTRUCTOR_ARGUMENTS)
            return fail(k, "A constructor has too many arguments.");
        if (mentions(sh, n.child[0])) {
            cc_term body = n.child[0];
            uint32_t arity = 0, depth = 0;
            while (node(k, body).kind == CC_PI) {
                cc_node binder = node(k, body);
                if (reserved(sh, binder.payload))
                    return fail(k, "A position's arity reuses a name of the signature.");
                if (mentions(sh, binder.child[0]))
                    return fail(k, "A position's arity mentions the sort, a constructor or a position: the sort "
                                   "occurs only at the end of a position (section 1.3).");
                if (++arity > CC_CONSTRUCTOR_ARGUMENTS)
                    return fail(k, "A position's arity is too long.");
                body = binder.child[1];
            }
            if (!cube(sh, body, &depth, 0))
                return false;
            sh->position_symbols[sh->positions] = n.payload;
            sh->position_arities[sh->positions++] = arity;
            positions = true;
        } else {
            if (positions)
                return fail(k, "A data argument follows a position; the kernel requires all data first (section 1.2).");
            ++data;
        }
        t = n.child[1];
    }
    uint32_t dimensions = 0;
    if (!cube(sh, t, &dimensions, 0))
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

/* The end of a parameter's type: after its Π telescope. */
static cc_term codomain_end(const cc_kernel *k, cc_term t) {
    while (node(k, t).kind == CC_PI)
        t = node(k, t).child[1];
    return t;
}

cc_judgement_id cc_instr_signature_begin(cc_kernel *k, cc_judgement_id former_id, uint32_t modifier,
                                         uint32_t sort_symbol, uint32_t recorded) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SIGNATURE_BEGIN, .premise = {former_id},
                                           .operand = {sort_symbol, recorded}, .entry = modifier},
                        NULL, 0, &found))
        return found;
    if (!(k->extensions & CC_EXTENSION_H1))
        return fail(k, "Declared types are a kernel extension under review (H1); the kernel admits them only when "
                       "the extension is enabled."), 0;
    cc_fact f = {0};
    if (!ck_instr_premise(k, former_id, CC_FACT_TYPING, &f))
        return 0;
    if (f.context)
        return fail(k, "A signature's former type must be closed."), 0;
    if (modifier > CC_TRUNCATION_MAX + 2)
        return fail(k, "A truncation level is at most the kernel's bound."), 0;
    if (!sort_symbol)
        return fail(k, "A signature needs a sort symbol."), 0;
    /* The prenex: Π (xs < ω). Π (ps : Ps). U(ℓ). */
    uint32_t symbols[CC_SIGNATURE_LEVELS + CC_SIGNATURE_PARAMETERS];
    cc_term types[CC_SIGNATURE_PARAMETERS];
    uint32_t levels = 0, parameters = 0;
    cc_term t = f.term;
    while (node(k, t).kind == CC_LPI) {
        cc_node n = node(k, t);
        if (levels == CC_SIGNATURE_LEVELS)
            return fail(k, "A signature has too many universe parameters."), 0;
        cc_node bound = node(k, n.child[0]);
        if (bound.kind != CC_LBOUND || bound.payload != 1)
            return fail(k, "A signature's universe parameters range below UU0: x < ω."), 0;
        symbols[levels++] = n.payload;
        t = n.child[1];
    }
    while (node(k, t).kind == CC_PI) {
        cc_node n = node(k, t);
        if (parameters == CC_SIGNATURE_PARAMETERS)
            return fail(k, "A signature has too many parameters."), 0;
        symbols[levels + parameters] = n.payload;
        types[parameters++] = n.child[0];
        t = n.child[1];
    }
    if (node(k, t).kind != CC_U)
        return fail(k, "A signature's former type is Π (xs < ω). Π (ps : Ps). U(ℓ)."), 0;
    cc_term level = node(k, t).child[0];
    uint32_t count = levels + parameters;
    for (uint32_t i = 0; i < count; ++i) {
        if (!symbols[i] || symbols[i] == sort_symbol)
            return fail(k, "A signature's parameters need distinct symbols, other than the sort's."), 0;
        for (uint32_t j = 0; j < i; ++j)
            if (symbols[i] == symbols[j])
                return fail(k, "A signature's parameters need distinct symbols, other than the sort's."), 0;
    }
    if (levels < 32 && (recorded >> levels))
        return fail(k, "The classification marks a universe parameter the signature does not have."), 0;
    /* An erased parameter is read at an instance from a term parameter whose
     * type ends in exactly U(x) (section 1.1). */
    for (uint32_t j = 0; j < levels; ++j) {
        if (recorded & (UINT32_C(1) << j))
            continue;
        bool determined = false;
        for (uint32_t i = 0; i < parameters && !determined; ++i) {
            cc_node end = node(k, codomain_end(k, types[i]));
            determined = end.kind == CC_U && node(k, end.child[0]).kind == CC_VAR &&
                         node(k, end.child[0]).payload == symbols[j];
        }
        if (!determined)
            return fail(k, "An erased universe parameter needs a determining occurrence: a parameter whose type ends in "
                           "U(x) (section 1.1). Otherwise it is recorded."), 0;
    }
    uint32_t index = 0;
    cc_signature *s = new_signature(k, &index);
    if (!s)
        return 0;
    s->symbols = malloc((count ? count : 1) * sizeof *s->symbols);
    s->parameter_types = malloc((parameters ? parameters : 1) * sizeof *s->parameter_types);
    if (!s->symbols || !s->parameter_types) {
        release(s);
        --k->signature_count;
        return fail(k, "Signature allocation failed."), 0;
    }
    memcpy(s->symbols, symbols, count * sizeof *symbols);
    memcpy(s->parameter_types, types, parameters * sizeof *types);
    s->modifier = modifier;
    s->sort_symbol = sort_symbol;
    s->level_count = levels;
    s->parameter_count = parameters;
    s->recorded = recorded;
    s->former = f.term;
    s->level = level;
    s->experimental = true;
    cc_term sort = ck_make(k, CC_SORT, index, 0, 0, 0, 0);
    cc_judgement_id id = sort ? ck_instr_publish(k, CC_FACT_SIGNATURE, sort, 0, f.term, 0) : 0;
    if (!id) {
        release(s);
        --k->signature_count;
    }
    return id;
}

/* Every entry of a constructor type's context is the signature's: a universe
 * or term parameter at its type, the sort entry, or an earlier constructor's
 * entry at that constructor's type. */
static bool admission_context(cc_kernel *k, const cc_signature *s, uint32_t context, uint32_t self) {
    cc_context_set set = k->context_sets[context];
    for (uint32_t i = 0; i < set.count; ++i) {
        cc_entry e = k->entries[k->context_items[set.offset + i]];
        if (e.dimension)
            return fail(k, "A constructor type's context holds a dimension entry.");
        if (e.symbol == self)
            return fail(k, "A constructor's type names the constructor itself (section 1.5).");
        bool known = false;
        if (e.level_variable) {
            for (uint32_t j = 0; j < s->level_count && !known; ++j)
                known = s->symbols[j] == e.symbol;
        } else if (e.symbol == s->sort_symbol) {
            if (!ck_alpha_equal(k, e.type, ck_universe(k, s->level)))
                return fail(k, "The sort entry's type is not the signature's universe.");
            known = true;
        } else {
            for (uint32_t j = 0; j < s->parameter_count && !known; ++j)
                if (s->symbols[s->level_count + j] == e.symbol) {
                    if (!ck_alpha_equal(k, e.type, s->parameter_types[j]))
                        return fail(k, "A parameter entry's type is not the signature's.");
                    known = true;
                }
            for (uint32_t j = 0; j < s->constructor_count && !known; ++j)
                if (s->constructors[j].symbol == e.symbol) {
                    if (!ck_alpha_equal(k, e.type, s->constructors[j].type))
                        return fail(k, "A constructor entry's type is not that constructor's.");
                    known = true;
                }
        }
        if (!known)
            return fail(k, "A constructor type's context holds an entry that is not the signature's: a later "
                           "constructor, or a name from outside the signature (section 1.5).");
        if (k->error[0])
            return false;
    }
    return true;
}

cc_judgement_id cc_instr_signature_constructor(cc_kernel *k, cc_judgement_id signature_id, cc_judgement_id type_id,
                                               uint32_t symbol) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SIGNATURE_CONSTRUCTOR,
                                           .premise = {signature_id, type_id}, .operand = {symbol}},
                        NULL, 0, &found))
        return found;
    cc_fact sf = {0}, tf = {0};
    uint32_t index = 0;
    cc_signature *s = NULL;
    if (!signature_fact(k, signature_id, &sf, &index, &s) || !ck_instr_premise(k, type_id, CC_FACT_TYPING, &tf))
        return 0;
    if (node(k, tf.type).kind != CC_U || !ck_level_equal(k, node(k, tf.type).child[0], s->level)) {
        if (!k->error[0])
            fail(k, "A constructor type is derived in the signature's universe U(ℓ); lift it there first.");
        return 0;
    }
    if (!symbol)
        return fail(k, "A constructor needs a symbol."), 0;
    shape sh = {.k = k, .signature = s, .constructors = s->constructor_count, .self = symbol};
    if (symbol == s->sort_symbol || is_constructor(&sh, symbol, NULL))
        return fail(k, "A constructor's symbol must be new to the signature."), 0;
    for (uint32_t i = 0; i < s->level_count + s->parameter_count; ++i)
        if (s->symbols[i] == symbol)
            return fail(k, "A constructor's symbol must be new to the signature."), 0;
    if (!admission_context(k, s, tf.context, symbol))
        return 0;
    cc_constructor c = {.symbol = symbol, .type = tf.term};
    if (!constructor_shape(&sh, tf.term, &c))
        return 0;
    for (uint32_t j = 0; j < s->level_count; ++j)
        if (!(s->recorded & (UINT32_C(1) << j)) && ck_term_free(k, tf.term, s->symbols[j]))
            return fail(k, "A constructor type mentions an erased universe parameter; only a recorded one may occur "
                           "there (section 1.1)."), 0;
    if (k->error[0] || !add_constructor(k, s, c))
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
 * n + 1 and gives B_{n+2}(y_{n+1}, z_{n+1}). Its dimension j is index j. */
static cc_term squash_type(cc_kernel *k, const cc_signature *s) {
    uint32_t steps = s->modifier;          /* n + 2 */
    uint32_t ys[CC_TRUNCATION_MAX + 2], zs[CC_TRUNCATION_MAX + 2];
    cc_term types[CC_TRUNCATION_MAX + 2];
    cc_term b = ck_var(k, s->sort_symbol);
    for (uint32_t j = 0; j < steps && b; ++j) {
        types[j] = b;
        ys[j] = ck_fresh_symbol(k);
        zs[j] = ck_fresh_symbol(k);
        b = ck_make(k, CC_PATH, j, b, ck_var(k, ys[j]), ck_var(k, zs[j]), 0);
    }
    for (uint32_t j = steps; j-- > 0 && b;) {
        b = ck_make(k, CC_PI, zs[j], types[j], b, 0, 0);
        b = ck_make(k, CC_PI, ys[j], types[j], b, 0, 0);
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
        cc_constructor c = {.symbol = ck_fresh_symbol(k), .generated = true};
        c.type = squash_type(k, s);
        shape sh = {.k = k, .signature = s, .constructors = s->constructor_count, .self = c.symbol};
        /* The generated type is checked like any other: a sanity check. */
        if (!c.type || !constructor_shape(&sh, c.type, &c) || !add_constructor(k, s, c))
            return 0;
    }
    s->admitted = true;
    return index;
}

/* ---- Reading the table ---------------------------------------------------- */

size_t cc_kernel_signature_count(const cc_kernel *k) { return k && k->signature_count ? k->signature_count : 1; }

bool cc_kernel_signature(const cc_kernel *k, uint32_t index, cc_signature_info *info) {
    if (!k || !info || !index || index >= k->signature_count)
        return false;
    const cc_signature *s = &k->signatures[index];
    *info = (cc_signature_info){s->admitted, s->experimental, s->modifier, s->sort_symbol, s->level_count,
                                s->parameter_count, s->constructor_count, s->recorded, s->former, s->level};
    return true;
}

uint32_t cc_kernel_signature_symbol(const cc_kernel *k, uint32_t index, uint32_t position) {
    if (!k || !index || index >= k->signature_count)
        return 0;
    const cc_signature *s = &k->signatures[index];
    return position < s->level_count + s->parameter_count ? s->symbols[position] : 0;
}

bool cc_kernel_signature_constructor(const cc_kernel *k, uint32_t index, uint32_t constructor,
                                     cc_constructor_info *info) {
    if (!k || !info || !index || index >= k->signature_count)
        return false;
    const cc_signature *s = &k->signatures[index];
    if (constructor >= s->constructor_count)
        return false;
    const cc_constructor *c = &s->constructors[constructor];
    *info = (cc_constructor_info){c->symbol, c->data, c->positions, c->dimensions, c->type, c->generated};
    return true;
}
