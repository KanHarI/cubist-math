/* Instructions: THTH-style forward rules on a graph of judgements. Each
 * instruction checks its side conditions syntactically (ck_alpha_equal) and
 * publishes one judgement, recording the instruction and operands that
 * derived it; nothing is reduced or unfolded except where an equality
 * instruction names the position and the rule. The graph is append-only, a
 * failed instruction publishes nothing, and a repeated one is shared.
 *
 * Invariants: the free term variables and dimensions of a judgement's terms
 * are entries of its context; a context is closed under the entries' own
 * dependencies; term entries have distinct symbols, and dimension entries
 * distinct indices. Binders discharge exactly one entry. */
#include "term_internal.h"

static void *reserve(cc_kernel *k, void *items, size_t *capacity, size_t needed, size_t size) {
    if (needed <= *capacity)
        return items;
    if (needed > UINT32_MAX)
        return ck_fail(k, "Instruction store handle space exhausted."), NULL;
    size_t next = *capacity ? *capacity : 64;
    while (next < needed)
        next *= 2;
    if (next > SIZE_MAX / size)
        return ck_fail(k, "Instruction store allocation overflow."), NULL;
    void *grown = realloc(items, next * size);
    if (!grown)
        return ck_fail(k, "Instruction store allocation failed."), NULL;
    *capacity = next;
    return grown;
}

/* Each instruction is one operation with its own budget. An instruction does
 * nothing while an earlier error is recorded. */
static bool ready(cc_kernel *k) {
    if (!k || k->error[0])
        return false;
    k->budget = k->operation_budget;
    k->recursion = 0;
    if (k->fact_count)
        return true;
    cc_fact *facts = reserve(k, k->facts, &k->fact_capacity, 1, sizeof *facts);
    if (facts) k->facts = facts;
    cc_entry *entries = reserve(k, k->entries, &k->entry_capacity, 1, sizeof *entries);
    if (entries) k->entries = entries;
    cc_context_set *sets = reserve(k, k->context_sets, &k->context_set_capacity, 1, sizeof *sets);
    if (sets) k->context_sets = sets;
    if (!facts || !entries || !sets)
        return false;
    k->facts[0] = (cc_fact){0};
    k->entries[0] = (cc_entry){0};
    k->context_sets[0] = (cc_context_set){0};
    k->fact_count = k->entry_count = k->context_set_count = 1;
    k->context_item_count = 0;
    return true;
}

/* ---- The derivation graph ---------------------------------------------- */

static uint32_t derivation_hash(const cc_derivation *d, const uint8_t *position) {
    uint32_t words[] = {d->rule, d->premise[0], d->premise[1], d->premise[2], d->premise[3],
                        d->entry, d->operand[0], d->operand[1], d->depth};
    uint32_t hash = UINT32_C(2166136261);
    for (size_t i = 0; i < sizeof words / sizeof *words; ++i)
        hash = (hash ^ words[i]) * UINT32_C(16777619);
    for (uint32_t i = 0; i < d->depth; ++i)
        hash = (hash ^ position[i]) * UINT32_C(16777619);
    return hash;
}

static bool same_derivation(const cc_kernel *k, const cc_derivation *a, const uint8_t *position, const cc_derivation *b) {
    if (a->rule != b->rule || memcmp(a->premise, b->premise, sizeof a->premise) || a->entry != b->entry ||
        memcmp(a->operand, b->operand, sizeof a->operand) || a->depth != b->depth)
        return false;
    for (uint32_t i = 0; i < a->depth; ++i)
        if (position[i] != k->positions[b->position + i]) return false;
    return true;
}

/* Index the facts by derivation. Truncated ids act as tombstones, and a
 * slot may name an id that was truncated and issued again; lookups compare
 * the whole derivation, so both only cost time. A failed allocation only
 * forgoes sharing. */
static void remember(cc_kernel *k, cc_judgement_id id) {
    if ((k->derivation_used + 1) * 2 > k->derivation_capacity) {
        size_t capacity = 1024;
        while (capacity < 4 * k->fact_count && capacity < SIZE_MAX / 8) capacity *= 2;
        uint32_t *table = calloc(capacity, sizeof *table);
        if (!table)
            return;
        free(k->derivations);
        k->derivations = table;
        k->derivation_capacity = capacity;
        k->derivation_used = 0;
        for (cc_judgement_id old = 1; old < id; ++old)
            remember(k, old);
    }
    const cc_fact *fact = &k->facts[id];
    size_t mask = k->derivation_capacity - 1;
    size_t slot = derivation_hash(&fact->how, k->positions + fact->how.position) & mask;
    while (k->derivations[slot] && k->derivations[slot] < k->fact_count)
        slot = (slot + 1) & mask;
    if (!k->derivations[slot])
        ++k->derivation_used;
    k->derivations[slot] = id;
}

/* Start an instruction. It proceeds only when it is new: the judgement of
 * an identical earlier instruction is returned instead, as is 0 on error. */
static bool begin(cc_kernel *k, cc_derivation how, const uint8_t *position, size_t depth, cc_judgement_id *found) {
    *found = 0;
    if (!ready(k))
        return false;
    if (depth > 1024)
        return ck_fail(k, "Position depth exceeded.");
    if (depth && !position)
        return ck_fail(k, "Missing position.");
    how.depth = (uint32_t)depth;
    k->pending = how;
    k->pending_position = position;
    if (k->derivation_capacity) {
        size_t mask = k->derivation_capacity - 1;
        for (size_t slot = derivation_hash(&how, position) & mask; k->derivations[slot]; slot = (slot + 1) & mask) {
            cc_judgement_id id = k->derivations[slot];
            if (id < k->fact_count && same_derivation(k, &how, position, &k->facts[id].how)) {
                *found = id;
                return false;
            }
        }
    }
    return true;
}

static bool premise(cc_kernel *k, cc_judgement_id id, uint32_t kind, cc_fact *out) {
    if (!id || id >= k->fact_count)
        return ck_fail(k, "Unknown judgement.");
    if (k->facts[id].kind != kind)
        return ck_fail(k, kind == CC_FACT_TYPING ? "Expected a typing judgement." : "Expected an equality judgement.");
    *out = k->facts[id];
    return true;
}

static bool entry(cc_kernel *k, cc_entry_id id, bool dimension, cc_entry *out) {
    if (!id || id >= k->entry_count)
        return ck_fail(k, "Unknown context entry.");
    if (k->entries[id].dimension != dimension)
        return ck_fail(k, dimension ? "Expected a dimension entry." : "Expected a term entry.");
    *out = k->entries[id];
    return true;
}

static cc_judgement_id publish(cc_kernel *k, uint32_t kind, cc_term term, cc_term other, cc_term type, uint32_t context) {
    if (k->error[0] || !term || !type || (kind == CC_FACT_EQUALITY && !other))
        return 0;
    cc_fact *facts = reserve(k, k->facts, &k->fact_capacity, k->fact_count + 1, sizeof *facts);
    if (!facts)
        return 0;
    k->facts = facts;
    cc_derivation how = k->pending;
    if (how.depth) {
        uint8_t *positions = reserve(k, k->positions, &k->position_capacity, k->position_count + how.depth, 1);
        if (!positions)
            return 0;
        k->positions = positions;
        memcpy(positions + k->position_count, k->pending_position, how.depth);
        how.position = (uint32_t)k->position_count;
        k->position_count += how.depth;
    }
    cc_judgement_id id = (cc_judgement_id)k->fact_count++;
    k->facts[id] = (cc_fact){kind, term, other, type, context, how, 0};
    remember(k, id);
    return id;
}

static cc_judgement_id typing(cc_kernel *k, cc_term term, cc_term type, uint32_t context) {
    return publish(k, CC_FACT_TYPING, term, 0, type, context);
}

/* A mismatch keeps the two terms for diagnostics, as conversion does. */
static bool same(cc_kernel *k, cc_term found, cc_term expected, const char *message) {
    if (ck_alpha_equal(k, found, expected))
        return true;
    if (k->error[0])
        return false;
    k->mismatch_found = found;
    k->mismatch_expected = expected;
    return ck_fail_as(k, CC_ERROR_MISMATCH, message);
}

static bool universe(cc_kernel *k, cc_term type, uint32_t *level) {
    if (!type || k->nodes[type].kind != CC_U)
        return ck_fail(k, "Expected a type: a term of a universe.");
    *level = k->nodes[type].payload;
    return true;
}

static cc_term make(cc_kernel *k, cc_term_kind kind, uint32_t payload, cc_term a, cc_term b, cc_term c, cc_term d) {
    return ck_make(k, kind, payload, a, b, c, d);
}

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return make(k, CC_APP, 0, f, x, 0, 0);
}

/* ---- Contexts ---------------------------------------------------------- */

static bool contains(const cc_kernel *k, uint32_t set, cc_entry_id id) {
    cc_context_set s = k->context_sets[set];
    const uint32_t *items = k->context_items + s.offset;
    size_t low = 0, high = s.count;
    while (low < high) {
        size_t middle = low + (high - low) / 2;
        if (items[middle] == id) return true;
        if (items[middle] < id) low = middle + 1;
        else high = middle;
    }
    return false;
}

/* Publish the count items written after the last set as a new set. The
 * empty context is always set zero, so closed judgements are recognized. */
static bool publish_set(cc_kernel *k, uint32_t count, uint32_t *out) {
    if (!count) { *out = 0; return true; }
    cc_context_set *sets = reserve(k, k->context_sets, &k->context_set_capacity, k->context_set_count + 1, sizeof *sets);
    if (!sets)
        return false;
    k->context_sets = sets;
    k->context_sets[k->context_set_count] = (cc_context_set){k->context_item_count, count};
    k->context_item_count += count;
    *out = (uint32_t)k->context_set_count++;
    return true;
}

static uint32_t *scratch(cc_kernel *k, size_t count) {
    uint32_t *items = reserve(k, k->context_items, &k->context_item_capacity, k->context_item_count + count + 1, sizeof *items);
    if (items) k->context_items = items;
    return items ? items + k->context_item_count : NULL;
}

/* The union of two contexts. Distinct dimension entries with one index
 * would make a dimension name ambiguous, so they never meet. */
static bool merge(cc_kernel *k, uint32_t a, uint32_t b, uint32_t *out) {
    if (k->error[0])
        return false;
    if (a == b || !b) { *out = a; return true; }
    if (!a) { *out = b; return true; }
    cc_context_set left = k->context_sets[a], right = k->context_sets[b];
    uint32_t *z = scratch(k, (size_t)left.count + right.count);
    if (!z)
        return false;
    const uint32_t *x = k->context_items + left.offset, *y = k->context_items + right.offset;
    uint32_t i = 0, j = 0, n = 0;
    uint64_t dimensions = 0;
    while (i < left.count || j < right.count) {
        uint32_t next;
        if (j == right.count || (i < left.count && x[i] < y[j])) next = x[i++];
        else if (i == left.count || y[j] < x[i]) next = y[j++];
        else { next = x[i++]; ++j; }
        cc_entry e = k->entries[next];
        if (e.dimension) {
            uint64_t bit = UINT64_C(1) << e.symbol;
            if (dimensions & bit)
                return ck_fail(k, "Two dimension entries with one index meet in a context.");
            dimensions |= bit;
        }
        z[n++] = next;
    }
    if (n == left.count) { *out = a; return true; }
    if (n == right.count) { *out = b; return true; }
    return publish_set(k, n, out);
}

static bool merge3(cc_kernel *k, uint32_t a, uint32_t b, uint32_t c, uint32_t *out) {
    uint32_t ab;
    return merge(k, a, b, &ab) && merge(k, ab, c, out);
}

/* Remove entries from a context. A remaining entry must not depend on a
 * removed one, and must not be another dimension entry with a removed
 * dimension's index: the binder would capture it. */
static bool discharge(cc_kernel *k, uint32_t set, const cc_entry_id *removed, size_t count, uint32_t *out) {
    if (k->error[0])
        return false;
    cc_context_set s = k->context_sets[set];
    uint32_t *z = scratch(k, s.count);
    if (!z)
        return false;
    const uint32_t *items = k->context_items + s.offset;
    uint32_t n = 0;
    for (uint32_t i = 0; i < s.count; ++i) {
        cc_entry e = k->entries[items[i]];
        bool gone = false;
        for (size_t r = 0; r < count && !gone; ++r) {
            cc_entry binder = k->entries[removed[r]];
            gone = items[i] == removed[r];
            if (!gone && contains(k, e.context, removed[r]))
                return ck_fail(k, "A context entry still depends on the discharged entry.");
            if (!gone && e.dimension && binder.dimension && e.symbol == binder.symbol)
                return ck_fail(k, "The binder would capture another dimension entry with its index.");
        }
        if (!gone)
            z[n++] = items[i];
    }
    if (n == s.count) { *out = set; return true; }
    return publish_set(k, n, out);
}

/* The context of a binder over entry e: the body's, without e, with e's. */
static bool bind(cc_kernel *k, uint32_t body, cc_entry_id e, uint32_t *out) {
    uint32_t rest;
    return discharge(k, body, &e, 1, &rest) && merge(k, rest, k->entries[e].context, out);
}

/* Term entries by symbol. A slot holding a truncated id is free again, and
 * lookups compare the entry, so a stale slot only costs time. */
static size_t symbol_slot(uint32_t symbol, size_t capacity) {
    return (size_t)(symbol * UINT32_C(2654435761)) & (capacity - 1);
}

static cc_entry_id find_entry(const cc_kernel *k, uint32_t symbol) {
    if (!k->entry_index_capacity)
        return 0;
    size_t mask = k->entry_index_capacity - 1;
    for (size_t slot = symbol_slot(symbol, k->entry_index_capacity); k->entry_index[slot]; slot = (slot + 1) & mask) {
        cc_entry_id id = k->entry_index[slot];
        if (id < k->entry_count && !k->entries[id].dimension && k->entries[id].symbol == symbol)
            return id;
    }
    return 0;
}

/* A failed allocation only forgoes the index: find_entry then misses, and
 * extend's uniqueness check would too, so it fails the instruction. */
static void index_entry(cc_kernel *k, cc_entry_id id) {
    if ((k->entry_index_used + 1) * 2 > k->entry_index_capacity) {
        size_t capacity = 256;
        while (capacity < 4 * k->entry_count && capacity < SIZE_MAX / 8) capacity *= 2;
        uint32_t *table = calloc(capacity, sizeof *table);
        if (!table) { ck_fail(k, "Entry index allocation failed."); return; }
        free(k->entry_index);
        k->entry_index = table;
        k->entry_index_capacity = capacity;
        k->entry_index_used = 0;
        for (cc_entry_id old = 1; old < id; ++old)
            if (!k->entries[old].dimension) index_entry(k, old);
    }
    size_t mask = k->entry_index_capacity - 1, slot = symbol_slot(k->entries[id].symbol, k->entry_index_capacity);
    while (k->entry_index[slot] && k->entry_index[slot] < k->entry_count && k->entry_index[slot] != id)
        slot = (slot + 1) & mask;
    if (!k->entry_index[slot]) ++k->entry_index_used;
    k->entry_index[slot] = id;
}

/* A term entry is named by its symbol: extending with the same type
 * judgement and symbol again returns the same entry. */
cc_entry_id cc_instr_extend(cc_kernel *k, cc_judgement_id type, uint32_t symbol) {
    cc_fact t = {0};
    uint32_t level = 0;
    if (!ready(k) || !premise(k, type, CC_FACT_TYPING, &t) || !universe(k, t.type, &level))
        return 0;
    if (!symbol)
        return ck_fail(k, "A context entry needs a symbol."), 0;
    /* The same name at the same type, however that type was derived, is the
     * same entry: its own judgement justifies its type. Contexts are then
     * canonical, one entry per name. */
    cc_entry_id named = find_entry(k, symbol);
    if (named) {
        if (k->entries[named].source == type || ck_alpha_equal(k, k->entries[named].type, t.term))
            return named;
        if (!k->error[0])
            ck_fail(k, "The symbol already names a context entry.");
        return 0;
    }
    if (!ck_var(k, symbol))
        return 0;
    cc_entry *entries = reserve(k, k->entries, &k->entry_capacity, k->entry_count + 1, sizeof *entries);
    if (!entries)
        return 0;
    k->entries = entries;
    /* The entry is published last, once its scope exists. */
    cc_entry_id id = (cc_entry_id)k->entry_count;
    uint32_t *self = scratch(k, 1), scope = 0;
    if (!self)
        return 0;
    *self = id;
    k->entries[id] = (cc_entry){symbol, t.term, level, t.context, 0, type, false};
    if (!publish_set(k, 1, &scope) || !merge(k, t.context, scope, &scope))
        return 0;
    k->entries[id].scope = scope;
    ++k->entry_count;
    index_entry(k, id);
    return id;
}

static cc_entry_id dimension_entry(cc_kernel *k, unsigned index);

cc_entry_id cc_instr_dimension(cc_kernel *k, unsigned index) {
    if (!ready(k))
        return 0;
    return dimension_entry(k, index);
}

static cc_entry_id dimension_entry(cc_kernel *k, unsigned index) {
    if (index >= CC_DIMENSIONS)
        return ck_fail(k, "Dimension outside the native range."), 0;
    cc_entry_id cached = k->dimension_entries[index];
    if (cached && cached < k->entry_count && k->entries[cached].dimension && k->entries[cached].symbol == index)
        return cached;
    cc_entry *entries = reserve(k, k->entries, &k->entry_capacity, k->entry_count + 1, sizeof *entries);
    if (!entries)
        return 0;
    k->entries = entries;
    cc_entry_id id = (cc_entry_id)k->entry_count;
    uint32_t *self = scratch(k, 1), scope = 0;
    if (!self)
        return 0;
    *self = id;
    k->entries[id] = (cc_entry){index, 0, 0, 0, 0, 0, true};
    if (!publish_set(k, 1, &scope))
        return 0;
    k->entries[id].scope = scope;
    ++k->entry_count;
    k->dimension_entries[index] = id;
    return id;
}

cc_judgement_id cc_instr_variable(cc_kernel *k, cc_entry_id id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_VARIABLE, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    if (!entry(k, id, false, &e))
        return 0;
    return typing(k, ck_var(k, e.symbol), e.type, e.scope);
}

/* ---- Universes and inductive types -------------------------------------- */

cc_judgement_id cc_instr_universe(cc_kernel *k, uint32_t level) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_UNIVERSE, .operand = {level}}, NULL, 0, &found))
        return found;
    if (level == UINT32_MAX)
        return ck_fail(k, "Universe successor overflow."), 0;
    return typing(k, make(k, CC_U, level, 0, 0, 0, 0), make(k, CC_U, level + 1, 0, 0, 0, 0), 0);
}

static cc_judgement_id constant(cc_kernel *k, cc_instruction rule, cc_term_kind kind, cc_term_kind type) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = rule}, NULL, 0, &found))
        return found;
    return typing(k, make(k, kind, 0, 0, 0, 0, 0), make(k, type, 0, 0, 0, 0, 0), 0);
}

cc_judgement_id cc_instr_nat(cc_kernel *k) { return constant(k, CC_INSTR_NAT, CC_NAT, CC_U); }
cc_judgement_id cc_instr_unit(cc_kernel *k) { return constant(k, CC_INSTR_UNIT, CC_UNIT, CC_U); }
cc_judgement_id cc_instr_void(cc_kernel *k) { return constant(k, CC_INSTR_VOID, CC_VOID, CC_U); }
cc_judgement_id cc_instr_zero(cc_kernel *k) { return constant(k, CC_INSTR_ZERO, CC_ZERO, CC_NAT); }
cc_judgement_id cc_instr_point(cc_kernel *k) { return constant(k, CC_INSTR_POINT, CC_POINT, CC_UNIT); }

cc_judgement_id cc_instr_succ(cc_kernel *k, cc_judgement_id value) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SUCC, .premise = {value}}, NULL, 0, &found))
        return found;
    cc_fact n = {0};
    if (!premise(k, value, CC_FACT_TYPING, &n) ||
        !same(k, n.type, make(k, CC_NAT, 0, 0, 0, 0, 0), "succ needs a natural number."))
        return 0;
    return typing(k, make(k, CC_SUCC, 0, n.term, 0, 0, 0), n.type, n.context);
}

/* A motive over the type domain: P : Π(x : domain). U(l). */
static bool motive(cc_kernel *k, cc_fact p, cc_term domain) {
    cc_node pi = k->nodes[p.type];
    if (pi.kind != CC_PI || k->nodes[pi.child[1]].kind != CC_U)
        return ck_fail(k, "A motive is a family of types: Π(x : A). U(l).");
    return same(k, pi.child[0], domain, "The motive is a family over another type.");
}

cc_judgement_id cc_instr_nat_elim(cc_kernel *k, cc_judgement_id motive_id, cc_judgement_id zero_id,
                                  cc_judgement_id step_id, cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_NAT_ELIM, .premise = {motive_id, zero_id, step_id, value_id}}, NULL, 0, &found))
        return found;
    cc_fact p = {0}, z = {0}, s = {0}, n = {0};
    if (!premise(k, motive_id, CC_FACT_TYPING, &p) || !premise(k, zero_id, CC_FACT_TYPING, &z) ||
        !premise(k, step_id, CC_FACT_TYPING, &s) || !premise(k, value_id, CC_FACT_TYPING, &n))
        return 0;
    cc_term nat = make(k, CC_NAT, 0, 0, 0, 0, 0);
    uint32_t predecessor = ck_fresh_symbol(k), hypothesis = ck_fresh_symbol(k);
    cc_term pred = ck_var(k, predecessor);
    cc_term step_type = make(k, CC_PI, predecessor, nat,
        make(k, CC_PI, hypothesis, app(k, p.term, pred), app(k, p.term, make(k, CC_SUCC, 0, pred, 0, 0, 0)), 0, 0), 0, 0);
    uint32_t context = 0;
    if (!motive(k, p, nat) || !same(k, n.type, nat, "Induction on a natural number needs a natural number.") ||
        !same(k, z.type, app(k, p.term, make(k, CC_ZERO, 0, 0, 0, 0, 0)), "The zero case has the wrong type.") ||
        !same(k, s.type, step_type, "The successor case has the wrong type.") ||
        !merge(k, p.context, z.context, &context) || !merge3(k, context, s.context, n.context, &context))
        return 0;
    return typing(k, make(k, CC_NATREC, 0, p.term, z.term, s.term, n.term), app(k, p.term, n.term), context);
}

cc_judgement_id cc_instr_unit_elim(cc_kernel *k, cc_judgement_id motive_id, cc_judgement_id point_id,
                                   cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_UNIT_ELIM, .premise = {motive_id, point_id, value_id}}, NULL, 0, &found))
        return found;
    cc_fact p = {0}, b = {0}, u = {0};
    uint32_t context = 0;
    if (!premise(k, motive_id, CC_FACT_TYPING, &p) || !premise(k, point_id, CC_FACT_TYPING, &b) ||
        !premise(k, value_id, CC_FACT_TYPING, &u))
        return 0;
    cc_term unit = make(k, CC_UNIT, 0, 0, 0, 0, 0);
    if (!motive(k, p, unit) || !same(k, u.type, unit, "Unit induction needs a unit value.") ||
        !same(k, b.type, app(k, p.term, make(k, CC_POINT, 0, 0, 0, 0, 0)), "The point case has the wrong type.") ||
        !merge3(k, p.context, b.context, u.context, &context))
        return 0;
    return typing(k, make(k, CC_UNITREC, 0, p.term, b.term, u.term, 0), app(k, p.term, u.term), context);
}

cc_judgement_id cc_instr_abort(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id impossible_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_ABORT, .premise = {type_id, impossible_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, e = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, &t) || !premise(k, impossible_id, CC_FACT_TYPING, &e) ||
        !universe(k, t.type, &level) ||
        !same(k, e.type, make(k, CC_VOID, 0, 0, 0, 0, 0), "abort needs an element of the empty type.") ||
        !merge(k, t.context, e.context, &context))
        return 0;
    return typing(k, make(k, CC_ABORT, 0, t.term, e.term, 0, 0), t.term, context);
}

cc_judgement_id cc_instr_sum(cc_kernel *k, cc_judgement_id left_id, cc_judgement_id right_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SUM, .premise = {left_id, right_id}}, NULL, 0, &found))
        return found;
    cc_fact a = {0}, b = {0};
    uint32_t left = 0, right = 0, context = 0;
    if (!premise(k, left_id, CC_FACT_TYPING, &a) || !premise(k, right_id, CC_FACT_TYPING, &b) ||
        !universe(k, a.type, &left) || !universe(k, b.type, &right) || !merge(k, a.context, b.context, &context))
        return 0;
    return typing(k, make(k, CC_SUM, 0, a.term, b.term, 0, 0), make(k, CC_U, left > right ? left : right, 0, 0, 0, 0), context);
}

cc_judgement_id cc_instr_inject(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id value_id, bool right) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_INJECT, .premise = {type_id, value_id}, .operand = {right}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, v = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, &t) || !premise(k, value_id, CC_FACT_TYPING, &v) ||
        !universe(k, t.type, &level))
        return 0;
    cc_node sum = k->nodes[t.term];
    if (sum.kind != CC_SUM)
        return ck_fail(k, "An injection needs a sum type."), 0;
    if (!same(k, v.type, sum.child[right ? 1 : 0], "The injected value has the wrong type.") ||
        !merge(k, t.context, v.context, &context))
        return 0;
    return typing(k, make(k, right ? CC_INR : CC_INL, 0, t.term, v.term, 0, 0), t.term, context);
}

cc_judgement_id cc_instr_sum_elim(cc_kernel *k, cc_judgement_id motive_id, cc_judgement_id left_id,
                                  cc_judgement_id right_id, cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SUM_ELIM, .premise = {motive_id, left_id, right_id, value_id}}, NULL, 0, &found))
        return found;
    cc_fact p = {0}, cases[2] = {0}, v = {0};
    uint32_t context = 0;
    if (!premise(k, motive_id, CC_FACT_TYPING, &p) || !premise(k, left_id, CC_FACT_TYPING, &cases[0]) ||
        !premise(k, right_id, CC_FACT_TYPING, &cases[1]) || !premise(k, value_id, CC_FACT_TYPING, &v))
        return 0;
    cc_node sum = k->nodes[v.type];
    if (sum.kind != CC_SUM)
        return ck_fail(k, "Sum induction needs a value of a sum type."), 0;
    if (!motive(k, p, v.type))
        return 0;
    for (unsigned side = 0; side < 2; ++side) {
        uint32_t name = ck_fresh_symbol(k);
        cc_term injected = make(k, side ? CC_INR : CC_INL, 0, v.type, ck_var(k, name), 0, 0);
        if (!same(k, cases[side].type, make(k, CC_PI, name, sum.child[side], app(k, p.term, injected), 0, 0),
                  side ? "The right case has the wrong type." : "The left case has the wrong type."))
            return 0;
    }
    if (!merge(k, p.context, cases[0].context, &context) || !merge3(k, context, cases[1].context, v.context, &context))
        return 0;
    return typing(k, make(k, CC_SUMREC, 0, p.term, cases[0].term, cases[1].term, v.term), app(k, p.term, v.term), context);
}

/* ---- Functions and pairs ------------------------------------------------ */

static cc_judgement_id former(cc_kernel *k, cc_term_kind kind, cc_entry_id id, cc_judgement_id family) {
    cc_judgement_id found;
    unsigned rule = kind == CC_PI ? CC_INSTR_PI : kind == CC_SIGMA ? CC_INSTR_SIGMA : CC_INSTR_W;
    if (!begin(k, (cc_derivation){.rule = rule, .premise = {family}, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    cc_fact b = {0};
    uint32_t level = 0, context = 0;
    if (!entry(k, id, false, &e) || !premise(k, family, CC_FACT_TYPING, &b) ||
        !universe(k, b.type, &level) || !bind(k, b.context, id, &context))
        return 0;
    return typing(k, make(k, kind, e.symbol, e.type, b.term, 0, 0),
                  make(k, CC_U, e.level > level ? e.level : level, 0, 0, 0, 0), context);
}

cc_judgement_id cc_instr_pi(cc_kernel *k, cc_entry_id id, cc_judgement_id codomain) {
    return former(k, CC_PI, id, codomain);
}

cc_judgement_id cc_instr_sigma(cc_kernel *k, cc_entry_id id, cc_judgement_id family) {
    return former(k, CC_SIGMA, id, family);
}

cc_judgement_id cc_instr_lambda(cc_kernel *k, cc_entry_id id, cc_judgement_id body_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_LAMBDA, .premise = {body_id}, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    cc_fact b = {0};
    uint32_t context = 0;
    if (!entry(k, id, false, &e) || !premise(k, body_id, CC_FACT_TYPING, &b) ||
        !bind(k, b.context, id, &context))
        return 0;
    return typing(k, make(k, CC_LAM, e.symbol, e.type, b.term, 0, 0), make(k, CC_PI, e.symbol, e.type, b.type, 0, 0), context);
}

cc_judgement_id cc_instr_apply(cc_kernel *k, cc_judgement_id function, cc_judgement_id argument) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_APPLY, .premise = {function, argument}}, NULL, 0, &found))
        return found;
    cc_fact f = {0}, a = {0};
    uint32_t context = 0;
    if (!premise(k, function, CC_FACT_TYPING, &f) || !premise(k, argument, CC_FACT_TYPING, &a))
        return 0;
    cc_node pi = k->nodes[f.type];
    if (pi.kind != CC_PI)
        return ck_fail(k, "Only a term of a Π type can be applied."), 0;
    if (!same(k, a.type, pi.child[0], "The argument has the wrong type.") || !merge(k, f.context, a.context, &context))
        return 0;
    return typing(k, app(k, f.term, a.term), ck_substitute(k, pi.child[1], pi.payload, a.term), context);
}

cc_judgement_id cc_instr_pair(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id first_id, cc_judgement_id second_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PAIR, .premise = {type_id, first_id, second_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, a = {0}, b = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, &t) || !premise(k, first_id, CC_FACT_TYPING, &a) ||
        !premise(k, second_id, CC_FACT_TYPING, &b) || !universe(k, t.type, &level))
        return 0;
    cc_node sigma = k->nodes[t.term];
    if (sigma.kind != CC_SIGMA)
        return ck_fail(k, "A pair needs a Σ type."), 0;
    if (!same(k, a.type, sigma.child[0], "The first component has the wrong type.") ||
        !same(k, b.type, ck_substitute(k, sigma.child[1], sigma.payload, a.term), "The second component has the wrong type.") ||
        !merge3(k, t.context, a.context, b.context, &context))
        return 0;
    return typing(k, make(k, CC_PAIR, 0, t.term, a.term, b.term, 0), t.term, context);
}

static cc_judgement_id projection(cc_kernel *k, cc_judgement_id pair, bool second) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = second ? CC_INSTR_SECOND : CC_INSTR_FIRST, .premise = {pair}}, NULL, 0, &found))
        return found;
    cc_fact p = {0};
    if (!premise(k, pair, CC_FACT_TYPING, &p))
        return 0;
    cc_node sigma = k->nodes[p.type];
    if (sigma.kind != CC_SIGMA)
        return ck_fail(k, "Only a term of a Σ type has projections."), 0;
    cc_term first = make(k, CC_FST, 0, p.term, 0, 0, 0);
    if (!second)
        return typing(k, first, sigma.child[0], p.context);
    return typing(k, make(k, CC_SND, 0, p.term, 0, 0, 0), ck_substitute(k, sigma.child[1], sigma.payload, first), p.context);
}

cc_judgement_id cc_instr_first(cc_kernel *k, cc_judgement_id pair) { return projection(k, pair, false); }
cc_judgement_id cc_instr_second(cc_kernel *k, cc_judgement_id pair) { return projection(k, pair, true); }

/* The parts of a type former are types in its universe, by cumulativity:
 * the domain of Π(x : A). B, Σ(x : A). B or W(x : A). B, and its family
 * B[a/x] at a : A. */
cc_judgement_id cc_instr_domain(cc_kernel *k, cc_judgement_id type_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_DOMAIN, .premise = {type_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0};
    uint32_t level = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, &t) || !universe(k, t.type, &level))
        return 0;
    cc_node former = k->nodes[t.term];
    if (former.kind != CC_PI && former.kind != CC_SIGMA && former.kind != CC_W)
        return ck_fail(k, "Only a Π, Σ or W type has a domain."), 0;
    return typing(k, former.child[0], t.type, t.context);
}

cc_judgement_id cc_instr_family(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id argument) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_FAMILY, .premise = {type_id, argument}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, a = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, &t) || !premise(k, argument, CC_FACT_TYPING, &a) ||
        !universe(k, t.type, &level))
        return 0;
    cc_node former = k->nodes[t.term];
    if (former.kind != CC_PI && former.kind != CC_SIGMA && former.kind != CC_W)
        return ck_fail(k, "Only a Π, Σ or W type has a family."), 0;
    if (!same(k, a.type, former.child[0], "The argument has the wrong type.") || !merge(k, t.context, a.context, &context))
        return 0;
    return typing(k, ck_substitute(k, former.child[1], former.payload, a.term), t.type, context);
}

/* ---- Paths -------------------------------------------------------------- */

cc_judgement_id cc_instr_path(cc_kernel *k, cc_entry_id dimension, cc_judgement_id family_id,
                              cc_judgement_id left_id, cc_judgement_id right_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PATH, .premise = {family_id, left_id, right_id}, .entry = dimension}, NULL, 0, &found))
        return found;
    cc_entry i = {0};
    cc_fact a = {0}, l = {0}, r = {0};
    uint32_t level = 0, context = 0;
    if (!entry(k, dimension, true, &i) || !premise(k, family_id, CC_FACT_TYPING, &a) ||
        !premise(k, left_id, CC_FACT_TYPING, &l) || !premise(k, right_id, CC_FACT_TYPING, &r) ||
        !universe(k, a.type, &level) ||
        !same(k, l.type, ck_endpoint_term(k, a.term, i.symbol, 0), "The left endpoint has the wrong type.") ||
        !same(k, r.type, ck_endpoint_term(k, a.term, i.symbol, 1), "The right endpoint has the wrong type.") ||
        !bind(k, a.context, dimension, &context) || !merge3(k, context, l.context, r.context, &context))
        return 0;
    return typing(k, make(k, CC_PATH, i.symbol, a.term, l.term, r.term, 0), a.type, context);
}

cc_judgement_id cc_instr_path_lambda(cc_kernel *k, cc_entry_id dimension, cc_judgement_id body_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PATH_LAMBDA, .premise = {body_id}, .entry = dimension}, NULL, 0, &found))
        return found;
    cc_entry i = {0};
    cc_fact b = {0};
    uint32_t context = 0;
    if (!entry(k, dimension, true, &i) || !premise(k, body_id, CC_FACT_TYPING, &b) ||
        !bind(k, b.context, dimension, &context))
        return 0;
    cc_term type = make(k, CC_PATH, i.symbol, b.type, ck_endpoint_term(k, b.term, i.symbol, 0),
                        ck_endpoint_term(k, b.term, i.symbol, 1), 0);
    return typing(k, make(k, CC_PLAM, i.symbol, b.type, b.term, 0, 0), type, context);
}

cc_judgement_id cc_instr_path_apply(cc_kernel *k, cc_judgement_id path_id, cc_entry_id dimension, unsigned endpoint) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PATH_APPLY, .premise = {path_id}, .entry = dimension, .operand = {endpoint}}, NULL, 0, &found))
        return found;
    cc_fact p = {0};
    cc_entry i = {0};
    uint32_t context = 0;
    if (!premise(k, path_id, CC_FACT_TYPING, &p) || (dimension && !entry(k, dimension, true, &i)))
        return 0;
    cc_node type = k->nodes[p.type];
    if (type.kind != CC_PATH)
        return ck_fail(k, "Only a term of a path type can be applied to a dimension."), 0;
    if (!dimension && endpoint > 1)
        return ck_fail(k, "A path applies at a dimension, 0 or 1."), 0;
    cc_formula point;
    cc_init(&point, CC_INTERVAL);
    cc_status status = dimension ? cc_generator(&point, i.symbol, true) : endpoint ? cc_one(&point) : CC_OK;
    cc_formula_id argument = status == CC_OK ? cc_kernel_formula(k, &point) : 0;
    cc_term result = argument ? ck_dimension_substitute(k, type.child[0], type.payload, &point) : 0;
    cc_clear(&point);
    if (status != CC_OK)
        return ck_fail(k, "Interval allocation failed."), 0;
    if (!result || !merge(k, p.context, dimension ? i.scope : 0, &context))
        return 0;
    return typing(k, make(k, CC_PAPP, argument, p.term, p.type, 0, 0), result, context);
}

cc_judgement_id cc_instr_endpoint(cc_kernel *k, cc_judgement_id id, cc_entry_id dimension, unsigned endpoint) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_ENDPOINT, .premise = {id}, .entry = dimension, .operand = {endpoint}},
               NULL, 0, &found))
        return found;
    cc_fact t = {0};
    cc_entry i = {0};
    uint32_t context = 0;
    if (!premise(k, id, CC_FACT_TYPING, &t) || !entry(k, dimension, true, &i))
        return 0;
    if (endpoint > 1)
        return ck_fail(k, "An endpoint is 0 or 1."), 0;
    if (!discharge(k, t.context, &dimension, 1, &context))
        return 0;
    return typing(k, ck_endpoint_term(k, t.term, i.symbol, endpoint), ck_endpoint_term(k, t.type, i.symbol, endpoint), context);
}

/* The context of the dimensions an interval or face formula names. */
static bool formula_context(cc_kernel *k, const cc_formula *f, uint32_t *out) {
    uint64_t names = 0;
    for (size_t i = 0; i < f->length; ++i) names |= f->clauses[i].positive | f->clauses[i].negative;
    *out = 0;
    for (unsigned dim = 0; dim < CC_DIMENSIONS && !k->error[0]; ++dim)
        if (names & (UINT64_C(1) << dim)) {
            cc_entry_id entry = dimension_entry(k, dim);
            if (!entry || !merge(k, *out, k->entries[entry].scope, out)) return false;
        }
    return !k->error[0];
}

cc_judgement_id cc_instr_path_at(cc_kernel *k, cc_judgement_id path_id, cc_formula_id interval) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PATH_AT, .premise = {path_id}, .operand = {interval}}, NULL, 0, &found))
        return found;
    cc_fact p = {0};
    uint32_t dims = 0, context = 0;
    if (!premise(k, path_id, CC_FACT_TYPING, &p))
        return 0;
    cc_node type = k->nodes[p.type];
    if (type.kind != CC_PATH)
        return ck_fail(k, "Only a term of a path type can be applied to an interval formula."), 0;
    const cc_formula *point = cc_kernel_get_formula(k, interval);
    if (!point || point->sort != CC_INTERVAL)
        return ck_fail(k, "A path applies at an interval formula."), 0;
    if (!formula_context(k, point, &dims) || !merge(k, p.context, dims, &context))
        return 0;
    return typing(k, make(k, CC_PAPP, interval, p.term, p.type, 0, 0),
                  ck_dimension_substitute(k, type.child[0], type.payload, point), context);
}

cc_judgement_id cc_instr_system(cc_kernel *k, cc_entry_id dimension, cc_judgement_id family_id, cc_judgement_id base_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SYSTEM, .premise = {family_id, base_id}, .entry = dimension}, NULL, 0, &found))
        return found;
    cc_entry i = {0};
    cc_fact a = {0}, b = {0};
    uint32_t level = 0, context = 0;
    if (!entry(k, dimension, true, &i) || !premise(k, family_id, CC_FACT_TYPING, &a) ||
        !premise(k, base_id, CC_FACT_TYPING, &b) || !universe(k, a.type, &level) ||
        !same(k, b.type, ck_endpoint_term(k, a.term, i.symbol, 0), "The base is not in the family at 0.") ||
        !merge(k, a.context, b.context, &context))
        return 0;
    if (ck_free_dims(k, b.term) & (UINT64_C(1) << i.symbol))
        return ck_fail(k, "The base of a composition may not use its dimension."), 0;
    cc_term comp = make(k, CC_COMP, i.symbol, a.term, 0, b.term, 0);
    return comp ? publish(k, CC_FACT_SYSTEM, comp, 0, ck_endpoint_term(k, a.term, i.symbol, 1), context) : 0;
}

static cc_term append_tube(cc_kernel *k, cc_term tubes, cc_formula_id face, cc_term tube) {
    if (!tubes)
        return make(k, CC_TUBE, face, tube, 0, 0, 0);
    cc_node n = k->nodes[tubes];
    cc_term rest = append_tube(k, n.child[1], face, tube);
    return rest ? make(k, CC_TUBE, n.payload, n.child[0], rest, 0, 0) : 0;
}

/* Where a system's tubes hang: a composition's second child, a Glue term's
 * third. Zero for a term that is not a system of tubes. */
static unsigned tube_slot(cc_kernel *k, cc_term system) {
    cc_term_kind kind = k->nodes[system].kind;
    return kind == CC_COMP ? 1 : kind == CC_GLUE_TERM ? 2 : 0;
}

/* The last tube of a system, its clause, and the tube at a position. */
static bool tube_at(cc_kernel *k, cc_term comp, uint32_t position, cc_term *term, cc_clause *clause, bool last) {
    uint32_t index = 0;
    for (cc_term cursor = k->nodes[comp].child[tube_slot(k, comp)]; cursor; cursor = k->nodes[cursor].child[1], ++index) {
        if (last ? k->nodes[cursor].child[1] != 0 : index != position)
            continue;
        const cc_formula *face = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (!face || face->length != 1)
            return ck_fail(k, "That tube's face is not one clause.");
        *term = k->nodes[cursor].child[0];
        *clause = face->clauses[0];
        return true;
    }
    return ck_fail(k, "The system has no tube at that position.");
}

static cc_judgement_id system_fact(cc_kernel *k, cc_term comp, cc_term type, uint32_t context, uint64_t pending) {
    cc_judgement_id id = publish(k, CC_FACT_SYSTEM, comp, 0, type, context);
    if (id)
        k->facts[id].pending = pending;
    return id;
}

cc_judgement_id cc_instr_system_tube(cc_kernel *k, cc_judgement_id system_id, cc_formula_id face,
                                     cc_judgement_id tube_id, cc_judgement_id adjacency_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SYSTEM_TUBE, .premise = {system_id, tube_id, adjacency_id},
                                  .operand = {face}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, u = {0}, e = {0};
    uint32_t dims = 0, context = 0;
    if (!premise(k, system_id, CC_FACT_SYSTEM, &s) || !premise(k, tube_id, CC_FACT_TYPING, &u))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    cc_node comp = k->nodes[s.term];
    if (comp.kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    unsigned dim = comp.payload;
    const cc_formula *phi = cc_kernel_get_formula(k, face);
    if (!phi || phi->sort != CC_FACE || phi->length > 1)
        return ck_fail(k, "A tube's face is one conjunction of endpoint equations, or 0."), 0;
    if (!phi->length) {
        /* On the face 0 nothing is required of the tube: it is never used. */
        if (adjacency_id)
            return ck_fail(k, "A tube on the face 0 takes no equality."), 0;
        cc_term tubes = merge(k, s.context, u.context, &context) ? append_tube(k, comp.child[1], face, u.term) : 0;
        cc_term extended = tubes ? make(k, CC_COMP, dim, comp.child[0], tubes, comp.child[2], 0) : 0;
        return extended ? system_fact(k, extended, s.type, context, 0) : 0;
    }
    if (!premise(k, adjacency_id, CC_FACT_EQUALITY, &e))
        return 0;
    cc_clause clause = phi->clauses[0];
    uint64_t names = clause.positive | clause.negative;
    if (clause.positive & clause.negative)
        return ck_fail(k, "A tube's face must be consistent."), 0;
    if (names & (UINT64_C(1) << dim))
        return ck_fail(k, "A tube's face may not use the composition's dimension."), 0;
    if (ck_free_dims(k, u.term) & names)
        return ck_fail(k, "A tube must already be restricted to its face."), 0;
    /* Every earlier tube whose face meets this one's must agree with it on
     * the overlap: SystemOverlap, once for each. */
    uint64_t pending = 0;
    uint32_t index = 0;
    for (cc_term cursor = comp.child[1]; cursor; cursor = k->nodes[cursor].child[1], ++index) {
        const cc_formula *other_face = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (!other_face->length)
            continue;
        cc_clause other = other_face->clauses[0];
        if ((clause.positive | other.positive) & (clause.negative | other.negative))
            continue;
        if (index >= 64)
            return ck_fail(k, "A tube may overlap only the first 64 tubes of a system."), 0;
        pending |= UINT64_C(1) << index;
    }
    if (!same(k, u.type, ck_restrict(k, comp.child[0], clause), "The tube is not in the family on its face.") ||
        !same(k, e.term, ck_endpoint_term(k, u.term, dim, 0), "The equality does not start at the tube at 0.") ||
        !same(k, e.other, ck_restrict(k, comp.child[2], clause), "The equality does not end at the base on the face.") ||
        !formula_context(k, phi, &dims) || !merge(k, s.context, u.context, &context) ||
        !merge3(k, context, e.context, dims, &context))
        return 0;
    cc_term tubes = append_tube(k, comp.child[1], face, u.term);
    cc_term extended = tubes ? make(k, CC_COMP, dim, comp.child[0], tubes, comp.child[2], 0) : 0;
    return extended ? system_fact(k, extended, s.type, context, pending) : 0;
}

/* The last tube u and the tube v at a position agree where their faces meet:
 * an equality u ≡ v, both restricted to the overlap. */
cc_judgement_id cc_instr_system_overlap(cc_kernel *k, cc_judgement_id system_id, uint32_t position,
                                        cc_judgement_id agreement_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SYSTEM_OVERLAP, .premise = {system_id, agreement_id},
                                  .operand = {position}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, e = {0};
    uint32_t context = 0;
    if (!premise(k, system_id, CC_FACT_SYSTEM, &s) || !premise(k, agreement_id, CC_FACT_EQUALITY, &e))
        return 0;
    if (!tube_slot(k, s.term))
        return ck_fail(k, "Not a system of tubes."), 0;
    if (position >= 64 || !(s.pending & (UINT64_C(1) << position)))
        return ck_fail(k, "The last tube does not overlap that tube, or already agrees with it."), 0;
    cc_term last = 0, other = 0;
    cc_clause mine = {0}, theirs = {0};
    if (!tube_at(k, s.term, 0, &last, &mine, true) || !tube_at(k, s.term, position, &other, &theirs, false))
        return 0;
    cc_clause overlap = {mine.positive | theirs.positive, mine.negative | theirs.negative};
    if (!same(k, e.term, ck_restrict(k, last, overlap), "The equality does not start at the last tube on the overlap.") ||
        !same(k, e.other, ck_restrict(k, other, overlap), "The equality does not end at the other tube on the overlap.") ||
        !merge(k, s.context, e.context, &context))
        return 0;
    return system_fact(k, s.term, s.type, context, s.pending & ~(UINT64_C(1) << position));
}

cc_judgement_id cc_instr_comp(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_COMP, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    uint32_t context = 0;
    if (!premise(k, system_id, CC_FACT_SYSTEM, &s))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    if (k->nodes[s.term].kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    cc_entry_id dimension = dimension_entry(k, k->nodes[s.term].payload);
    if (!dimension || !discharge(k, s.context, &dimension, 1, &context))
        return 0;
    return typing(k, s.term, s.type, context);
}

/* ---- W types ------------------------------------------------------------- */

cc_judgement_id cc_instr_w(cc_kernel *k, cc_entry_id id, cc_judgement_id arities) {
    return former(k, CC_W, id, arities);
}

/* A W type as written: its typing judgement and its node. */
static bool w_type(cc_kernel *k, cc_term type, cc_node *w) {
    *w = k->nodes[type];
    if (w->kind != CC_W)
        return ck_fail(k, "Expected a W type.");
    return true;
}

cc_judgement_id cc_instr_sup(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id label_id, cc_judgement_id children_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SUP, .premise = {type_id, label_id, children_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, l = {0}, c = {0};
    cc_node w = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, &t) || !premise(k, label_id, CC_FACT_TYPING, &l) ||
        !premise(k, children_id, CC_FACT_TYPING, &c) || !universe(k, t.type, &level) || !w_type(k, t.term, &w))
        return 0;
    cc_term arity = ck_substitute(k, w.child[1], w.payload, l.term);
    cc_term children = make(k, CC_PI, ck_fresh_symbol(k), arity, t.term, 0, 0);
    if (!same(k, l.type, w.child[0], "The label has the wrong type.") ||
        !same(k, c.type, children, "The children have the wrong type.") ||
        !merge(k, t.context, l.context, &context) || !merge(k, context, c.context, &context))
        return 0;
    return typing(k, make(k, CC_SUP, 0, t.term, l.term, c.term, 0), t.term, context);
}

cc_judgement_id cc_instr_w_elim(cc_kernel *k, cc_judgement_id motive_id, cc_judgement_id step_id, cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_W_ELIM, .premise = {motive_id, step_id, value_id}}, NULL, 0, &found))
        return found;
    cc_fact p = {0}, s = {0}, v = {0};
    cc_node w = {0};
    uint32_t context = 0;
    if (!premise(k, motive_id, CC_FACT_TYPING, &p) || !premise(k, step_id, CC_FACT_TYPING, &s) ||
        !premise(k, value_id, CC_FACT_TYPING, &v) || !w_type(k, v.type, &w) || !motive(k, p, v.type))
        return 0;
    /* As the term checker states it (check_inductives.c). */
    uint32_t label_name = ck_fresh_symbol(k), child_name = ck_fresh_symbol(k);
    uint32_t index_name = ck_fresh_symbol(k), hypothesis_name = ck_fresh_symbol(k);
    cc_term label = ck_var(k, label_name), children = ck_var(k, child_name), index = ck_var(k, index_name);
    cc_term arity = ck_substitute(k, w.child[1], w.payload, label);
    cc_term child_type = make(k, CC_PI, index_name, arity, v.type, 0, 0);
    cc_term hypothesis_type = make(k, CC_PI, index_name, arity, app(k, p.term, app(k, children, index)), 0, 0);
    cc_term tree = make(k, CC_SUP, 0, v.type, label, children, 0);
    cc_term step_type = make(k, CC_PI, hypothesis_name, hypothesis_type, app(k, p.term, tree), 0, 0);
    step_type = make(k, CC_PI, child_name, child_type, step_type, 0, 0);
    step_type = make(k, CC_PI, label_name, w.child[0], step_type, 0, 0);
    if (!same(k, s.type, step_type, "The step has the wrong type.") ||
        !merge(k, p.context, s.context, &context) || !merge(k, context, v.context, &context))
        return 0;
    return typing(k, make(k, CC_WREC, 0, p.term, s.term, v.term, 0), app(k, p.term, v.term), context);
}

/* ---- Pushouts ------------------------------------------------------------ */

cc_judgement_id cc_instr_pushout(cc_kernel *k, cc_judgement_id source_id, cc_judgement_id left_id,
                                 cc_judgement_id right_id, cc_judgement_id maps_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PUSHOUT, .premise = {source_id, left_id, right_id, maps_id}},
               NULL, 0, &found))
        return found;
    cc_fact c = {0}, a = {0}, b = {0}, m = {0};
    uint32_t lc = 0, la = 0, lb = 0, context = 0;
    if (!premise(k, source_id, CC_FACT_TYPING, &c) || !premise(k, left_id, CC_FACT_TYPING, &a) ||
        !premise(k, right_id, CC_FACT_TYPING, &b) || !premise(k, maps_id, CC_FACT_TYPING, &m) ||
        !universe(k, c.type, &lc) || !universe(k, a.type, &la) || !universe(k, b.type, &lb))
        return 0;
    uint32_t x = ck_fresh_symbol(k), f = ck_fresh_symbol(k);
    cc_term span = make(k, CC_SIGMA, f, make(k, CC_PI, x, c.term, a.term, 0, 0), make(k, CC_PI, x, c.term, b.term, 0, 0), 0, 0);
    if (!same(k, m.type, span, "The maps of a pushout are a pair C → A, C → B.") ||
        !merge(k, c.context, a.context, &context) || !merge3(k, context, b.context, m.context, &context))
        return 0;
    uint32_t level = lc > la ? lc : la;
    if (lb > level)
        level = lb;
    return typing(k, make(k, CC_PUSHOUT, 0, c.term, a.term, b.term, m.term), make(k, CC_U, level, 0, 0, 0, 0), context);
}

/* A pushout type as written, and the context of its typing judgement. */
static bool pushout_type(cc_kernel *k, cc_judgement_id type_id, cc_fact *t, cc_node *span) {
    uint32_t level = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, t) || !universe(k, t->type, &level))
        return false;
    *span = k->nodes[t->term];
    if (span->kind != CC_PUSHOUT)
        return ck_fail(k, "Expected a pushout type.");
    return true;
}

cc_judgement_id cc_instr_push_point(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id value_id, bool right) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PUSH_POINT, .premise = {type_id, value_id}, .operand = {right}},
               NULL, 0, &found))
        return found;
    cc_fact t = {0}, v = {0};
    cc_node span = {0};
    uint32_t context = 0;
    if (!pushout_type(k, type_id, &t, &span) || !premise(k, value_id, CC_FACT_TYPING, &v) ||
        !same(k, v.type, span.child[right ? 2 : 1], "The point has the wrong type.") ||
        !merge(k, t.context, v.context, &context))
        return 0;
    return typing(k, make(k, right ? CC_PUSH_RIGHT : CC_PUSH_LEFT, 0, t.term, v.term, 0, 0), t.term, context);
}

cc_judgement_id cc_instr_push_path(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id value_id, cc_formula_id interval) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PUSH_PATH, .premise = {type_id, value_id}, .operand = {interval}},
               NULL, 0, &found))
        return found;
    cc_fact t = {0}, v = {0};
    cc_node span = {0};
    uint32_t dims = 0, context = 0;
    const cc_formula *point = cc_kernel_get_formula(k, interval);
    if (!point || point->sort != CC_INTERVAL)
        return ck_fail(k, "A pushout path is at an interval formula."), 0;
    if (!pushout_type(k, type_id, &t, &span) || !premise(k, value_id, CC_FACT_TYPING, &v) ||
        !same(k, v.type, span.child[0], "The path's point has the wrong type.") ||
        !formula_context(k, point, &dims) || !merge3(k, t.context, v.context, dims, &context))
        return 0;
    return typing(k, make(k, CC_PUSH_PATH, interval, t.term, v.term, 0, 0), t.term, context);
}

cc_judgement_id cc_instr_push_elim(cc_kernel *k, cc_judgement_id motive_id, cc_judgement_id left_id,
                                   cc_judgement_id right_id, cc_judgement_id bridge_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_PUSH_ELIM, .premise = {motive_id, left_id, right_id, bridge_id}},
               NULL, 0, &found))
        return found;
    cc_fact p = {0}, l = {0}, r = {0}, b = {0};
    uint32_t context = 0;
    if (!premise(k, motive_id, CC_FACT_TYPING, &p) || !premise(k, left_id, CC_FACT_TYPING, &l) ||
        !premise(k, right_id, CC_FACT_TYPING, &r) || !premise(k, bridge_id, CC_FACT_TYPING, &b))
        return 0;
    cc_node family = k->nodes[p.type];
    if (family.kind != CC_PI || k->nodes[family.child[1]].kind != CC_U || k->nodes[family.child[0]].kind != CC_PUSHOUT)
        return ck_fail(k, "A pushout motive is a family of types over a pushout type."), 0;
    cc_term P = family.child[0];
    cc_node span = k->nodes[P];
    uint32_t a = ck_fresh_symbol(k), bb = ck_fresh_symbol(k), c = ck_fresh_symbol(k), z = ck_fresh_symbol(k);
    cc_term left_type = make(k, CC_PI, a, span.child[1],
                             app(k, p.term, make(k, CC_PUSH_LEFT, 0, P, ck_var(k, a), 0, 0)), 0, 0);
    cc_term right_type = make(k, CC_PI, bb, span.child[2],
                              app(k, p.term, make(k, CC_PUSH_RIGHT, 0, P, ck_var(k, bb), 0, 0)), 0, 0);
    cc_term path = ck_pushout_bridge_type(k, P, p.term, l.term, r.term, ck_var(k, c));
    cc_term bridge_type = path ? make(k, CC_PI, c, span.child[0], path, 0, 0) : 0;
    if (!bridge_type || !same(k, l.type, left_type, "The left case has the wrong type.") ||
        !same(k, r.type, right_type, "The right case has the wrong type.") ||
        !same(k, b.type, bridge_type, "The bridge case has the wrong type.") ||
        !merge(k, p.context, l.context, &context) || !merge3(k, context, r.context, b.context, &context))
        return 0;
    return typing(k, make(k, CC_PUSH_ELIM, 0, p.term, l.term, r.term, b.term),
                  make(k, CC_PI, z, P, app(k, p.term, ck_var(k, z)), 0, 0), context);
}

cc_judgement_id cc_instr_hcomp(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_HCOMP, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    uint32_t context = 0;
    if (!premise(k, system_id, CC_FACT_SYSTEM, &s))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    if (k->nodes[s.term].kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    cc_node comp = k->nodes[s.term];
    if (ck_free_dims(k, comp.child[0]) & (UINT64_C(1) << comp.payload))
        return ck_fail(k, "A homogeneous composition's type may not use its dimension."), 0;
    cc_term head = ck_whnf(k, comp.child[0]);
    if (!head || k->nodes[head].kind != CC_PUSHOUT)
        return k->error[0] ? 0 : (ck_fail(k, "Homogeneous composition is for pushout types."), 0);
    cc_entry_id dimension = dimension_entry(k, comp.payload);
    if (!dimension || !discharge(k, s.context, &dimension, 1, &context))
        return 0;
    return typing(k, make(k, CC_HCOMP, comp.payload, comp.child[0], comp.child[1], comp.child[2], 0), s.type, context);
}

cc_judgement_id cc_instr_trans(cc_kernel *k, cc_judgement_id system_id, cc_formula_id face) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_TRANS, .premise = {system_id}, .operand = {face}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    uint32_t context = 0, dims = 0;
    if (!premise(k, system_id, CC_FACT_SYSTEM, &s))
        return 0;
    if (s.pending)
        return ck_fail(k, "The last tube must first be shown to agree with the tubes it overlaps."), 0;
    if (k->nodes[s.term].kind != CC_COMP)
        return ck_fail(k, "Not a composition system."), 0;
    const cc_formula *phi = cc_kernel_get_formula(k, face);
    if (!phi || phi->sort != CC_FACE)
        return ck_fail(k, "A transport's face is a face formula."), 0;
    cc_node comp = k->nodes[s.term];
    size_t clause = 0;
    for (cc_term cursor = comp.child[1]; cursor; cursor = k->nodes[cursor].child[1], ++clause) {
        const cc_formula *own = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (clause >= phi->length || own->length != 1 || own->clauses[0].positive != phi->clauses[clause].positive ||
            own->clauses[0].negative != phi->clauses[clause].negative)
            return ck_fail(k, "A transport's tubes are its face's clauses, in order."), 0;
        if (!same(k, k->nodes[cursor].child[0], ck_restrict(k, comp.child[2], phi->clauses[clause]),
                  "A transport's tube is its base on the face."))
            return 0;
    }
    if (clause != phi->length)
        return ck_fail(k, "A transport's tubes are its face's clauses, in order."), 0;
    cc_term head = ck_whnf(k, comp.child[0]);
    if (!head || k->nodes[head].kind != CC_PUSHOUT)
        return k->error[0] ? 0 : (ck_fail(k, "Transport is for pushout type families."), 0);
    cc_entry_id dimension = dimension_entry(k, comp.payload);
    if (!dimension || !formula_context(k, phi, &dims) || !discharge(k, s.context, &dimension, 1, &context) ||
        !merge(k, context, dims, &context))
        return 0;
    cc_term tube = make(k, CC_TUBE, face, comp.child[2], 0, 0, 0);
    return typing(k, make(k, CC_TRANS, comp.payload, comp.child[0], tube, comp.child[2], 0), s.type, context);
}

/* ---- Glue ---------------------------------------------------------------- */

cc_term cc_kernel_equiv_type(cc_kernel *k, cc_term a, cc_term b) {
    if (!k || !a || !b || a >= k->count || b >= k->count)
        return 0;
    return ck_equiv_type(k, a, b);
}

cc_judgement_id cc_instr_glue_base(cc_kernel *k, cc_judgement_id base_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_BASE, .premise = {base_id}}, NULL, 0, &found))
        return found;
    cc_fact a = {0};
    uint32_t level = 0;
    if (!premise(k, base_id, CC_FACT_TYPING, &a) || !universe(k, a.type, &level))
        return 0;
    cc_term glue = make(k, CC_GLUE, 0, a.term, 0, 0, 0);
    return glue ? system_fact(k, glue, a.type, a.context, 0) : 0;
}

static cc_term append_piece(cc_kernel *k, cc_term pieces, cc_formula_id face, cc_term type, cc_term equivalence) {
    if (!pieces)
        return make(k, CC_GLUE_SYSTEM, face, type, equivalence, 0, 0);
    cc_node n = k->nodes[pieces];
    cc_term rest = append_piece(k, n.child[2], face, type, equivalence);
    return rest ? make(k, CC_GLUE_SYSTEM, n.payload, n.child[0], n.child[1], rest, 0) : 0;
}

/* A system judgement whose term is of the given kind, with nothing pending. */
static bool open_system(cc_kernel *k, cc_judgement_id id, cc_term_kind kind, cc_fact *s) {
    if (!premise(k, id, CC_FACT_SYSTEM, s))
        return false;
    if (k->nodes[s->term].kind != kind)
        return ck_fail(k, kind == CC_GLUE ? "Not a Glue type under construction." : "Not a Glue term under construction.");
    if (s->pending)
        return ck_fail(k, "The last piece must first be shown to agree with the pieces it overlaps.");
    return true;
}

/* The positions of earlier pieces or tubes, chained through `next`, whose
 * one-clause faces meet a clause. */
static bool overlapping(cc_kernel *k, cc_term cursor, unsigned next, cc_clause clause, uint64_t *out) {
    *out = 0;
    for (uint32_t index = 0; cursor; cursor = k->nodes[cursor].child[next], ++index) {
        const cc_formula *face = cc_kernel_get_formula(k, k->nodes[cursor].payload);
        if (!face->length)
            continue;
        cc_clause other = face->clauses[0];
        if ((clause.positive | other.positive) & (clause.negative | other.negative))
            continue;
        if (index >= 64)
            return ck_fail(k, "A piece may overlap only the first 64 pieces.");
        *out |= UINT64_C(1) << index;
    }
    return true;
}

cc_judgement_id cc_instr_glue_piece(cc_kernel *k, cc_judgement_id system_id, cc_formula_id face,
                                    cc_judgement_id type_id, cc_judgement_id equivalence_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_PIECE, .premise = {system_id, type_id, equivalence_id},
                                  .operand = {face}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, t = {0}, e = {0};
    uint32_t level = 0, own = 0, dims = 0, context = 0;
    if (!open_system(k, system_id, CC_GLUE, &s) || !premise(k, type_id, CC_FACT_TYPING, &t) ||
        !premise(k, equivalence_id, CC_FACT_TYPING, &e) || !universe(k, s.type, &level) || !universe(k, t.type, &own))
        return 0;
    const cc_formula *phi = cc_kernel_get_formula(k, face);
    if (!phi || phi->sort != CC_FACE || phi->length > 1)
        return ck_fail(k, "A Glue piece's face is one conjunction of endpoint equations, or 0."), 0;
    cc_node glue = k->nodes[s.term];
    uint64_t pending = 0;
    if (phi->length) {
        cc_clause clause = phi->clauses[0];
        uint64_t names = clause.positive | clause.negative;
        if (clause.positive & clause.negative)
            return ck_fail(k, "A Glue piece's face must be consistent."), 0;
        if ((ck_free_dims(k, t.term) | ck_free_dims(k, e.term)) & names)
            return ck_fail(k, "A Glue piece must already be restricted to its face."), 0;
        if (!same(k, e.type, ck_equiv_type(k, t.term, ck_restrict(k, glue.child[0], clause)),
                  "The equivalence is not from the piece's type to the base on the face.") ||
            !overlapping(k, glue.child[1], 2, clause, &pending) || !formula_context(k, phi, &dims))
            return 0;
    }
    if (!merge(k, s.context, t.context, &context) || !merge3(k, context, e.context, dims, &context))
        return 0;
    cc_term pieces = append_piece(k, glue.child[1], face, t.term, e.term);
    cc_term extended = pieces ? make(k, CC_GLUE, 0, glue.child[0], pieces, 0, 0) : 0;
    cc_term sort = make(k, CC_U, own > level ? own : level, 0, 0, 0, 0);
    return extended && sort ? system_fact(k, extended, sort, context, pending) : 0;
}

/* The last piece of a Glue type under construction, and the piece at a position. */
static bool piece_at(cc_kernel *k, cc_term glue, uint32_t position, bool last, cc_node *piece, cc_clause *clause) {
    uint32_t index = 0;
    for (cc_term cursor = k->nodes[glue].child[1]; cursor; cursor = k->nodes[cursor].child[2], ++index) {
        if (last ? k->nodes[cursor].child[2] != 0 : index != position)
            continue;
        *piece = k->nodes[cursor];
        const cc_formula *face = cc_kernel_get_formula(k, piece->payload);
        if (!face || face->length != 1)
            return ck_fail(k, "That piece's face is not one clause.");
        *clause = face->clauses[0];
        return true;
    }
    return ck_fail(k, "The Glue type has no piece at that position.");
}

cc_judgement_id cc_instr_glue_overlap(cc_kernel *k, cc_judgement_id system_id, uint32_t position,
                                      cc_judgement_id types_id, cc_judgement_id equivalences_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_OVERLAP, .premise = {system_id, types_id, equivalences_id},
                                  .operand = {position}}, NULL, 0, &found))
        return found;
    cc_fact s = {0}, t = {0}, e = {0};
    uint32_t context = 0;
    if (!premise(k, system_id, CC_FACT_SYSTEM, &s) || !premise(k, types_id, CC_FACT_EQUALITY, &t) ||
        !premise(k, equivalences_id, CC_FACT_EQUALITY, &e))
        return 0;
    if (k->nodes[s.term].kind != CC_GLUE)
        return ck_fail(k, "Not a Glue type under construction."), 0;
    if (position >= 64 || !(s.pending & (UINT64_C(1) << position)))
        return ck_fail(k, "The last piece does not overlap that piece, or already agrees with it."), 0;
    cc_node mine = {0}, theirs = {0};
    cc_clause a = {0}, b = {0};
    if (!piece_at(k, s.term, 0, true, &mine, &a) || !piece_at(k, s.term, position, false, &theirs, &b))
        return 0;
    cc_clause overlap = {a.positive | b.positive, a.negative | b.negative};
    if (!same(k, t.term, ck_restrict(k, mine.child[0], overlap), "The types' equality does not start at the last piece.") ||
        !same(k, t.other, ck_restrict(k, theirs.child[0], overlap), "The types' equality does not end at the other piece.") ||
        !same(k, e.term, ck_restrict(k, mine.child[1], overlap), "The equivalences' equality does not start at the last piece.") ||
        !same(k, e.other, ck_restrict(k, theirs.child[1], overlap), "The equivalences' equality does not end at the other piece.") ||
        !merge3(k, s.context, t.context, e.context, &context))
        return 0;
    return system_fact(k, s.term, s.type, context, s.pending & ~(UINT64_C(1) << position));
}

cc_judgement_id cc_instr_glue(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_GLUE, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    if (!open_system(k, system_id, CC_GLUE, &s))
        return 0;
    return typing(k, s.term, s.type, s.context);
}

cc_judgement_id cc_instr_glue_term_base(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id base_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_TERM_BASE, .premise = {type_id, base_id}}, NULL, 0, &found))
        return found;
    cc_fact g = {0}, a = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, type_id, CC_FACT_TYPING, &g) || !premise(k, base_id, CC_FACT_TYPING, &a) ||
        !universe(k, g.type, &level))
        return 0;
    cc_node glue = k->nodes[g.term];
    if (glue.kind != CC_GLUE)
        return ck_fail(k, "A Glue term needs a Glue type."), 0;
    if (!same(k, a.type, glue.child[0], "The base is not in the Glue type's base.") ||
        !merge(k, g.context, a.context, &context))
        return 0;
    cc_term term = make(k, CC_GLUE_TERM, 0, g.term, a.term, 0, 0);
    return term ? system_fact(k, term, g.term, context, 0) : 0;
}

cc_judgement_id cc_instr_glue_term_piece(cc_kernel *k, cc_judgement_id system_id, cc_judgement_id value_id,
                                         cc_judgement_id image_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_TERM_PIECE, .premise = {system_id, value_id, image_id}},
               NULL, 0, &found))
        return found;
    cc_fact s = {0}, v = {0}, e = {0};
    uint32_t dims = 0, context = 0;
    if (!open_system(k, system_id, CC_GLUE_TERM, &s) || !premise(k, value_id, CC_FACT_TYPING, &v))
        return 0;
    cc_node term = k->nodes[s.term], glue = k->nodes[term.child[0]];
    /* The piece of the type this value is for: the next one, in order. */
    cc_term piece = glue.child[1];
    for (cc_term cursor = term.child[2]; cursor && piece; cursor = k->nodes[cursor].child[1])
        piece = k->nodes[piece].child[2];
    if (!piece)
        return ck_fail(k, "The Glue term has a value for every piece of its type."), 0;
    cc_node part = k->nodes[piece];
    const cc_formula *phi = cc_kernel_get_formula(k, part.payload);
    uint64_t pending = 0;
    if (phi->length) {
        cc_clause clause = phi->clauses[0];
        if (!premise(k, image_id, CC_FACT_EQUALITY, &e))
            return 0;
        if (ck_free_dims(k, v.term) & (clause.positive | clause.negative))
            return ck_fail(k, "A Glue term's value must already be restricted to its face."), 0;
        cc_term image = app(k, make(k, CC_FST, 0, part.child[1], 0, 0, 0), v.term);
        if (!same(k, v.type, part.child[0], "The value is not in the piece's type.") ||
            !same(k, e.term, image, "The equality does not start at the value's image.") ||
            !same(k, e.other, ck_restrict(k, term.child[1], clause), "The equality does not end at the base on the face.") ||
            !overlapping(k, term.child[2], 1, clause, &pending) || !formula_context(k, phi, &dims) ||
            !merge(k, s.context, e.context, &context))
            return 0;
    } else {
        if (image_id)
            return ck_fail(k, "A value on the face 0 takes no equality."), 0;
        context = s.context;
    }
    if (!merge3(k, context, v.context, dims, &context))
        return 0;
    cc_term tubes = append_tube(k, term.child[2], part.payload, v.term);
    cc_term extended = tubes ? make(k, CC_GLUE_TERM, 0, term.child[0], term.child[1], tubes, 0) : 0;
    return extended ? system_fact(k, extended, s.type, context, pending) : 0;
}

cc_judgement_id cc_instr_glue_term(cc_kernel *k, cc_judgement_id system_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_GLUE_TERM, .premise = {system_id}}, NULL, 0, &found))
        return found;
    cc_fact s = {0};
    if (!open_system(k, system_id, CC_GLUE_TERM, &s))
        return 0;
    cc_node term = k->nodes[s.term];
    cc_term piece = k->nodes[term.child[0]].child[1], tube = term.child[2];
    for (; piece && tube; piece = k->nodes[piece].child[2], tube = k->nodes[tube].child[1]) {}
    if (piece || tube)
        return ck_fail(k, "The Glue term has a value for every piece of its type."), 0;
    return typing(k, s.term, s.type, s.context);
}

cc_judgement_id cc_instr_unglue(cc_kernel *k, cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_UNGLUE, .premise = {value_id}}, NULL, 0, &found))
        return found;
    cc_fact v = {0};
    if (!premise(k, value_id, CC_FACT_TYPING, &v))
        return 0;
    cc_node glue = k->nodes[v.type];
    if (glue.kind != CC_GLUE)
        return ck_fail(k, "Only an element of a Glue type is unglued."), 0;
    return typing(k, make(k, CC_UNGLUE, 0, v.type, v.term, 0, 0), glue.child[0], v.context);
}

/* ---- Definitions -------------------------------------------------------- */

cc_judgement_id cc_instr_define(cc_kernel *k, uint32_t symbol, cc_judgement_id closed) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_DEFINE, .premise = {closed}, .operand = {symbol}}, NULL, 0, &found))
        return found;
    cc_fact d = {0};
    if (!premise(k, closed, CC_FACT_TYPING, &d))
        return 0;
    if (d.context)
        return ck_fail(k, "Only a closed judgement can be defined."), 0;
    for (size_t i = 1; i < k->definition_count; ++i)
        if (k->definitions[i].symbol == symbol)
            return ck_fail(k, "Definition symbol is already registered."), 0;
    cc_definition *definitions = reserve(k, k->definitions, &k->definition_capacity, k->definition_count + 1, sizeof *definitions);
    if (!definitions)
        return 0;
    k->definitions = definitions;
    uint32_t index = (uint32_t)k->definition_count;
    cc_term reference = make(k, CC_DEFREF, index, 0, 0, 0, 0);
    if (!reference)
        return 0;
    k->definitions[index] = (cc_definition){symbol, d.term, d.type, true};
    ++k->definition_count;
    return typing(k, reference, d.type, 0);
}

cc_judgement_id cc_instr_lookup(cc_kernel *k, cc_term reference) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_LOOKUP, .operand = {reference}}, NULL, 0, &found))
        return found;
    if (!reference || reference >= k->count || k->nodes[reference].kind != CC_DEFREF ||
        !k->nodes[reference].payload || k->nodes[reference].payload >= k->definition_count)
        return ck_fail(k, "Unknown checked definition reference."), 0;
    /* Only what the instructions admitted: the term checker is not trusted. */
    if (!k->definitions[k->nodes[reference].payload].admitted)
        return ck_fail(k, "Only a definition admitted by Define can be looked up."), 0;
    return typing(k, reference, k->definitions[k->nodes[reference].payload].type, 0);
}

/* ---- Equality ----------------------------------------------------------- */

cc_judgement_id cc_instr_refl(cc_kernel *k, cc_judgement_id typing_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_REFL, .premise = {typing_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0};
    if (!premise(k, typing_id, CC_FACT_TYPING, &t))
        return 0;
    return publish(k, CC_FACT_EQUALITY, t.term, t.term, t.type, t.context);
}

/* Both sides of an equality have its type. */
cc_judgement_id cc_instr_side(cc_kernel *k, cc_judgement_id equality, unsigned side) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SIDE, .premise = {equality}, .operand = {side}}, NULL, 0, &found))
        return found;
    cc_fact e = {0};
    if (!premise(k, equality, CC_FACT_EQUALITY, &e))
        return 0;
    if (side > 1)
        return ck_fail(k, "An equality has sides 0 and 1."), 0;
    return typing(k, side ? e.other : e.term, e.type, e.context);
}

cc_judgement_id cc_instr_symmetry(cc_kernel *k, cc_judgement_id equality) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_SYMMETRY, .premise = {equality}}, NULL, 0, &found))
        return found;
    cc_fact e = {0};
    if (!premise(k, equality, CC_FACT_EQUALITY, &e))
        return 0;
    return publish(k, CC_FACT_EQUALITY, e.other, e.term, e.type, e.context);
}

cc_judgement_id cc_instr_transitivity(cc_kernel *k, cc_judgement_id first, cc_judgement_id second) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_TRANSITIVITY, .premise = {first, second}}, NULL, 0, &found))
        return found;
    cc_fact a = {0}, b = {0};
    uint32_t context = 0;
    if (!premise(k, first, CC_FACT_EQUALITY, &a) || !premise(k, second, CC_FACT_EQUALITY, &b) ||
        !same(k, b.term, a.other, "The equalities do not meet.") ||
        !same(k, b.type, a.type, "The equalities are at different types.") ||
        !merge(k, a.context, b.context, &context))
        return 0;
    return publish(k, CC_FACT_EQUALITY, a.term, b.other, a.type, context);
}

cc_judgement_id cc_instr_convert(cc_kernel *k, cc_judgement_id typing_id, cc_judgement_id equality) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_CONVERT, .premise = {typing_id, equality}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, e = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, typing_id, CC_FACT_TYPING, &t) || !premise(k, equality, CC_FACT_EQUALITY, &e) ||
        !universe(k, e.type, &level) || !same(k, t.type, e.term, "The equality does not start at the judgement's type.") ||
        !merge(k, t.context, e.context, &context))
        return 0;
    return typing(k, t.term, e.other, context);
}

cc_judgement_id cc_instr_lift(cc_kernel *k, cc_judgement_id typing_id, cc_judgement_id type_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_LIFT, .premise = {typing_id, type_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, b = {0};
    uint32_t level = 0, context = 0;
    if (!premise(k, typing_id, CC_FACT_TYPING, &t) || !premise(k, type_id, CC_FACT_TYPING, &b) ||
        !universe(k, b.type, &level))
        return 0;
    if (!ck_syntactic_cumulative(k, t.type, b.term)) {
        if (k->error[0])
            return 0;
        k->mismatch_found = t.type;
        k->mismatch_expected = b.term;
        return ck_fail_as(k, CC_ERROR_MISMATCH, "The type is not included in the target type."), 0;
    }
    if (!merge(k, t.context, b.context, &context))
        return 0;
    return typing(k, t.term, b.term, context);
}

cc_judgement_id cc_instr_eta(cc_kernel *k, cc_judgement_id typing_id) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_ETA, .premise = {typing_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0};
    if (!premise(k, typing_id, CC_FACT_TYPING, &t))
        return 0;
    cc_node type = k->nodes[t.type];
    cc_term expanded = 0;
    if (type.kind == CC_PI) {
        uint32_t name = ck_fresh_symbol(k);
        expanded = make(k, CC_LAM, name, type.child[0], app(k, t.term, ck_var(k, name)), 0, 0);
    } else if (type.kind == CC_SIGMA) {
        expanded = make(k, CC_PAIR, 0, t.type, make(k, CC_FST, 0, t.term, 0, 0, 0), make(k, CC_SND, 0, t.term, 0, 0, 0), 0);
    } else if (type.kind == CC_PATH) {
        unsigned fresh = ck_fresh_dimension(k, ck_free_dims(k, t.term) | ck_free_dims(k, t.type));
        if (fresh >= CC_DIMENSIONS)
            return 0;
        cc_formula point;
        cc_init(&point, CC_INTERVAL);
        cc_formula_id argument = cc_generator(&point, fresh, true) == CC_OK ? cc_kernel_formula(k, &point) : 0;
        cc_term family = argument ? ck_dimension_substitute(k, type.child[0], type.payload, &point) : 0;
        cc_clear(&point);
        if (!family)
            return ck_fail(k, "Interval allocation failed."), 0;
        expanded = make(k, CC_PLAM, fresh, family, make(k, CC_PAPP, argument, t.term, t.type, 0, 0), 0, 0);
    } else {
        return ck_fail(k, "Eta needs a term of a Π, Σ or path type."), 0;
    }
    return publish(k, CC_FACT_EQUALITY, t.term, expanded, t.type, t.context);
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
    return make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], n.child[3]);
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
        return ck_fail(k, "Beta needs a lambda applied to an argument."), 0;
    case CC_STEP_DELTA:
        if (n.kind == CC_DEFREF && n.payload && n.payload < k->definition_count)
            return k->definitions[n.payload].value;
        return ck_fail(k, "Delta needs a definition."), 0;
    case CC_STEP_IOTA: {
        cc_node head;
        switch (n.kind) {
        case CC_NATREC:
            head = k->nodes[n.child[3]];
            if (head.kind == CC_ZERO)
                return n.child[1];
            if (head.kind == CC_SUCC)
                return app(k, app(k, n.child[2], head.child[0]), make(k, CC_NATREC, 0, n.child[0], n.child[1], n.child[2], head.child[0]));
            break;
        case CC_SUMREC:
            head = k->nodes[n.child[3]];
            if (head.kind == CC_INL || head.kind == CC_INR)
                return app(k, n.child[head.kind == CC_INL ? 1 : 2], head.child[1]);
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
        case CC_WREC:
            /* WRec(M, s, sup(l, c)) is s(l)(c)(λi. WRec(M, s, c(i))); the
             * arity is read off the W type's weak head, which involves no
             * choice. */
            head = k->nodes[n.child[2]];
            if (head.kind == CC_SUP) {
                cc_term type = ck_whnf(k, head.child[0]);
                if (!type || k->nodes[type].kind != CC_W)
                    return ck_fail(k, "Malformed W constructor."), 0;
                cc_node w = k->nodes[type];
                uint32_t name = ck_fresh_symbol(k);
                cc_term arity = ck_substitute(k, w.child[1], w.payload, head.child[1]);
                cc_term recursive = make(k, CC_WREC, 0, n.child[0], n.child[1], app(k, head.child[2], ck_var(k, name)), 0);
                cc_term hypothesis = make(k, CC_LAM, name, arity, recursive, 0, 0);
                return app(k, app(k, app(k, n.child[1], head.child[1]), head.child[2]), hypothesis);
            }
            break;
        case CC_PUSH_PATH: {
            /* push at 0 is inl(f(c)), at 1 inr(g(c)); the maps are read off
             * the pushout type's weak head, which involves no choice. */
            cc_term reduct = ck_pushout_reduce(k, term);
            if (reduct && reduct != term)
                return reduct;
            if (k->error[0])
                return 0;
            break;
        }
        case CC_APP: {
            /* The pushout eliminator on a point or on a path. */
            cc_node eliminator = k->nodes[n.child[0]];
            head = k->nodes[n.child[1]];
            if (eliminator.kind != CC_PUSH_ELIM)
                break;
            if (head.kind == CC_PUSH_LEFT || head.kind == CC_PUSH_RIGHT)
                return app(k, eliminator.child[head.kind == CC_PUSH_LEFT ? 1 : 2], head.child[1]);
            if (head.kind == CC_PUSH_PATH) {
                cc_term path = ck_pushout_bridge_type(k, head.child[0], eliminator.child[0], eliminator.child[1],
                                                      eliminator.child[2], head.child[1]);
                return path ? make(k, CC_PAPP, head.payload, app(k, eliminator.child[3], head.child[1]), path, 0, 0) : 0;
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
    if (side > 2 || (side == 1 && out->kind != CC_FACT_EQUALITY))
        return ck_fail(k, "A judgement has sides 0 (term), 2 (type), and 1 for an equality's other term.");
    *root = side == 0 ? out->term : side == 1 ? out->other : out->type;
    return true;
}

static cc_judgement_id republish(cc_kernel *k, cc_fact f, unsigned side, cc_term changed, uint32_t context) {
    if (side == 0) f.term = changed;
    else if (side == 1) f.other = changed;
    else f.type = changed;
    return publish(k, f.kind, f.term, f.other, f.type, context);
}

cc_judgement_id cc_instr_step(cc_kernel *k, cc_judgement_id id, unsigned side,
                              const uint8_t *position, size_t depth, cc_step_rule rule) {
    cc_judgement_id found;
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_STEP, .premise = {id}, .operand = {side, rule}}, position, depth, &found))
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
    if (!begin(k, (cc_derivation){.rule = CC_INSTR_REPLACE, .premise = {id, by}, .operand = {side}}, position, depth, &found))
        return found;
    cc_fact e = {0}, inner = {0};
    cc_term root = 0;
    if (!judgement(k, id, side, &e, &root) || !premise(k, by, CC_FACT_EQUALITY, &inner))
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
    if (!target || !same(k, target, inner.term, "The highlighted subterm is not the equality's left side."))
        goto done;
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
            if (!same(k, k->entries[id].type, crossed[at].node.child[0], "The entry and the binder have different types."))
                goto done;
            terms[count++] = (scoped_term){k->entries[id].type, at};
        }
        removed[discharged++] = id;
    }
    uint32_t context = 0;
    cc_term changed = rebuild(k, root, position, depth, inner.other);
    if (!changed || !discharge(k, inner.context, removed, discharged, &context) || !merge(k, e.context, context, &context))
        goto done;
    result = republish(k, e, side, changed, context);
done:
    free(crossed);
    free(terms);
    free(removed);
    return result;
}

/* ---- Reading the store -------------------------------------------------- */

size_t cc_kernel_judgement_count(const cc_kernel *k) {
    return k && k->fact_count ? k->fact_count : 1;
}

bool cc_kernel_judgement(const cc_kernel *k, cc_judgement_id id, cc_judgement_info *info) {
    if (!k || !info || !id || id >= k->fact_count)
        return false;
    cc_fact f = k->facts[id];
    *info = (cc_judgement_info){f.kind, f.term, f.other, f.type, (cc_instruction)f.how.rule,
        {f.how.premise[0], f.how.premise[1], f.how.premise[2], f.how.premise[3]}, f.how.entry,
        {f.how.operand[0], f.how.operand[1]}, f.how.depth ? k->positions + f.how.position : NULL, f.how.depth};
    return true;
}

cc_entry_id cc_kernel_judgement_context(const cc_kernel *k, cc_judgement_id id, size_t index) {
    if (!k || !id || id >= k->fact_count)
        return 0;
    cc_context_set s = k->context_sets[k->facts[id].context];
    return index < s.count ? k->context_items[s.offset + index] : 0;
}

size_t cc_kernel_entry_count(const cc_kernel *k) {
    return k && k->entry_count ? k->entry_count : 1;
}

bool cc_kernel_entry(const cc_kernel *k, cc_entry_id id, uint32_t *symbol, cc_term *type, bool *dimension,
                     cc_judgement_id *source) {
    if (!k || !id || id >= k->entry_count)
        return false;
    cc_entry e = k->entries[id];
    if (symbol) *symbol = e.symbol;
    if (type) *type = e.type;
    if (dimension) *dimension = e.dimension;
    if (source) *source = e.source;
    return true;
}
