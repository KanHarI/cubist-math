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

/* Each instruction is one operation with its own budget, counted as kernel
 * work (cc_kernel_work). An instruction does nothing, and counts nothing,
 * while an earlier error is recorded. */
static bool ready(cc_kernel *k) {
    if (!k || k->error[0])
        return false;
    ck_operation(k, CC_WORK_INSTRUCTION);
    k->recursion = 0;
    /* The deadline bounds instructions as it bounds checking. */
    if (!ck_tick(k))
        return false;
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
    /* A derivation of depth 0 has no positions, and the array may still be
     * null: an offset from it is undefined, and the hash reads none. */
    size_t slot = derivation_hash(&fact->how, fact->how.depth ? k->positions + fact->how.position : NULL) & mask;
    while (k->derivations[slot] && k->derivations[slot] < k->fact_count)
        slot = (slot + 1) & mask;
    if (!k->derivations[slot])
        ++k->derivation_used;
    k->derivations[slot] = id;
}

/* Start an instruction. It proceeds only when it is new: the judgement of
 * an identical earlier instruction is returned instead, as is 0 on error. */
bool ck_instr_begin(cc_kernel *k, cc_derivation how, const uint8_t *position, size_t depth, cc_judgement_id *found) {
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

bool ck_instr_premise(cc_kernel *k, cc_judgement_id id, uint32_t kind, cc_fact *out) {
    if (!id || id >= k->fact_count)
        return ck_fail(k, "Unknown judgement.");
    if (k->facts[id].kind != kind)
        return ck_fail(k, kind == CC_FACT_TYPING ? "Expected a typing judgement." : "Expected an equality judgement.");
    *out = k->facts[id];
    return true;
}

bool ck_instr_entry(cc_kernel *k, cc_entry_id id, bool dimension, cc_entry *out) {
    if (!id || id >= k->entry_count)
        return ck_fail(k, "Unknown context entry.");
    if (k->entries[id].face)
        return ck_fail(k, "A face entry is an assumption, not a variable or a dimension.");
    if (k->entries[id].dimension != dimension)
        return ck_fail(k, dimension ? "Expected a dimension entry." : "Expected a term entry.");
    if (k->entries[id].level_variable)
        return ck_fail(k, "A universe variable is not a term: use it in a level, as U(x).");
    *out = k->entries[id];
    return true;
}

cc_judgement_id ck_instr_publish(cc_kernel *k, uint32_t kind, cc_term term, cc_term other, cc_term type, uint32_t context) {
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

cc_judgement_id ck_instr_typing(cc_kernel *k, cc_term term, cc_term type, uint32_t context) {
    return ck_instr_publish(k, CC_FACT_TYPING, term, 0, type, context);
}

/* A mismatch keeps the two terms for diagnostics, as conversion does. */
bool ck_instr_same(cc_kernel *k, cc_term found, cc_term expected, const char *message) {
    if (ck_alpha_equal(k, found, expected))
        return true;
    if (k->error[0])
        return false;
    k->mismatch_found = found;
    k->mismatch_expected = expected;
    return ck_fail_as(k, CC_ERROR_MISMATCH, message);
}

/* A type's universe, and its level: the universe's level child. */
bool ck_instr_universe(cc_kernel *k, cc_term type, cc_term *level) {
    if (!type || k->nodes[type].kind != CC_U)
        return ck_fail(k, "Expected a type: a term of a universe.");
    *level = k->nodes[type].child[0];
    return true;
}

cc_term ck_instr_make(cc_kernel *k, cc_term_kind kind, uint32_t payload, cc_term a, cc_term b, cc_term c, cc_term d) {
    return ck_make(k, kind, payload, a, b, c, d);
}

cc_term ck_instr_app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_instr_make(k, CC_APP, 0, f, x, 0, 0);
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
bool ck_instr_merge(cc_kernel *k, uint32_t a, uint32_t b, uint32_t *out) {
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

bool ck_instr_merge3(cc_kernel *k, uint32_t a, uint32_t b, uint32_t c, uint32_t *out) {
    uint32_t ab;
    return ck_instr_merge(k, a, b, &ab) && ck_instr_merge(k, ab, c, out);
}

/* Remove entries from a context. A remaining entry must not depend on a
 * removed one, and must not be another dimension entry with a removed
 * dimension's index: the binder would capture it. */
bool ck_instr_discharge(cc_kernel *k, uint32_t set, const cc_entry_id *removed, size_t count, uint32_t *out) {
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
bool ck_instr_bind(cc_kernel *k, uint32_t body, cc_entry_id e, uint32_t *out) {
    uint32_t rest;
    return ck_instr_discharge(k, body, &e, 1, &rest) && ck_instr_merge(k, rest, k->entries[e].context, out);
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
            if (!k->entries[old].dimension && !k->entries[old].face) index_entry(k, old);
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
    cc_term level = 0;
    if (!ready(k) || !ck_instr_premise(k, type, CC_FACT_TYPING, &t) || !ck_instr_universe(k, t.type, &level))
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
    k->entries[id] = (cc_entry){.symbol = symbol, .type = t.term, .level = level, .context = t.context, .source = type};
    if (!publish_set(k, 1, &scope) || !ck_instr_merge(k, t.context, scope, &scope))
        return 0;
    k->entries[id].scope = scope;
    ++k->entry_count;
    index_entry(k, id);
    return id;
}

/* A level entry x < ω (G0 §2.2). Its type is the bound, LBound(1): binder
 * syntax, never a term, so the entry needs no judgement. Level and term
 * entries share the symbols: the same symbol again gives the same level
 * entry, and a term entry's symbol is refused. */
cc_entry_id cc_instr_level(cc_kernel *k, uint32_t symbol) {
    if (!ready(k))
        return 0;
    if (!symbol)
        return ck_fail(k, "A context entry needs a symbol."), 0;
    cc_entry_id named = find_entry(k, symbol);
    if (named) {
        if (k->entries[named].level_variable)
            return named;
        return ck_fail(k, "The symbol already names a context entry."), 0;
    }
    cc_term bound = ck_instr_make(k, CC_LBOUND, 1, 0, 0, 0, 0);
    if (!bound || !ck_var(k, symbol))
        return 0;
    cc_entry *entries = reserve(k, k->entries, &k->entry_capacity, k->entry_count + 1, sizeof *entries);
    if (!entries)
        return 0;
    k->entries = entries;
    cc_entry_id id = (cc_entry_id)k->entry_count;
    uint32_t *self = scratch(k, 1), scope = 0;
    if (!self)
        return 0;
    *self = id;
    k->entries[id] = (cc_entry){.symbol = symbol, .type = bound, .level_variable = true};
    if (!publish_set(k, 1, &scope))
        return 0;
    k->entries[id].scope = scope;
    ++k->entry_count;
    index_entry(k, id);
    return id;
}

static bool level_entry(cc_kernel *k, cc_entry_id id, cc_entry *out) {
    if (!id || id >= k->entry_count)
        return ck_fail(k, "Unknown context entry.");
    if (!k->entries[id].level_variable)
        return ck_fail(k, "Expected a level entry.");
    *out = k->entries[id];
    return true;
}

cc_entry_id ck_instr_dimension_entry(cc_kernel *k, unsigned index);

cc_entry_id cc_instr_dimension(cc_kernel *k, unsigned index) {
    if (!ready(k))
        return 0;
    return ck_instr_dimension_entry(k, index);
}

cc_entry_id ck_instr_dimension_entry(cc_kernel *k, unsigned index) {
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
    k->entries[id] = (cc_entry){.symbol = index, .dimension = true};
    if (!publish_set(k, 1, &scope))
        return 0;
    k->entries[id].scope = scope;
    ++k->entry_count;
    k->dimension_entries[index] = id;
    return id;
}

/* The face entry of a consistent clause with at least one equation: one
 * entry per clause. Its context is the clause's dimension entries. */
cc_entry_id ck_instr_face_entry(cc_kernel *k, cc_clause clause) {
    for (cc_entry_id id = 1; id < k->entry_count; ++id)
        if (k->entries[id].face && k->entries[id].clause.positive == clause.positive &&
            k->entries[id].clause.negative == clause.negative)
            return id;
    uint64_t names = clause.positive | clause.negative;
    uint32_t context = 0;
    for (unsigned dim = 0; dim < CC_DIMENSIONS; ++dim) {
        if (!(names >> dim & 1))
            continue;
        cc_entry_id entry = ck_instr_dimension_entry(k, dim);
        if (!entry || !ck_instr_merge(k, context, k->entries[entry].scope, &context))
            return 0;
    }
    cc_entry *entries = reserve(k, k->entries, &k->entry_capacity, k->entry_count + 1, sizeof *entries);
    if (!entries)
        return 0;
    k->entries = entries;
    cc_entry_id id = (cc_entry_id)k->entry_count;
    uint32_t *self = scratch(k, 1), scope = 0;
    if (!self)
        return 0;
    *self = id;
    k->entries[id] = (cc_entry){.context = context, .face = true, .clause = clause};
    if (!publish_set(k, 1, &scope) || !ck_instr_merge(k, context, scope, &scope))
        return 0;
    k->entries[id].scope = scope;
    ++k->entry_count;
    return id;
}

/* A premise of a partial element on a clause: its context without the face
 * entries the clause implies, each a conjunction of some of its equations.
 * On the clause they hold, so the premise holds there (Γ, φ ⊢ J). A face
 * entry the clause does not imply stays. One that a remaining entry depends
 * on, a variable whose type holds only on that face, is refused, as any
 * discharge is. */
bool ck_instr_on_face(cc_kernel *k, uint32_t set, cc_clause clause, uint32_t *out) {
    *out = set;
    for (bool again = true; again && !k->error[0];) {
        again = false;
        cc_context_set s = k->context_sets[*out];
        for (uint32_t i = 0; i < s.count; ++i) {
            cc_entry_id id = k->context_items[s.offset + i];
            cc_entry e = k->entries[id];
            if (!e.face || e.clause.positive & ~clause.positive || e.clause.negative & ~clause.negative)
                continue;
            if (!ck_instr_discharge(k, *out, &id, 1, out))
                return false;
            again = true;
            break;
        }
    }
    return !k->error[0];
}

cc_judgement_id cc_instr_variable(cc_kernel *k, cc_entry_id id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_VARIABLE, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    if (!ck_instr_entry(k, id, false, &e))
        return 0;
    return ck_instr_typing(k, ck_var(k, e.symbol), e.type, e.scope);
}

/* ---- Universes and inductive types -------------------------------------- */

/* The context of a level (G0 §2.3): the level entries of its variables. */
static bool level_context(cc_kernel *k, const cc_level_nf *nf, uint32_t *context) {
    *context = 0;
    for (uint32_t i = 0; i < nf->count; ++i) {
        cc_entry_id id = nf->terms[i].key <= UINT32_MAX ? find_entry(k, (uint32_t)nf->terms[i].key) : 0;
        if (!id)
            return ck_fail(k, "Unbound level variable.");
        if (!k->entries[id].level_variable)
            return ck_fail(k, "A term variable is not a level.");
        if (!ck_instr_merge(k, *context, k->entries[id].scope, context))
            return false;
    }
    return true;
}

/* U-Form (G0 §2.5): a well-formed level whose successor is within the bound.
 * The level is taken in normal form, so universes at equal levels are one
 * term; its variables' entries are the context. */
cc_judgement_id cc_instr_universe(cc_kernel *k, cc_term level) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_UNIVERSE, .operand = {level}}, NULL, 0, &found))
        return found;
    cc_level_nf nf;
    if (!ck_level_normal(k, level, &nf))
        return 0;
    cc_term canonical = 0, next = 0;
    uint32_t context = 0;
    bool bound = level_context(k, &nf, &context);
    if (bound && nf.constant >= CC_LEVEL_MAX)
        ck_fail(k, "A universe level exceeds the kernel's bound.");
    else if (bound) {
        canonical = ck_level_build(k, &nf);
        if (!ck_level_nf_succ(k, &nf))
            canonical = 0;
        next = canonical ? ck_level_build(k, &nf) : 0;
    }
    ck_level_nf_free(&nf);
    if (!canonical || !next)
        return 0;
    return ck_instr_typing(k, ck_universe(k, canonical), ck_universe(k, next), context);
}

static cc_judgement_id constant(cc_kernel *k, cc_instruction rule, cc_term_kind kind, cc_term_kind type) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = rule}, NULL, 0, &found))
        return found;
    cc_term sort = type == CC_U ? ck_universe_at(k, 0) : ck_instr_make(k, type, 0, 0, 0, 0, 0);
    return ck_instr_typing(k, ck_instr_make(k, kind, 0, 0, 0, 0, 0), sort, 0);
}

cc_judgement_id cc_instr_unit(cc_kernel *k) { return constant(k, CC_INSTR_UNIT, CC_UNIT, CC_U); }
cc_judgement_id cc_instr_void(cc_kernel *k) { return constant(k, CC_INSTR_VOID, CC_VOID, CC_U); }

cc_judgement_id cc_instr_point(cc_kernel *k) { return constant(k, CC_INSTR_POINT, CC_POINT, CC_UNIT); }

/* A motive over the type domain: P : Π(x : domain). U(l). */
static bool motive(cc_kernel *k, cc_fact p, cc_term domain) {
    cc_node pi = k->nodes[p.type];
    if (pi.kind != CC_PI || k->nodes[pi.child[1]].kind != CC_U)
        return ck_fail(k, "A motive is a family of types: Π(x : A). U(l).");
    return ck_instr_same(k, pi.child[0], domain, "The motive is a family over another type.");
}

cc_judgement_id cc_instr_unit_elim(cc_kernel *k, cc_judgement_id motive_id, cc_judgement_id point_id,
                                   cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_UNIT_ELIM, .premise = {motive_id, point_id, value_id}}, NULL, 0, &found))
        return found;
    cc_fact p = {0}, b = {0}, u = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, motive_id, CC_FACT_TYPING, &p) || !ck_instr_premise(k, point_id, CC_FACT_TYPING, &b) ||
        !ck_instr_premise(k, value_id, CC_FACT_TYPING, &u))
        return 0;
    cc_term unit = ck_instr_make(k, CC_UNIT, 0, 0, 0, 0, 0);
    if (!motive(k, p, unit) || !ck_instr_same(k, u.type, unit, "Unit induction needs a unit value.") ||
        !ck_instr_same(k, b.type, ck_instr_app(k, p.term, ck_instr_make(k, CC_POINT, 0, 0, 0, 0, 0)), "The point case has the wrong type.") ||
        !ck_instr_merge3(k, p.context, b.context, u.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_UNITREC, 0, p.term, b.term, u.term, 0), ck_instr_app(k, p.term, u.term), context);
}

cc_judgement_id cc_instr_abort(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id impossible_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_ABORT, .premise = {type_id, impossible_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, e = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, type_id, CC_FACT_TYPING, &t) || !ck_instr_premise(k, impossible_id, CC_FACT_TYPING, &e) ||
        !ck_instr_universe(k, t.type, &level) ||
        !ck_instr_same(k, e.type, ck_instr_make(k, CC_VOID, 0, 0, 0, 0, 0), "abort needs an element of the empty type.") ||
        !ck_instr_merge(k, t.context, e.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_ABORT, 0, t.term, e.term, 0, 0), t.term, context);
}

cc_judgement_id cc_instr_sum(cc_kernel *k, cc_judgement_id left_id, cc_judgement_id right_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SUM, .premise = {left_id, right_id}}, NULL, 0, &found))
        return found;
    cc_fact a = {0}, b = {0};
    cc_term left = 0, right = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, left_id, CC_FACT_TYPING, &a) || !ck_instr_premise(k, right_id, CC_FACT_TYPING, &b) ||
        !ck_instr_universe(k, a.type, &left) || !ck_instr_universe(k, b.type, &right) || !ck_instr_merge(k, a.context, b.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_SUM, 0, a.term, b.term, 0, 0), ck_universe(k, ck_level_max(k, left, right)), context);
}

cc_judgement_id cc_instr_inject(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id value_id, bool right) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_INJECT, .premise = {type_id, value_id}, .operand = {right}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, v = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, type_id, CC_FACT_TYPING, &t) || !ck_instr_premise(k, value_id, CC_FACT_TYPING, &v) ||
        !ck_instr_universe(k, t.type, &level))
        return 0;
    cc_node sum = k->nodes[t.term];
    if (sum.kind != CC_SUM)
        return ck_fail(k, "An injection needs a sum type."), 0;
    if (!ck_instr_same(k, v.type, sum.child[right ? 1 : 0], "The injected value has the wrong type.") ||
        !ck_instr_merge(k, t.context, v.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, right ? CC_INR : CC_INL, 0, t.term, v.term, 0, 0), t.term, context);
}

cc_judgement_id cc_instr_sum_elim(cc_kernel *k, cc_judgement_id motive_id, cc_judgement_id left_id,
                                  cc_judgement_id right_id, cc_judgement_id value_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_SUM_ELIM, .premise = {motive_id, left_id, right_id, value_id}}, NULL, 0, &found))
        return found;
    cc_fact p = {0}, cases[2] = {0}, v = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, motive_id, CC_FACT_TYPING, &p) || !ck_instr_premise(k, left_id, CC_FACT_TYPING, &cases[0]) ||
        !ck_instr_premise(k, right_id, CC_FACT_TYPING, &cases[1]) || !ck_instr_premise(k, value_id, CC_FACT_TYPING, &v))
        return 0;
    cc_node sum = k->nodes[v.type];
    if (sum.kind != CC_SUM)
        return ck_fail(k, "Sum induction needs a value of a sum type."), 0;
    if (!motive(k, p, v.type))
        return 0;
    for (unsigned side = 0; side < 2; ++side) {
        uint32_t name = ck_fresh_symbol(k);
        cc_term injected = ck_instr_make(k, side ? CC_INR : CC_INL, 0, v.type, ck_var(k, name), 0, 0);
        if (!ck_instr_same(k, cases[side].type, ck_instr_make(k, CC_PI, name, sum.child[side], ck_instr_app(k, p.term, injected), 0, 0),
                  side ? "The right case has the wrong type." : "The left case has the wrong type."))
            return 0;
    }
    if (!ck_instr_merge(k, p.context, cases[0].context, &context) || !ck_instr_merge3(k, context, cases[1].context, v.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_SUMREC, 0, p.term, cases[0].term, cases[1].term, v.term), ck_instr_app(k, p.term, v.term), context);
}

/* ---- Functions and pairs ------------------------------------------------ */

static cc_judgement_id former(cc_kernel *k, cc_term_kind kind, cc_entry_id id, cc_judgement_id family) {
    cc_judgement_id found;
    unsigned rule = kind == CC_PI ? CC_INSTR_PI : CC_INSTR_SIGMA;
    if (!ck_instr_begin(k, (cc_derivation){.rule = rule, .premise = {family}, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    cc_fact b = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_entry(k, id, false, &e) || !ck_instr_premise(k, family, CC_FACT_TYPING, &b) ||
        !ck_instr_universe(k, b.type, &level) || !ck_instr_bind(k, b.context, id, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, kind, e.symbol, e.type, b.term, 0, 0),
                  ck_universe(k, ck_level_max(k, e.level, level)), context);
}

cc_judgement_id cc_instr_pi(cc_kernel *k, cc_entry_id id, cc_judgement_id codomain) {
    return former(k, CC_PI, id, codomain);
}

cc_judgement_id cc_instr_sigma(cc_kernel *k, cc_entry_id id, cc_judgement_id family) {
    return former(k, CC_SIGMA, id, family);
}

cc_judgement_id cc_instr_lambda(cc_kernel *k, cc_entry_id id, cc_judgement_id body_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_LAMBDA, .premise = {body_id}, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    cc_fact b = {0};
    uint32_t context = 0;
    if (!ck_instr_entry(k, id, false, &e) || !ck_instr_premise(k, body_id, CC_FACT_TYPING, &b) ||
        !ck_instr_bind(k, b.context, id, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_LAM, e.symbol, e.type, b.term, 0, 0), ck_instr_make(k, CC_PI, e.symbol, e.type, b.type, 0, 0), context);
}

cc_judgement_id cc_instr_apply(cc_kernel *k, cc_judgement_id function, cc_judgement_id argument) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_APPLY, .premise = {function, argument}}, NULL, 0, &found))
        return found;
    cc_fact f = {0}, a = {0};
    uint32_t context = 0;
    if (!ck_instr_premise(k, function, CC_FACT_TYPING, &f) || !ck_instr_premise(k, argument, CC_FACT_TYPING, &a))
        return 0;
    cc_node pi = k->nodes[f.type];
    if (pi.kind != CC_PI)
        return ck_fail(k, "Only a term of a Π type can be applied."), 0;
    if (!ck_instr_same(k, a.type, pi.child[0], "The argument has the wrong type.") || !ck_instr_merge(k, f.context, a.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_app(k, f.term, a.term), ck_substitute(k, pi.child[1], pi.payload, a.term), context);
}

/* ---- Level quantification (G0 §2.7) ------------------------------------ */

/* ∀-Form: the statement lives at lim_x of its body's level, ω when x occurs
 * in the body's level and that level otherwise. */
cc_judgement_id cc_instr_level_pi(cc_kernel *k, cc_entry_id id, cc_judgement_id body_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_LEVEL_PI, .premise = {body_id}, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    cc_fact b = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!level_entry(k, id, &e) || !ck_instr_premise(k, body_id, CC_FACT_TYPING, &b) || !ck_instr_universe(k, b.type, &level) ||
        !ck_instr_bind(k, b.context, id, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_LPI, e.symbol, e.type, b.term, 0, 0),
                  ck_universe(k, ck_level_limit(k, e.symbol, level)), context);
}

/* ∀-Intro. */
cc_judgement_id cc_instr_level_lambda(cc_kernel *k, cc_entry_id id, cc_judgement_id body_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_LEVEL_LAMBDA, .premise = {body_id}, .entry = id}, NULL, 0, &found))
        return found;
    cc_entry e = {0};
    cc_fact b = {0};
    uint32_t context = 0;
    if (!level_entry(k, id, &e) || !ck_instr_premise(k, body_id, CC_FACT_TYPING, &b) || !ck_instr_bind(k, b.context, id, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_LLAM, e.symbol, e.type, b.term, 0, 0),
                  ck_instr_make(k, CC_LPI, e.symbol, e.type, b.type, 0, 0), context);
}

/* ∀-Elim: only at a finite level, since the variable ranges over the levels
 * below ω (§3.3 shows why ω itself would be unsound). The instance's levels
 * are taken to normal form, and must stay within the bounds. */
cc_judgement_id cc_instr_level_apply(cc_kernel *k, cc_judgement_id function, cc_term level) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_LEVEL_APPLY, .premise = {function}, .operand = {level}}, NULL, 0, &found))
        return found;
    cc_fact f = {0};
    if (!ck_instr_premise(k, function, CC_FACT_TYPING, &f))
        return 0;
    cc_node pi = k->nodes[f.type];
    if (pi.kind != CC_LPI)
        return ck_fail(k, "Only a term of a level Π can be instantiated at a level."), 0;
    cc_level_nf nf;
    if (!ck_level_normal(k, level, &nf))
        return 0;
    cc_term canonical = 0;
    uint32_t levels = 0, context = 0;
    if (nf.tier)
        ck_fail(k, "Instantiation needs a finite level, below ω.");
    else if (level_context(k, &nf, &levels))
        canonical = ck_level_build(k, &nf);
    ck_level_nf_free(&nf);
    if (!canonical || !ck_instr_merge(k, f.context, levels, &context))
        return 0;
    cc_term type = ck_level_instantiate(k, pi.child[1], pi.payload, canonical);
    return type ? ck_instr_typing(k, ck_instr_make(k, CC_LAPP, 0, f.term, canonical, 0, 0), type, context) : 0;
}

cc_judgement_id cc_instr_pair(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id first_id, cc_judgement_id second_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_PAIR, .premise = {type_id, first_id, second_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, a = {0}, b = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, type_id, CC_FACT_TYPING, &t) || !ck_instr_premise(k, first_id, CC_FACT_TYPING, &a) ||
        !ck_instr_premise(k, second_id, CC_FACT_TYPING, &b) || !ck_instr_universe(k, t.type, &level))
        return 0;
    cc_node sigma = k->nodes[t.term];
    if (sigma.kind != CC_SIGMA)
        return ck_fail(k, "A pair needs a Σ type."), 0;
    if (!ck_instr_same(k, a.type, sigma.child[0], "The first component has the wrong type.") ||
        !ck_instr_same(k, b.type, ck_substitute(k, sigma.child[1], sigma.payload, a.term), "The second component has the wrong type.") ||
        !ck_instr_merge3(k, t.context, a.context, b.context, &context))
        return 0;
    return ck_instr_typing(k, ck_instr_make(k, CC_PAIR, 0, t.term, a.term, b.term, 0), t.term, context);
}

static cc_judgement_id projection(cc_kernel *k, cc_judgement_id pair, bool second) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = second ? CC_INSTR_SECOND : CC_INSTR_FIRST, .premise = {pair}}, NULL, 0, &found))
        return found;
    cc_fact p = {0};
    if (!ck_instr_premise(k, pair, CC_FACT_TYPING, &p))
        return 0;
    cc_node sigma = k->nodes[p.type];
    if (sigma.kind != CC_SIGMA)
        return ck_fail(k, "Only a term of a Σ type has projections."), 0;
    cc_term first = ck_instr_make(k, CC_FST, 0, p.term, 0, 0, 0);
    if (!second)
        return ck_instr_typing(k, first, sigma.child[0], p.context);
    return ck_instr_typing(k, ck_instr_make(k, CC_SND, 0, p.term, 0, 0, 0), ck_substitute(k, sigma.child[1], sigma.payload, first), p.context);
}

cc_judgement_id cc_instr_first(cc_kernel *k, cc_judgement_id pair) { return projection(k, pair, false); }
cc_judgement_id cc_instr_second(cc_kernel *k, cc_judgement_id pair) { return projection(k, pair, true); }

/* The parts of a type former are types in its universe, by cumulativity:
 * the domain of Π(x : A). B or Σ(x : A). B, and its family
 * B[a/x] at a : A. */
cc_judgement_id cc_instr_domain(cc_kernel *k, cc_judgement_id type_id) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_DOMAIN, .premise = {type_id}}, NULL, 0, &found))
        return found;
    cc_fact t = {0};
    cc_term level = 0;
    if (!ck_instr_premise(k, type_id, CC_FACT_TYPING, &t) || !ck_instr_universe(k, t.type, &level))
        return 0;
    cc_node former = k->nodes[t.term];
    if (former.kind != CC_PI && former.kind != CC_SIGMA)
        return ck_fail(k, "Only a Π or Σ type has a domain."), 0;
    return ck_instr_typing(k, former.child[0], t.type, t.context);
}

cc_judgement_id cc_instr_family(cc_kernel *k, cc_judgement_id type_id, cc_judgement_id argument) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_FAMILY, .premise = {type_id, argument}}, NULL, 0, &found))
        return found;
    cc_fact t = {0}, a = {0};
    cc_term level = 0;
    uint32_t context = 0;
    if (!ck_instr_premise(k, type_id, CC_FACT_TYPING, &t) || !ck_instr_premise(k, argument, CC_FACT_TYPING, &a) ||
        !ck_instr_universe(k, t.type, &level))
        return 0;
    cc_node former = k->nodes[t.term];
    if (former.kind != CC_PI && former.kind != CC_SIGMA)
        return ck_fail(k, "Only a Π or Σ type has a family."), 0;
    if (!ck_instr_same(k, a.type, former.child[0], "The argument has the wrong type.") || !ck_instr_merge(k, t.context, a.context, &context))
        return 0;
    return ck_instr_typing(k, ck_substitute(k, former.child[1], former.payload, a.term), t.type, context);
}

/* ---- Definitions -------------------------------------------------------- */

cc_judgement_id cc_instr_define(cc_kernel *k, uint32_t symbol, cc_judgement_id closed) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_DEFINE, .premise = {closed}, .operand = {symbol}}, NULL, 0, &found))
        return found;
    cc_fact d = {0};
    if (!ck_instr_premise(k, closed, CC_FACT_TYPING, &d))
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
    cc_term reference = ck_instr_make(k, CC_DEFREF, index, 0, 0, 0, 0);
    if (!reference)
        return 0;
    k->definitions[index] = (cc_definition){symbol, d.term, d.type};
    ++k->definition_count;
    return ck_instr_typing(k, reference, d.type, 0);
}

cc_judgement_id cc_instr_lookup(cc_kernel *k, cc_term reference) {
    cc_judgement_id found;
    if (!ck_instr_begin(k, (cc_derivation){.rule = CC_INSTR_LOOKUP, .operand = {reference}}, NULL, 0, &found))
        return found;
    if (!reference || reference >= k->count || k->nodes[reference].kind != CC_DEFREF ||
        !k->nodes[reference].payload || k->nodes[reference].payload >= k->definition_count)
        return ck_fail(k, "Unknown checked definition reference."), 0;
    return ck_instr_typing(k, reference, k->definitions[k->nodes[reference].payload].type, 0);
}

/* ---- Reading the store -------------------------------------------------- */

size_t cc_kernel_judgement_count(const cc_kernel *k) {
    return k && k->fact_count ? k->fact_count : 1;
}

/* The machinery above, for instruction families in their own files. */
bool ck_instr_ready(cc_kernel *k) { return ready(k); }
bool ck_instr_begin_stateful(cc_kernel *k, cc_derivation how) {
    if (!ready(k))
        return false;
    k->pending = how;
    k->pending_position = NULL;
    return true;
}
/* A level in normal form, and its context: the level entries of its
 * variables. The finite form refuses tier 1 and above, as LevelApply does. */
bool ck_instr_finite_level(cc_kernel *k, cc_term level, cc_term *canonical, uint32_t *context) {
    return ck_instr_level(k, level, true, canonical, context);
}
bool ck_instr_level(cc_kernel *k, cc_term level, bool finite, cc_term *canonical, uint32_t *context) {
    cc_level_nf nf;
    if (!ck_level_normal(k, level, &nf))
        return false;
    *canonical = 0;
    if (finite && nf.tier)
        ck_fail(k, "A declared type's instance reads finite levels only, below ω (Q16).");
    else if (nf.constant >= CC_LEVEL_MAX)
        ck_fail(k, "A universe level exceeds the kernel's bound.");
    else if (level_context(k, &nf, context))
        *canonical = ck_level_build(k, &nf);
    ck_level_nf_free(&nf);
    return *canonical != 0;
}

bool cc_kernel_judgement(const cc_kernel *k, cc_judgement_id id, cc_judgement_info *info) {
    if (!k || !info || !id || id >= k->fact_count)
        return false;
    cc_fact f = k->facts[id];
    /* Judgements in progress keep state in other, which only their own
     * instructions read: it is shown for an equality only. */
    cc_term other = f.kind == CC_FACT_EQUALITY ? f.other : 0;
    *info = (cc_judgement_info){f.kind, f.term, other, f.type, (cc_instruction)f.how.rule,
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

bool cc_kernel_entry_face(const cc_kernel *k, cc_entry_id id, cc_clause *clause) {
    if (!k || !id || id >= k->entry_count || !k->entries[id].face)
        return false;
    if (clause) *clause = k->entries[id].clause;
    return true;
}
