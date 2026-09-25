/* The arena stores inert syntax and checked normal-form caches separately.
 * Handle zero denotes absence/failure, never a type or term. */
#include "term_internal.h"

/* The first error of an operation is kept, with its class. */
bool ck_fail_as(cc_kernel *k, cc_error_kind kind, const char *message) {
    if (!k->error[0]) {
        strncpy(k->error, message, sizeof k->error - 1);
        k->error[sizeof k->error - 1] = '\0';
        k->error_kind = kind;
    }
    return false;
}

bool ck_fail(cc_kernel *k, const char *message) {
    return ck_fail_as(k, CC_ERROR_OTHER, message);
}

bool ck_tick(cc_kernel *k, bool checking) {
    if (k->error[0])
        return false;
    if (k->deadline_ms && (!k->deadline_ticks--)) {
        k->deadline_ticks = 1023;
        if (!ck_deadline(k)) return false;
    }
    if (!k->budget)
        return ck_fail_as(k, CC_ERROR_BUDGET, "Kernel checking/reduction budget exhausted.");
    --k->budget;
    if (checking)
        ++k->checking_steps;
    else
        ++k->reduction_steps;
    return true;
}

unsigned ck_arity(cc_term_kind kind) {
    switch (kind) {
    case CC_DEFREF: case CC_U: case CC_VAR: case CC_NAT: case CC_ZERO: case CC_UNIT: case CC_POINT: case CC_VOID:
        return 0;
    case CC_SUCC: case CC_FST: case CC_SND:
        return 1;
    case CC_PI: case CC_LAM: case CC_APP: case CC_SIGMA: case CC_PLAM: case CC_PAPP:
    case CC_TUBE: case CC_ABORT: case CC_W: case CC_SUM: case CC_INL: case CC_INR:
    case CC_GLUE: case CC_UNGLUE: case CC_PUSH_LEFT: case CC_PUSH_RIGHT: case CC_PUSH_PATH:
        return 2;
    case CC_PAIR: case CC_PATH: case CC_COMP: case CC_SUP: case CC_WREC: case CC_UNITREC:
    case CC_GLUE_SYSTEM: case CC_GLUE_TERM: case CC_HCOMP: case CC_TRANS:
        return 3;
    case CC_NATREC: case CC_SUMREC: case CC_PUSHOUT: case CC_PUSH_ELIM:
        return 4;
    }
    return 5;
}

cc_kernel *cc_kernel_new(void) {
    cc_kernel *k = calloc(1, sizeof *k);
    if (k) {
        k->optimizations = CC_SHARE_SYNTAX | CC_REUSE_CHECKS;
        k->count = 1;
        k->formula_count = 1;
        k->definition_count = 1;
        k->next_symbol = 1;
        k->budget = k->operation_budget = UINT64_C(10000000);
    }
    return k;
}

void cc_kernel_set_optimizations(cc_kernel *k, unsigned flags) {
    if (!k) return;
    k->optimizations = flags & (CC_SHARE_SYNTAX | CC_REUSE_CHECKS);
    if (!(flags & CC_SHARE_SYNTAX)) { free(k->interned); k->interned = NULL; }
    if (!(flags & CC_REUSE_CHECKS)) ck_clear_check_cache(k);
}

void cc_kernel_set_step_budget(cc_kernel *k, uint64_t steps) {
    if (k && steps) k->operation_budget = steps;
}

void cc_kernel_free(cc_kernel *k) {
    if (!k)
        return;
    for (size_t i = 1; i < k->formula_count; ++i)
        cc_clear(&k->formulas[i]);
    free(k->relocation);
    free(k->definitions);
    free(k->unfolding_hints);
    free(k->formulas);
    free(k->syntax_memo);
    free(k->alpha_memo);
    free(k->alpha_scopes);
    free(k->weak_cache);
    free(k->interned);
    free(k->contexts);
    free(k->inferred);
    free(k->nodes);
    free(k);
}

const char *cc_kernel_error(const cc_kernel *k) {
    return k ? k->error : "Kernel allocation failed.";
}

cc_error_kind cc_kernel_error_kind(const cc_kernel *k) {
    if (!k) return CC_ERROR_OTHER;
    return k->error[0] ? k->error_kind : CC_ERROR_NONE;
}

bool cc_kernel_mismatch(const cc_kernel *k, cc_term *found, cc_term *expected) {
    if (!k || !found || !expected || !k->error[0] || k->error_kind != CC_ERROR_MISMATCH)
        return false;
    *found = k->mismatch_found;
    *expected = k->mismatch_expected;
    return true;
}

cc_term ck_make(cc_kernel *k, cc_term_kind kind, uint32_t payload,
                cc_term a, cc_term b, cc_term c, cc_term d) {
    if (!k || k->error[0])
        return 0;
    unsigned arity = ck_arity(kind);
    cc_term children[] = {a, b, c, d};
    if (arity > 4)
        return ck_fail(k, "Unknown term constructor."), 0;
    for (unsigned i = 0; i < 4; ++i) {
        bool optional = (kind == CC_PAPP && i == 1) ||
                        (kind == CC_TUBE && i == 1) ||
                        ((kind == CC_COMP || kind == CC_HCOMP) && i == 1) || (kind == CC_GLUE && i == 1) ||
                        (kind == CC_GLUE_SYSTEM && i == 2) || (kind == CC_GLUE_TERM && i == 2);
        if (i < arity && !children[i] && !optional)
            return ck_fail(k, "Missing syntax child."), 0;
        if (children[i] >= k->count || (i >= arity && children[i]))
            return ck_fail(k, "Invalid syntax child handle."), 0;
    }
    /* Intern only identical syntax. Every child and payload is compared after
     * hashing, so collisions affect performance, never term identity. */
    if ((k->optimizations & CC_SHARE_SYNTAX) && !k->interned) k->interned = calloc(CC_INTERN_SIZE, sizeof *k->interned);
    uint32_t hash = (uint32_t)kind;
    hash = (hash ^ payload) * UINT32_C(16777619);
    for (unsigned i = 0; i < 4; ++i) hash = (hash ^ children[i]) * UINT32_C(16777619);
    size_t slot = hash % CC_INTERN_SIZE;
    if (k->interned && k->interned[slot]) {
        cc_term existing = k->interned[slot];
        cc_node node = k->nodes[existing];
        if (node.kind == kind && node.payload == payload &&
            !memcmp(node.child, children, sizeof children)) return existing;
    }
    unsigned depth = 1;
    for (unsigned i = 0; i < arity; ++i)
        if (children[i] && k->nodes[children[i]].depth >= depth)
            depth = k->nodes[children[i]].depth + 1;
    if (depth > 512)
        return ck_fail(k, "Native prototype syntax depth exceeds 512."), 0;
    if (k->count >= UINT32_MAX)
        return ck_fail(k, "Term handle space exhausted."), 0;
    if (k->count >= k->capacity) {
        size_t capacity = k->capacity ? 2 * k->capacity : 256;
        if (capacity < k->capacity || capacity > SIZE_MAX / sizeof(cc_node))
            return ck_fail(k, "Term arena capacity overflow."), 0;
        cc_node *nodes = realloc(k->nodes, capacity * sizeof *nodes);
        if (!nodes)
            return ck_fail(k, "Term arena allocation failed."), 0;
        k->nodes = nodes;
        cc_term *cache = realloc(k->weak_cache, capacity * sizeof *cache);
        if (!cache)
            return ck_fail(k, "Normal cache allocation failed."), 0;
        memset(cache + k->capacity, 0, (capacity - k->capacity) * sizeof *cache);
        k->weak_cache = cache;
        k->capacity = capacity;
    }
    cc_term result = (cc_term)k->count++;
    k->nodes[result] = (cc_node){kind, payload, {a,b,c,d}, depth};
    if ((kind == CC_VAR || ck_term_binder(kind)) && payload >= k->next_symbol) {
        if (payload == UINT32_MAX)
            return ck_fail(k, "Term symbol space exhausted."), 0;
        k->next_symbol = payload + 1;
    }
    if (k->interned) k->interned[slot] = result;
    return result;
}

cc_term cc_kernel_term(cc_kernel *k, cc_term_kind kind, uint32_t payload,
                       cc_term a, cc_term b, cc_term c, cc_term d) {
    return ck_make(k, kind, payload, a, b, c, d);
}

cc_formula_id cc_kernel_formula(cc_kernel *k, const cc_formula *f) {
    if (!k || !f || !cc_valid_sort(f->sort) || k->error[0])
        return 0;
    for (size_t i = 1; i < k->formula_count; ++i)
        if (cc_equal(&k->formulas[i], f))
            return (cc_formula_id)i;
    if (k->formula_count >= UINT32_MAX)
        return ck_fail(k, "Formula handle space exhausted."), 0;
    if (k->formula_count == k->formula_capacity || !k->formula_capacity) {
        size_t capacity = k->formula_capacity ? 2 * k->formula_capacity : 64;
        if (capacity < k->formula_capacity || capacity > SIZE_MAX / sizeof(cc_formula))
            return ck_fail(k, "Formula arena capacity overflow."), 0;
        cc_formula *formulas = realloc(k->formulas, capacity * sizeof *formulas);
        if (!formulas)
            return ck_fail(k, "Formula arena allocation failed."), 0;
        k->formulas = formulas;
        k->formula_capacity = capacity;
    }
    cc_formula_id result = (cc_formula_id)k->formula_count;
    cc_init(&k->formulas[result], f->sort);
    if (cc_copy(&k->formulas[result], f) != CC_OK)
        return ck_fail(k, "Formula copy failed."), 0;
    ++k->formula_count;
    return result;
}

const cc_formula *cc_kernel_get_formula(const cc_kernel *k, cc_formula_id id) {
    return k && id && id < k->formula_count ? &k->formulas[id] : NULL;
}

bool cc_kernel_node(const cc_kernel *k, cc_term id, cc_term_kind *kind,
                     uint32_t *payload, cc_term children[4]) {
    if (!k || !id || id >= k->count)
        return false;
    if (kind) *kind = k->nodes[id].kind;
    if (payload) *payload = k->nodes[id].payload;
    if (children) memcpy(children, k->nodes[id].child, sizeof k->nodes[id].child);
    return true;
}

cc_term ck_var(cc_kernel *k, uint32_t name) {
    return ck_make(k, CC_VAR, name, 0, 0, 0, 0);
}

uint32_t ck_fresh_symbol(cc_kernel *k) {
    if (k->next_symbol == UINT32_MAX) {
        ck_fail(k, "Fresh symbol space exhausted.");
        return 0;
    }
    return k->next_symbol++;
}

void cc_kernel_clear_error(cc_kernel *k) {
    if (k)
        k->error[0] = '\0';
}
