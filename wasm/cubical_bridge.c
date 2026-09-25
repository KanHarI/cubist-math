/* Browser boundary for the independent cubical checker.
 * Syntax handles are not proofs. Only cb_check returns a checked judgement;
 * normalization is a separate, explicit inspection operation. */
#include "cubical_kernel.h"
#include <stdlib.h>
#include <string.h>

typedef struct {
    cc_kernel *kernel;
    uint32_t token;
    cc_assumption *context;
    size_t count, capacity;
    cc_term *unfolding;
    size_t unfolding_count, unfolding_capacity;
    cc_formula formula;
    bool formula_open;
    const char *error;
    cc_checked_result checked;
} browser_session;

static browser_session sessions[8];
static uint32_t next_token = 1;

static browser_session *lookup(uint32_t token) {
    for (unsigned i = 0; i < 8; ++i)
        if (sessions[i].kernel && sessions[i].token == token) return &sessions[i];
    return NULL;
}

uint32_t cb_new(void) {
    if (!next_token) return 0;
    for (unsigned i = 0; i < 8; ++i) {
        if (sessions[i].kernel) continue;
        cc_kernel *kernel = cc_kernel_new();
        if (!kernel) return 0;
        sessions[i] = (browser_session){.kernel = kernel, .token = next_token++};
        cc_init(&sessions[i].formula, CC_INTERVAL);
        return sessions[i].token;
    }
    return 0;
}

void cb_free(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s) return;
    cc_kernel_free(s->kernel);
    cc_clear(&s->formula);
    free(s->context);
    free(s->unfolding);
    *s = (browser_session){0};
}

const char *cb_error(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s) return "Invalid cubical session.";
    return s->error ? s->error : cc_kernel_error(s->kernel);
}

/* The class of cb_error's error: a cc_error_kind. */
unsigned cb_error_kind(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s || s->error) return CC_ERROR_OTHER;
    return cc_kernel_error_kind(s->kernel);
}

/* For a mismatch error, side 0 is the type found and side 1 the type
 * expected; otherwise 0. */
uint32_t cb_mismatch(uint32_t token, unsigned side) {
    browser_session *s = lookup(token);
    cc_term found, expected;
    if (!s || s->error || side > 1 || !cc_kernel_mismatch(s->kernel, &found, &expected)) return 0;
    return side ? expected : found;
}

void cb_optimizations(uint32_t token, unsigned flags) {
    browser_session *s = lookup(token);
    if (s) cc_kernel_set_optimizations(s->kernel, flags);
}

void cb_checkpoint(uint32_t token) {
    browser_session *s = lookup(token);
    if (s) cc_kernel_checkpoint(s->kernel);
}
void cb_rollback(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s) return;
    cc_kernel_rollback(s->kernel);
    s->count = 0; s->unfolding_count = 0; s->error = NULL;
    memset(&s->checked, 0, sizeof s->checked);
}

int cb_commit_checkpoint(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    s->count = 0; memset(&s->checked, 0, sizeof s->checked);
    if (!cc_kernel_commit_checkpoint(s->kernel)) return 0;
    for (size_t i = 0; i < s->unfolding_count; ++i)
        s->unfolding[i] = cc_kernel_relocated(s->kernel, s->unfolding[i]);
    return 1;
}
cc_term cb_relocated(uint32_t token, cc_term term) {
    browser_session *s = lookup(token);
    return s ? cc_kernel_relocated(s->kernel, term) : 0;
}

void cb_deadline_ms(uint32_t token, double duration_ms) {
    browser_session *s = lookup(token);
    if (s) cc_kernel_set_deadline_ms(s->kernel, duration_ms);
}

void cb_step_budget(uint32_t token, uint32_t low, uint32_t high) {
    browser_session *s = lookup(token);
    if (s) cc_kernel_set_step_budget(s->kernel, ((uint64_t)high << 32) | low);
}

/* Strategy hints contain only references already checked in this session.
 * They choose reduction order; every requested conversion is still checked. */
int cb_unfolding_clear(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    cc_kernel_clear_error(s->kernel); s->error = NULL;
    if (!cc_kernel_set_unfolding_hints(s->kernel, NULL, 0)) return 0;
    s->unfolding_count = 0;
    return 1;
}

int cb_unfolding_add(uint32_t token, cc_term reference) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    cc_kernel_clear_error(s->kernel); s->error = NULL;
    if (s->unfolding_count == s->unfolding_capacity) {
        size_t capacity = s->unfolding_capacity ? s->unfolding_capacity * 2 : 8;
        if (capacity < s->unfolding_capacity || capacity > SIZE_MAX / sizeof(cc_term)) {
            s->error = "Conversion hint capacity overflow."; return 0;
        }
        cc_term *grown = realloc(s->unfolding, capacity * sizeof(cc_term));
        if (!grown) { s->error = "Conversion hint allocation failed."; return 0; }
        s->unfolding = grown; s->unfolding_capacity = capacity;
    }
    s->unfolding[s->unfolding_count] = reference;
    if (!cc_kernel_set_unfolding_hints(s->kernel, s->unfolding, s->unfolding_count + 1)) return 0;
    ++s->unfolding_count;
    return 1;
}

uint32_t cb_term(uint32_t token, unsigned kind, uint32_t payload,
                 uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    cc_kernel_clear_error(s->kernel);
    s->error = NULL;
    return cc_kernel_term(s->kernel, (cc_term_kind)kind, payload, a, b, c, d);
}

/* A formula is a disjunction of clauses. Four 32-bit words carry the two
 * 64-bit masks without passing lossy JavaScript numbers or raw pointers. */
int cb_formula_begin(uint32_t token, unsigned sort) {
    browser_session *s = lookup(token);
    if (!s || sort > CC_FACE) return 0;
    cc_clear(&s->formula);
    cc_init(&s->formula, (cc_sort)sort);
    s->formula_open = true;
    s->error = NULL;
    return 1;
}

int cb_formula_clause(uint32_t token, uint32_t pl, uint32_t ph, uint32_t nl, uint32_t nh) {
    browser_session *s = lookup(token);
    if (!s || !s->formula_open) return 0;
    cc_clause clause = {((uint64_t)ph << 32) | pl, ((uint64_t)nh << 32) | nl};
    cc_formula input = {s->formula.sort, &clause, 1, 1};
    cc_status status = cc_join(&s->formula, &s->formula, &input);
    if (status != CC_OK) {
        s->error = status == CC_LIMIT_EXCEEDED
            ? "Cubical lattice term-size or work budget exceeded."
            : "Could not allocate cubical formula.";
        s->formula_open = false;
        return 0;
    }
    return 1;
}

uint32_t cb_formula_end(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s || !s->formula_open) return 0;
    s->formula_open = false;
    cc_kernel_clear_error(s->kernel);
    return cc_kernel_formula(s->kernel, &s->formula);
}

void cb_context_clear(uint32_t token) {
    browser_session *s = lookup(token);
    if (s) s->count = 0;
}

int cb_context_add(uint32_t token, uint32_t symbol, uint32_t type) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    if (s->count == s->capacity) {
        size_t capacity = s->capacity ? s->capacity * 2 : 16;
        if (capacity < s->capacity || capacity > SIZE_MAX / sizeof(cc_assumption)) return 0;
        cc_assumption *context = realloc(s->context, capacity * sizeof(*context));
        if (!context) { s->error = "Could not allocate cubical context."; return 0; }
        s->context = context;
        s->capacity = capacity;
    }
    s->context[s->count++] = (cc_assumption){symbol, type};
    return 1;
}

int cb_check_in_cube(uint32_t token, uint32_t term, uint32_t expected,
                     uint32_t dimensions_low, uint32_t dimensions_high) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    s->error = NULL;
    s->checked = (cc_checked_result){0};
    uint64_t dimensions = ((uint64_t)dimensions_high << 32) | dimensions_low;
    return cc_kernel_check_in_cube(s->kernel, term, expected, s->context,
                                   s->count, dimensions, &s->checked);
}

int cb_check(uint32_t token, uint32_t term, uint32_t expected) {
    return cb_check_in_cube(token, term, expected, 0, 0);
}

uint32_t cb_define(uint32_t token, uint32_t symbol, uint32_t value, uint32_t expected) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    s->error = NULL;
    cc_kernel_clear_error(s->kernel);
    s->checked = (cc_checked_result){0};
    return cc_kernel_define(s->kernel, symbol, value, expected);
}

uint32_t cb_definition(uint32_t token, uint32_t reference, unsigned field) {
    browser_session *s = lookup(token);
    uint32_t symbol;
    cc_term value, type;
    if (!s || !cc_kernel_definition(s->kernel, reference, &symbol, &value, &type)) return 0;
    return field == 0 ? symbol : field == 1 ? value : field == 2 ? type : 0;
}

uint32_t cb_head(uint32_t token, uint32_t term) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    s->error = NULL;
    cc_kernel_clear_error(s->kernel);
    return cc_kernel_whnf(s->kernel, term);
}

double cb_result(uint32_t token, unsigned field) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    switch (field) {
    case 0: return s->checked.expression;
    case 1: return s->checked.type;
    case 2: return s->checked.normal;
    case 3: return (double)s->checked.checking_steps;
    case 4: return (double)s->checked.reduction_steps;
    case 5: return (double)s->checked.arena_nodes;
    case 6: return (double)s->checked.arena_bytes;
    default: return 0;
    }
}

uint32_t cb_normalize(uint32_t token, uint32_t term) {
    browser_session *s = lookup(token);
    if (!s || !term || (term != s->checked.expression && term != s->checked.type && term != s->checked.normal)) return 0;
    cc_kernel_clear_error(s->kernel);
    return cc_kernel_normalize(s->kernel, term);
}

uint32_t cb_node(uint32_t token, uint32_t term, unsigned field) {
    browser_session *s = lookup(token);
    cc_term_kind kind;
    uint32_t payload, children[4];
    if (!s || !cc_kernel_node(s->kernel, term, &kind, &payload, children)) return 0;
    if (field == 0) return (uint32_t)kind;
    if (field == 1) return payload;
    return field < 6 ? children[field - 2] : 0;
}

uint32_t cb_formula_view(uint32_t token, uint32_t id, unsigned clause, unsigned field) {
    browser_session *s = lookup(token);
    const cc_formula *f = s ? cc_kernel_get_formula(s->kernel, id) : NULL;
    if (!f) return 0;
    if (field == 0) return (uint32_t)f->length;
    if (field == 1) return (uint32_t)f->sort;
    if (clause >= f->length) return 0;
    uint64_t bits = field < 4 ? f->clauses[clause].positive : f->clauses[clause].negative;
    return (field == 3 || field == 5) ? (uint32_t)(bits >> 32) : (uint32_t)bits;
}
