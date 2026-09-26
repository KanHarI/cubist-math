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
    uint8_t position[1024]; /* the highlighted position of the next step or replacement */
    size_t depth;
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

/* The checker's trace (cubical_kernel.h), for inspection: a capacity starts
 * it and zero stops it. An event's fields are 0 kind, 1 depth, 2 a, 3 b, 4 c. */
bool cb_trace(uint32_t token, uint32_t capacity) {
    browser_session *s = lookup(token);
    if (!s) return false;
    if (!capacity) { cc_kernel_trace_stop(s->kernel); return true; }
    return cc_kernel_trace_start(s->kernel, capacity);
}

uint32_t cb_trace_count(uint32_t token) {
    browser_session *s = lookup(token);
    size_t count = s ? cc_kernel_trace_count(s->kernel) : 0;
    return count > UINT32_MAX ? UINT32_MAX : (uint32_t)count;
}

uint32_t cb_trace_event(uint32_t token, uint32_t index, unsigned field) {
    browser_session *s = lookup(token);
    cc_trace_event event;
    if (!s || field > 4 || !cc_kernel_trace_event(s->kernel, index, &event)) return 0;
    const uint32_t fields[] = { event.kind, event.depth, event.a, event.b, event.c };
    return fields[field];
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

/* A term the page derived by instructions, and so knows to be well typed:
 * the page keeps that list; the kernel only computes. */
uint32_t cb_normalize_derived(uint32_t token, uint32_t term) {
    browser_session *s = lookup(token);
    if (!s || !term) return 0;
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

/* Instructions (kernel/include/cubical_kernel.h). cb_instr applies one by
 * its cc_instruction code, or extends the context (CB_EXTEND: a = type
 * judgement, b = symbol; CB_DIMENSION: a = index). A step or replacement
 * reads the position pushed since the last cb_position_clear. An
 * instruction's error stays recorded until cb_clear_error. */
enum { CB_EXTEND = 100, CB_DIMENSION = 101 };

void cb_position_clear(uint32_t token) {
    browser_session *s = lookup(token);
    if (s) s->depth = 0;
}

int cb_position_push(uint32_t token, uint32_t child) {
    browser_session *s = lookup(token);
    if (!s || child > 3 || s->depth >= sizeof s->position) return 0;
    s->position[s->depth++] = (uint8_t)child;
    return 1;
}

void cb_clear_error(uint32_t token) {
    browser_session *s = lookup(token);
    if (!s) return;
    s->error = NULL;
    cc_kernel_clear_error(s->kernel);
}

uint32_t cb_instr(uint32_t token, unsigned op, uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    cc_kernel *k = s->kernel;
    switch (op) {
    case CC_INSTR_UNIVERSE: return cc_instr_universe(k, a);
    case CC_INSTR_NAT: return cc_instr_nat(k);
    case CC_INSTR_ZERO: return cc_instr_zero(k);
    case CC_INSTR_SUCC: return cc_instr_succ(k, a);
    case CC_INSTR_NAT_ELIM: return cc_instr_nat_elim(k, a, b, c, d);
    case CC_INSTR_UNIT: return cc_instr_unit(k);
    case CC_INSTR_POINT: return cc_instr_point(k);
    case CC_INSTR_UNIT_ELIM: return cc_instr_unit_elim(k, a, b, c);
    case CC_INSTR_VOID: return cc_instr_void(k);
    case CC_INSTR_ABORT: return cc_instr_abort(k, a, b);
    case CC_INSTR_SUM: return cc_instr_sum(k, a, b);
    case CC_INSTR_INJECT: return cc_instr_inject(k, a, b, c != 0);
    case CC_INSTR_SUM_ELIM: return cc_instr_sum_elim(k, a, b, c, d);
    case CC_INSTR_VARIABLE: return cc_instr_variable(k, a);
    case CC_INSTR_PI: return cc_instr_pi(k, a, b);
    case CC_INSTR_LAMBDA: return cc_instr_lambda(k, a, b);
    case CC_INSTR_APPLY: return cc_instr_apply(k, a, b);
    case CC_INSTR_SIGMA: return cc_instr_sigma(k, a, b);
    case CC_INSTR_PAIR: return cc_instr_pair(k, a, b, c);
    case CC_INSTR_FIRST: return cc_instr_first(k, a);
    case CC_INSTR_SECOND: return cc_instr_second(k, a);
    case CC_INSTR_DOMAIN: return cc_instr_domain(k, a);
    case CC_INSTR_FAMILY: return cc_instr_family(k, a, b);
    case CC_INSTR_PATH: return cc_instr_path(k, a, b, c, d);
    case CC_INSTR_PATH_LAMBDA: return cc_instr_path_lambda(k, a, b);
    case CC_INSTR_PATH_APPLY: return cc_instr_path_apply(k, a, b, c);
    case CC_INSTR_DEFINE: return cc_instr_define(k, a, b);
    case CC_INSTR_LOOKUP: return cc_instr_lookup(k, a);
    case CC_INSTR_REFL: return cc_instr_refl(k, a);
    case CC_INSTR_STEP: return cc_instr_step(k, a, b, s->position, s->depth, (cc_step_rule)c);
    case CC_INSTR_REPLACE: return cc_instr_replace(k, a, b, s->position, s->depth, c);
    case CC_INSTR_ETA: return cc_instr_eta(k, a);
    case CC_INSTR_SIDE: return cc_instr_side(k, a, b);
    case CC_INSTR_SYMMETRY: return cc_instr_symmetry(k, a);
    case CC_INSTR_TRANSITIVITY: return cc_instr_transitivity(k, a, b);
    case CC_INSTR_CONVERT: return cc_instr_convert(k, a, b);
    case CC_INSTR_LIFT: return cc_instr_lift(k, a, b);
    case CC_INSTR_ENDPOINT: return cc_instr_endpoint(k, a, b, c);
    case CC_INSTR_PATH_AT: return cc_instr_path_at(k, a, b);
    case CC_INSTR_SYSTEM: return cc_instr_system(k, a, b, c);
    case CC_INSTR_SYSTEM_TUBE: return cc_instr_system_tube(k, a, b, c, d);
    case CC_INSTR_COMP: return cc_instr_comp(k, a);
    case CC_INSTR_SYSTEM_OVERLAP: return cc_instr_system_overlap(k, a, b, c);
    case CC_INSTR_PUSHOUT: return cc_instr_pushout(k, a, b, c, d);
    case CC_INSTR_PUSH_POINT: return cc_instr_push_point(k, a, b, c != 0);
    case CC_INSTR_PUSH_PATH: return cc_instr_push_path(k, a, b, c);
    case CC_INSTR_PUSH_ELIM: return cc_instr_push_elim(k, a, b, c, d);
    case CC_INSTR_W: return cc_instr_w(k, a, b);
    case CC_INSTR_SUP: return cc_instr_sup(k, a, b, c);
    case CC_INSTR_W_ELIM: return cc_instr_w_elim(k, a, b, c);
    case CC_INSTR_HCOMP: return cc_instr_hcomp(k, a);
    case CC_INSTR_TRANS: return cc_instr_trans(k, a, b);
    case CC_INSTR_GLUE_BASE: return cc_instr_glue_base(k, a);
    case CC_INSTR_GLUE_PIECE: return cc_instr_glue_piece(k, a, b, c, d);
    case CC_INSTR_GLUE_OVERLAP: return cc_instr_glue_overlap(k, a, b, c, d);
    case CC_INSTR_GLUE: return cc_instr_glue(k, a);
    case CC_INSTR_GLUE_TERM_BASE: return cc_instr_glue_term_base(k, a, b);
    case CC_INSTR_GLUE_TERM_PIECE: return cc_instr_glue_term_piece(k, a, b, c);
    case CC_INSTR_GLUE_TERM: return cc_instr_glue_term(k, a);
    case CC_INSTR_UNGLUE: return cc_instr_unglue(k, a);
    case CB_EXTEND: return cc_instr_extend(k, a, b);
    case CB_DIMENSION: return cc_instr_dimension(k, a);
    }
    s->error = "Unknown instruction.";
    return 0;
}

/* 1 when the term checker's conversion finds the terms equal, 0 when not,
 * 2 when it could not tell (its error is cleared): a search aid only. */
unsigned cb_convertible(uint32_t token, uint32_t a, uint32_t b, uint32_t steps) {
    browser_session *s = lookup(token);
    if (!s) return 2;
    bool equal = cc_kernel_convertible(s->kernel, a, b, steps);
    if (cc_kernel_error_kind(s->kernel) != CC_ERROR_NONE) { cc_kernel_clear_error(s->kernel); return 2; }
    return equal ? 1 : 0;
}

/* The syntax services below return 0 on failure and leave the kernel's
 * error, such as an expired deadline, for the caller to read and clear. */
/* Syntax only: a term with an endpoint substituted for a dimension. */
uint32_t cb_endpoint_term(uint32_t token, uint32_t term, uint32_t dimension, unsigned endpoint) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    return cc_kernel_endpoint_term(s->kernel, term, dimension, endpoint);
}

/* The arena's size: field 0 its nodes, field 1 its bytes. */
uint32_t cb_arena(uint32_t token, unsigned field) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    size_t nodes = 0, bytes = 0;
    cc_kernel_arena(s->kernel, &nodes, &bytes);
    return (uint32_t)(field ? bytes : nodes);
}

/* A symbol id shared by no name the kernel or the page has given out. */
uint32_t cb_fresh_symbol(uint32_t token) {
    browser_session *s = lookup(token);
    return s ? cc_kernel_fresh_symbol(s->kernel) : 0;
}

uint32_t cb_rename(uint32_t token, uint32_t term, unsigned dimension, uint32_t from, uint32_t to) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    return cc_kernel_rename(s->kernel, term, dimension != 0, from, to);
}

/* Syntax only: Equiv(a, b) as the Glue rules state it. */
uint32_t cb_equiv_type(uint32_t token, uint32_t a, uint32_t b) {
    browser_session *s = lookup(token);
    if (!s) return 0;
    return cc_kernel_equiv_type(s->kernel, a, b);
}

uint32_t cb_judgement_count(uint32_t token) {
    browser_session *s = lookup(token);
    size_t count = s ? cc_kernel_judgement_count(s->kernel) : 0;
    return count > UINT32_MAX ? UINT32_MAX : (uint32_t)count;
}

/* Fields: 0 kind, 1 term, 2 other, 3 type, 4 rule, 5-8 premises, 9 entry,
 * 10-11 operands, 12 depth, and 13 + i the position's i-th child index. */
uint32_t cb_judgement(uint32_t token, uint32_t id, uint32_t field) {
    browser_session *s = lookup(token);
    cc_judgement_info j;
    if (!s || !cc_kernel_judgement(s->kernel, id, &j)) return 0;
    if (field >= 13) return field - 13 < j.depth ? j.position[field - 13] : 0;
    const uint32_t fields[] = {j.kind, j.term, j.other, j.type, (uint32_t)j.rule, j.premise[0], j.premise[1],
                               j.premise[2], j.premise[3], j.entry, j.operand[0], j.operand[1], (uint32_t)j.depth};
    return fields[field];
}

uint32_t cb_judgement_context(uint32_t token, uint32_t id, uint32_t index) {
    browser_session *s = lookup(token);
    return s ? cc_kernel_judgement_context(s->kernel, id, index) : 0;
}

uint32_t cb_entry_count(uint32_t token) {
    browser_session *s = lookup(token);
    size_t count = s ? cc_kernel_entry_count(s->kernel) : 0;
    return count > UINT32_MAX ? UINT32_MAX : (uint32_t)count;
}

/* Fields: 0 symbol (a dimension's index), 1 type, 2 dimension, 3 source. */
uint32_t cb_entry(uint32_t token, uint32_t id, unsigned field) {
    browser_session *s = lookup(token);
    uint32_t symbol;
    cc_term type;
    bool dimension;
    cc_judgement_id source;
    if (!s || field > 3 || !cc_kernel_entry(s->kernel, id, &symbol, &type, &dimension, &source)) return 0;
    const uint32_t fields[] = {symbol, type, dimension, source};
    return fields[field];
}
