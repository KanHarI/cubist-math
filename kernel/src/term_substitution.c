/* Capture-avoiding substitution. Term variables and dimensions are separate
 * namespaces; a Path binds its dimension in the family, not in its endpoints.
 * A composition binds its direction in the family and tube terms, but not in
 * the face formulas or starting lid. These distinctions are trusted rules. */
#include "term_internal.h"

bool ck_term_binder(cc_term_kind kind) {
    return kind == CC_PI || kind == CC_LAM || kind == CC_SIGMA || kind == CC_LPI || kind == CC_LLAM;
}

bool ck_dim_binder(cc_term_kind kind) {
    return kind == CC_PATH || kind == CC_PLAM || kind == CC_COMP || kind == CC_HCOMP || kind == CC_TRANS;
}

bool ck_term_free(cc_kernel *k, cc_term term, uint32_t name) {
    typedef struct {
        cc_term term;
        unsigned next;
        bool waiting;
    } frame;
    frame local[32], *frames = local;
    size_t count = 1;
    bool result = false;
    frames[0] = (frame){term, UINT_MAX, false};
    while (count && !k->error[0]) {
        frame *f = &frames[count - 1];
        cc_node n = f->term ? k->nodes[f->term] : (cc_node){0};
        if (f->next == UINT_MAX) {
            uint64_t cached;
            if (f->term && !(n.symbols & (UINT64_C(1) << (name % 64)))) {
                result = false;
                --count;
                continue;
            }
            if (ck_memo_get(k, 1, f->term, name, 0, &cached)) {
                result = cached != 0;
                --count;
                continue;
            }
            if (!f->term) {
                result = false;
                goto done;
            }
            if (!ck_tick(k)) break;
            if (n.kind == CC_VAR) {
                result = n.payload == name;
                goto done;
            }
            f->next = 0;
        }
        if (f->waiting) {
            if (result) goto done;
            f->waiting = false;
        }
        if (f->next == ck_arity(n.kind)) {
            result = false;
            goto done;
        }
        unsigned i = f->next++;
        if (i == 1 && ck_term_binder(n.kind) && n.payload == name)
            continue;
        f->waiting = true;
        if (frames == local && count == sizeof local / sizeof *local) {
            size_t capacity = k->nodes[term].depth + (size_t)1;
            frames = capacity <= SIZE_MAX / sizeof *frames ? malloc(capacity * sizeof *frames) : NULL;
            if (!frames) {
                frames = local;
                ck_fail_as(k, CC_ERROR_RESOURCE, "Variable scan allocation failed.");
                break;
            }
            memcpy(frames, local, sizeof local);
        }
        frames[count++] = (frame){n.child[i], UINT_MAX, false};
        continue;
done:
        ck_memo_put(k, 1, f->term, name, 0, result);
        --count;
    }
    if (frames != local) free(frames);
    return !k->error[0] && result;
}

static uint64_t formula_names(const cc_formula *f) {
    uint64_t names = 0;
    if (f)
        for (size_t i = 0; i < f->length; ++i)
            names |= f->clauses[i].positive | f->clauses[i].negative;
    return names;
}

/* A completed dependency mask is an immutable property of one syntax node.
 * Keep it there instead of evicting it from the shared substitution memo.
 * Until completion, dims remains a conservative mask, so interrupted scans
 * cannot turn a free dimension into an absent one. */
typedef struct {
    cc_term term, tube;
    unsigned next;
    uint64_t result;
} dimension_frame;

uint64_t ck_free_dims(cc_kernel *k, cc_term term) {
    if (!term || k->error[0])
        return 0;
    if (k->nodes[term].dimensions_known)
        return k->nodes[term].dims;
    dimension_frame local[32], *frames = local;
    size_t count = 1;
    frames[0] = (dimension_frame){term, 0, UINT_MAX, 0};
    while (count && !k->error[0]) {
        dimension_frame *frame = &frames[count - 1];
        cc_node n = k->nodes[frame->term];
        if (frame->next == UINT_MAX) {
            if (!ck_tick(k)) break;
            frame->next = 0;
            frame->tube = n.child[1];
            if (n.kind == CC_PAPP || n.kind == CC_TUBE || n.kind == CC_GLUE_SYSTEM)
                frame->result = formula_names(cc_kernel_get_formula(k, n.payload));
        }
        if (frame->next == ck_arity(n.kind)) {
            k->nodes[frame->term].dims = frame->result;
            k->nodes[frame->term].dimensions_known = true;
            --count;
            continue;
        }
        unsigned i = frame->next;
        bool tubes = i == 1 && (n.kind == CC_COMP || n.kind == CC_HCOMP) && n.payload < CC_DIMENSIONS;
        if (tubes && !frame->tube) {
            ++frame->next;
            continue;
        }
        cc_term child = tubes ? k->nodes[frame->tube].child[0] : n.child[i];
        if (child && !k->nodes[child].dimensions_known) {
            if (frames == local && count == sizeof local / sizeof *local) {
                /* Every push follows a child edge (or skips a tube node),
                 * so the input's recorded syntax depth bounds the stack.
                 * Allocate only when the local frames actually run out. */
                size_t capacity = k->nodes[term].depth;
                if (capacity > SIZE_MAX / sizeof *frames || !(frames = malloc(capacity * sizeof *frames))) {
                    frames = local;
                    ck_fail_as(k, CC_ERROR_RESOURCE, "Dimension scan allocation failed.");
                    break;
                }
                memcpy(frames, local, sizeof local);
            }
            frames[count++] = (dimension_frame){child, 0, UINT_MAX, 0};
            continue;
        }
        uint64_t names = child ? k->nodes[child].dims : 0;
        if (tubes) {
            /* The direction binds tube TERMS, never their face formulas. */
            cc_node tube = k->nodes[frame->tube];
            frame->result |= (names & ~(UINT64_C(1) << n.payload)) |
                            formula_names(cc_kernel_get_formula(k, tube.payload));
            frame->tube = tube.child[1];
        } else {
            bool bound = (i == 0 && ck_dim_binder(n.kind) && n.kind != CC_HCOMP) ||
                         (i == 1 && n.kind == CC_PLAM);
            if (bound && n.payload < CC_DIMENSIONS)
                names &= ~(UINT64_C(1) << n.payload);
            frame->result |= names;
            ++frame->next;
        }
    }
    if (frames != local) free(frames);
    return k->error[0] ? 0 : k->nodes[term].dims;
}

unsigned ck_fresh_dimension(cc_kernel *k, uint64_t avoid) {
    for (unsigned d = 0; d < CC_DIMENSIONS; ++d)
        if (!(avoid & (UINT64_C(1) << d)))
            return d;
    ck_fail_as(k, CC_ERROR_RESOURCE, "Native prototype has exhausted its 64 dimension names.");
    return CC_DIMENSIONS;
}

/* Term substitution can rename a dimension, and renaming a term binder is
 * itself a substitution. Keep all three traversals in one continuation loop
 * so capture avoidance does not reintroduce native recursion. */
typedef enum { SUBSTITUTE_TERM, SUBSTITUTE_DIMENSION, SUBSTITUTE_TUBES } substitution_kind;
typedef enum {
    SUBSTITUTE_PREPARE, SUBSTITUTE_RENAME_DIMENSION, SUBSTITUTE_RENAME_TERM,
    SUBSTITUTE_AFTER_RENAME_TERM, SUBSTITUTE_CHILDREN, SUBSTITUTE_TUBE_TAIL,
    SUBSTITUTE_FINISH, SUBSTITUTE_DELEGATED
} substitution_stage;

typedef struct {
    substitution_kind kind;
    substitution_stage stage;
    cc_term term, value;
    uint32_t name, fresh;
    cc_node node;
    /* Descriptors are copied; immutable formula clauses outlive this query.
     * Never retain a pointer into the relocatable formula arena. */
    cc_formula interval, rename_interval;
    cc_formula_id formula;
    unsigned next, waiting;
    bool has_interval, bodies, faces, cache;
} substitution_frame;

/* Most external requests are cached or leave their input untouched. Keep
 * them outside the continuation machinery, using these same entry checks
 * for child requests. Only a request that will traverse needs a frame. */
static bool term_substitution_ready(cc_kernel *k, cc_term term, uint32_t name, cc_term value,
                                    cc_term *result, bool *cache) {
    uint64_t cached;
    *cache = false;
    if (!term) { *result = 0; return false; }
    if (ck_memo_get(k, 3, term, name, value, &cached)) {
        *result = ck_tick(k) ? (cc_term)cached : 0;
        return false;
    }
    if (!ck_tick(k)) { *result = 0; return false; }
    *cache = true;
    if (!ck_term_free(k, term, name)) { *result = term; return false; }
    if (k->nodes[term].kind == CC_VAR && k->nodes[term].payload == name) {
        *result = value;
        return false;
    }
    return true;
}

static bool dimension_substitution_ready(cc_kernel *k, cc_term term, unsigned dim,
                                         const cc_formula *value, cc_term *result,
                                         cc_formula_id *formula, bool *cache) {
    uint64_t cached;
    *cache = false;
    if (!term || !ck_tick(k)) { *result = 0; return false; }
    if (dim >= CC_DIMENSIONS || !value || value->sort != CC_INTERVAL) {
        ck_fail(k, "Invalid dimension substitution.");
        *result = 0;
        return false;
    }
    uint64_t free = ck_free_dims(k, term);
    if (k->error[0]) { *result = 0; return false; }
    if (!(free & (UINT64_C(1) << dim))) { *result = term; return false; }
    *formula = ck_formula(k, value);
    if (!*formula) { *result = 0; return false; }
    if (ck_memo_get(k, 6, term, dim, *formula, &cached)) {
        *result = (cc_term)cached;
        return false;
    }
    *cache = true;
    return true;
}

static substitution_frame dimension_request(cc_term term, unsigned dim, const cc_formula *value) {
    substitution_frame f = {.kind = SUBSTITUTE_DIMENSION, .term = term, .name = dim,
                            .has_interval = value != NULL};
    if (value) f.interval = *value;
    return f;
}

static substitution_frame tube_request(cc_term term, unsigned dim, const cc_formula *value,
                                        bool bodies, bool faces) {
    substitution_frame f = dimension_request(term, dim, value);
    f.kind = SUBSTITUTE_TUBES;
    f.bodies = bodies;
    f.faces = faces;
    return f;
}

static bool substitution_push(cc_kernel *k, substitution_frame **frames, size_t *capacity,
                              size_t count, substitution_frame *local, substitution_frame child,
                              cc_term *result) {
    if (k->error[0]) return false;
    if (child.kind == SUBSTITUTE_TERM) {
        if (!term_substitution_ready(k, child.term, child.name, child.value, result, &child.cache)) {
            if (*result && child.cache) ck_memo_put(k, 3, child.term, child.name, child.value, *result);
            return false;
        }
    } else if (child.kind == SUBSTITUTE_DIMENSION) {
        if (!dimension_substitution_ready(k, child.term, child.name,
                child.has_interval ? &child.interval : NULL, result, &child.formula, &child.cache))
            return false;
    } else if (!child.term || !ck_tick(k)) {
        *result = 0;
        return false;
    }
    if (count == *capacity) {
        if (*capacity >= 16384)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Substitution stack depth exceeded.");
        size_t next = *capacity * 2;
        substitution_frame *grown = *frames == local ? malloc(next * sizeof *grown)
                                                     : realloc(*frames, next * sizeof *grown);
        if (!grown)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Substitution stack allocation failed.");
        if (*frames == local) memcpy(grown, local, count * sizeof *grown);
        *frames = grown;
        *capacity = next;
    }
    (*frames)[count] = child;
    return true;
}

static cc_formula_id substitute_formula(cc_kernel *k, cc_formula_id id, unsigned dim,
                                        const cc_formula *value, cc_term_kind kind) {
    cc_sort sort = kind == CC_PAPP ? CC_INTERVAL : CC_FACE;
    const cc_formula *source = cc_kernel_get_formula(k, id);
    cc_formula changed;
    cc_init(&changed, sort);
    if (!ck_deadline(k)) { cc_clear(&changed); return 0; }
    cc_status status = !source ? CC_BAD_INPUT : sort == CC_FACE
        ? cc_face_substitute(&changed, source, dim, value)
        : cc_interval_substitute(&changed, source, dim, value);
    if (!ck_deadline(k)) { cc_clear(&changed); return 0; }
    cc_formula_id result = 0;
    if (ck_formula_result(k, status, status == CC_LIMIT_EXCEEDED
            ? "Cubical lattice term-size or work budget exceeded."
            : kind == CC_PAPP ? "Invalid interval substitution."
            : kind == CC_GLUE_SYSTEM ? "Invalid Glue face substitution."
            : "Invalid face substitution."))
        result = ck_formula(k, &changed);
    cc_clear(&changed);
    return result;
}

static cc_term substitution(cc_kernel *k, substitution_frame root) {
    substitution_frame local[32], *frames = local;
    size_t count = 1, capacity = sizeof local / sizeof *local;
    cc_term result = 0;
    frames[0] = root;
    while (count && !k->error[0]) {
        substitution_frame *f = &frames[count - 1];
        if (f->waiting) {
            f->node.child[f->waiting - 1] = result;
            f->waiting = 0;
        }
        switch (f->stage) {
        case SUBSTITUTE_PREPARE: {
            f->node = k->nodes[f->term];
            if (f->kind == SUBSTITUTE_TUBES) {
                if (f->node.kind != CC_TUBE) {
                    ck_fail(k, "Malformed composition tube list.");
                    break;
                }
                f->stage = SUBSTITUTE_TUBE_TAIL;
                if (f->bodies) {
                    substitution_frame child = dimension_request(f->node.child[0], f->name, &f->interval);
                    f->waiting = 1;
                    if (substitution_push(k, &frames, &capacity, count, local, child, &result)) ++count;
                }
                break;
            }
            if (f->kind == SUBSTITUTE_DIMENSION && ck_dim_binder(f->node.kind) &&
                f->node.payload >= CC_DIMENSIONS) {
                ck_fail(k, "Dimension binder outside native range.");
                break;
            }
            f->stage = SUBSTITUTE_RENAME_TERM;
            if (ck_dim_binder(f->node.kind) && f->node.payload < CC_DIMENSIONS) {
                uint64_t value_dims = f->kind == SUBSTITUTE_TERM
                    ? ck_free_dims(k, f->value) : formula_names(&f->interval);
                if ((f->kind == SUBSTITUTE_TERM || f->node.payload != f->name) &&
                    (value_dims & (UINT64_C(1) << f->node.payload))) {
                    uint64_t avoid = ck_free_dims(k, f->term) | value_dims |
                                     (UINT64_C(1) << f->node.payload);
                    if (f->kind == SUBSTITUTE_DIMENSION) avoid |= UINT64_C(1) << f->name;
                    f->fresh = ck_fresh_dimension(k, avoid);
                    cc_formula variable;
                    cc_init(&variable, CC_INTERVAL);
                    if (ck_formula_result(k, cc_generator(&variable, f->fresh, true),
                            f->kind == SUBSTITUTE_TERM ? "Term substitution dimension allocation failed."
                                                      : "Fresh dimension allocation failed.")) {
                        cc_formula_id id = ck_formula(k, &variable);
                        if (id) f->rename_interval = *cc_kernel_get_formula(k, id);
                    }
                    cc_clear(&variable);
                    f->stage = SUBSTITUTE_RENAME_DIMENSION;
                }
            }
            break;
        }
        case SUBSTITUTE_RENAME_DIMENSION: {
            unsigned i = f->next++;
            if (i == 2) {
                f->node.payload = f->fresh;
                f->stage = SUBSTITUTE_RENAME_TERM;
                break;
            }
            bool tube = i == 1 && (f->node.kind == CC_COMP || f->node.kind == CC_HCOMP);
            bool bound = i == 0 ? f->node.kind != CC_HCOMP : f->node.kind == CC_PLAM || tube;
            if (!bound) break;
            substitution_frame child = tube
                ? tube_request(f->node.child[i], f->node.payload, &f->rename_interval, true, false)
                : dimension_request(f->node.child[i], f->node.payload, &f->rename_interval);
            f->waiting = i + 1;
            if (substitution_push(k, &frames, &capacity, count, local, child, &result)) ++count;
            break;
        }
        case SUBSTITUTE_RENAME_TERM:
            if (f->kind == SUBSTITUTE_TERM && ck_term_binder(f->node.kind) &&
                f->node.payload != f->name && ck_term_free(k, f->value, f->node.payload)) {
                f->fresh = ck_fresh_symbol(k);
                substitution_frame child = {.kind = SUBSTITUTE_TERM, .term = f->node.child[1],
                                             .name = f->node.payload, .value = ck_var(k, f->fresh)};
                f->stage = SUBSTITUTE_AFTER_RENAME_TERM;
                f->waiting = 2;
                if (substitution_push(k, &frames, &capacity, count, local, child, &result)) ++count;
                break;
            }
            f->next = 0;
            f->stage = SUBSTITUTE_CHILDREN;
            if (f->kind == SUBSTITUTE_DIMENSION && f->node.kind == CC_TUBE) {
                substitution_frame child = tube_request(f->term, f->name, &f->interval, true, true);
                f->stage = SUBSTITUTE_DELEGATED;
                if (substitution_push(k, &frames, &capacity, count, local, child, &result)) ++count;
            }
            break;
        case SUBSTITUTE_AFTER_RENAME_TERM:
            f->node.payload = f->fresh;
            f->next = 0;
            f->stage = SUBSTITUTE_CHILDREN;
            break;
        case SUBSTITUTE_CHILDREN: {
            if (f->next == ck_arity(f->node.kind)) {
                f->stage = SUBSTITUTE_FINISH;
                break;
            }
            unsigned i = f->next++;
            substitution_frame child;
            if (f->kind == SUBSTITUTE_TERM) {
                if (i == 1 && ck_term_binder(f->node.kind) && f->node.payload == f->name) break;
                child = (substitution_frame){.kind = SUBSTITUTE_TERM, .term = f->node.child[i],
                                             .name = f->name, .value = f->value};
            } else if (i == 1 && (f->node.kind == CC_COMP || f->node.kind == CC_HCOMP)) {
                child = tube_request(f->node.child[i], f->name, &f->interval, f->node.payload != f->name, true);
            } else {
                bool bound = ck_dim_binder(f->node.kind) &&
                    ((i == 0 && f->node.kind != CC_HCOMP) || (i == 1 && f->node.kind == CC_PLAM));
                if (bound && f->node.payload == f->name) break;
                child = dimension_request(f->node.child[i], f->name, &f->interval);
            }
            f->waiting = i + 1;
            if (substitution_push(k, &frames, &capacity, count, local, child, &result)) ++count;
            break;
        }
        case SUBSTITUTE_TUBE_TAIL: {
            if (f->faces)
                f->node.payload = substitute_formula(k, f->node.payload, f->name, &f->interval,
                                                     CC_TUBE);
            substitution_frame child = tube_request(f->node.child[1], f->name, &f->interval, f->bodies, f->faces);
            f->stage = SUBSTITUTE_FINISH;
            f->waiting = 2;
            if (substitution_push(k, &frames, &capacity, count, local, child, &result)) ++count;
            break;
        }
        case SUBSTITUTE_FINISH: {
            if (f->kind == SUBSTITUTE_DIMENSION && f->node.kind == CC_GLUE_SYSTEM)
                f->node.payload = substitute_formula(k, f->node.payload, f->name, &f->interval,
                                                     CC_GLUE_SYSTEM);
            if (f->kind == SUBSTITUTE_DIMENSION && f->node.kind == CC_PAPP)
                f->node.payload = substitute_formula(k, f->node.payload, f->name, &f->interval,
                                                     CC_PAPP);
            cc_node original = k->nodes[f->term], n = f->node;
            result = f->kind != SUBSTITUTE_TUBES && n.payload == original.payload &&
                     !memcmp(n.child, original.child, sizeof n.child) ? f->term
                : ck_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], n.child[3]);
            goto complete;
        }
        case SUBSTITUTE_DELEGATED:
            goto complete;
        }
        continue;
complete:
        if (result && f->cache && !k->error[0])
            ck_memo_put(k, f->kind == SUBSTITUTE_TERM ? 3 : 6, f->term, f->name,
                        f->kind == SUBSTITUTE_TERM ? f->value : f->formula, result);
        --count;
    }
    if (frames != local) free(frames);
    return k->error[0] ? 0 : result;
}

cc_term ck_substitute(cc_kernel *k, cc_term term, uint32_t name, cc_term value) {
    cc_term result;
    bool cache;
    if (!term_substitution_ready(k, term, name, value, &result, &cache)) {
        if (result && cache) ck_memo_put(k, 3, term, name, value, result);
        return k->error[0] ? 0 : result;
    }
    return substitution(k, (substitution_frame){.kind = SUBSTITUTE_TERM, .stage = SUBSTITUTE_PREPARE,
                                                .term = term, .name = name, .value = value, .cache = true});
}

cc_term ck_dimension_substitute(cc_kernel *k, cc_term term, unsigned dim, const cc_formula *value) {
    cc_formula stable = value ? *value : (cc_formula){0};
    cc_term result;
    cc_formula_id formula = 0;
    bool cache;
    if (!dimension_substitution_ready(k, term, dim, value ? &stable : NULL, &result, &formula, &cache))
        return k->error[0] ? 0 : result;
    substitution_frame root = dimension_request(term, dim, &stable);
    root.stage = SUBSTITUTE_PREPARE;
    root.formula = formula;
    root.cache = true;
    return substitution(k, root);
}


cc_term ck_endpoint_term(cc_kernel *k, cc_term term, unsigned dim, unsigned endpoint) {
    cc_formula value;
    cc_init(&value, CC_INTERVAL);
    if (!ck_formula_result(k, endpoint ? cc_one(&value) : CC_OK, "Endpoint allocation failed.")) {
        cc_clear(&value);
        return 0;
    }
    cc_term result = ck_dimension_substitute(k, term, dim, &value);
    cc_clear(&value);
    return result;
}

cc_term ck_restrict(cc_kernel *k, cc_term term, cc_clause face) {
    for (unsigned dim = 0; dim < CC_DIMENSIONS; ++dim) {
        uint64_t bit = UINT64_C(1) << dim;
        if (face.positive & bit)
            term = ck_endpoint_term(k, term, dim, 1);
        if (face.negative & bit)
            term = ck_endpoint_term(k, term, dim, 0);
    }
    return term;
}

cc_formula_id ck_interval_variable(cc_kernel *k, unsigned dim) {
    cc_formula f;
    cc_init(&f, CC_INTERVAL);
    cc_formula_id result = 0;
    if (ck_formula_result(k, cc_generator(&f, dim, true), "Invalid interval variable."))
        result = ck_formula(k, &f);
    cc_clear(&f);
    return result;
}

cc_formula_id ck_endpoint_face(cc_kernel *k, unsigned dim, unsigned endpoint) {
    cc_formula f;
    cc_init(&f, CC_FACE);
    cc_formula_id result = 0;
    if (ck_formula_result(k, cc_generator(&f, dim, endpoint != 0), "Invalid face variable."))
        result = ck_formula(k, &f);
    cc_clear(&f);
    return result;
}
