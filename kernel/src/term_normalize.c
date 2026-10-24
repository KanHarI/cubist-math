/* Call-by-name weak-head reduction is the conversion engine's workhorse.
 * Application first exposes its FUNCTION, not its argument. Induction first
 * exposes the SCRUTINEE, not every branch or recursive hypothesis. Therefore a
 * branch that ignores its recursive hypothesis does not evaluate that subtree.
 * Full normalization is only requested for an explicit inspection result. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

static cc_term nonempty_system(cc_kernel *k, cc_term system, bool types) {
    if (!system)
        return 0;
    cc_node piece = k->nodes[system];
    const cc_formula *face = cc_kernel_get_formula(k, piece.payload);
    if (!face || face->sort != CC_FACE)
        return ck_fail(k, "Unchecked partial face reached reduction."), 0;
    bool empty = face->length == 0;
    unsigned next = types ? 2 : 1;
    cc_term tail = nonempty_system(k, piece.child[next], types);
    if (empty)
        return tail;
    if (tail == piece.child[next])
        return system;
    piece.child[next] = tail;
    return ck_make(k, piece.kind, piece.payload, piece.child[0], piece.child[1], piece.child[2], 0);
}

/* Returning a continuation performs the same next weak-head request without
 * retaining a native frame. Prerequisite head queries remain guarded calls. */
static cc_term weak_again(cc_term *next, cc_term term) {
    *next = term;
    return 0;
}

static cc_term weak(cc_kernel *k, cc_term term, cc_term *next) {
    cc_node n = k->nodes[term];
    if (n.kind == CC_HCOMP || n.kind == CC_TRANS)
        return ck_hit_reduce(k, term);
    if (n.kind == CC_DEFREF) {
        if (!n.payload || n.payload >= k->definition_count)
            return ck_fail(k, "Unknown definition reached reduction."), 0;
        return weak_again(next, k->definitions[n.payload].value);
    }
    if (n.kind == CC_GLUE || n.kind == CC_GLUE_TERM) {
        unsigned slot = n.kind == CC_GLUE ? 1 : 2;
        cc_term system = nonempty_system(k, n.child[slot], n.kind == CC_GLUE);
        if (system != n.child[slot]) {
            n.child[slot] = system;
            return weak_again(next, ck_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], 0));
        }
        while (system) {
            cc_node piece = k->nodes[system];
            const cc_formula *face = cc_kernel_get_formula(k, piece.payload);
            if (!face || face->sort != CC_FACE)
                return ck_fail(k, "Unchecked Glue face reached reduction."), 0;
            if (face->length == 1 && !face->clauses[0].positive && !face->clauses[0].negative)
                return weak_again(next, piece.child[0]);
            system = piece.child[n.kind == CC_GLUE ? 2 : 1];
        }
    }
    /* Glue eta: glue [φ ↦ b|φ] (unglue b) is b. Reduction is trusted, so its
     * side conditions are syntactic, as instructions' are (ck_alpha_equal):
     * the same Glue type, and each piece the restriction of b. When the sides
     * are equal only after computation, the redex stays uncontracted, and
     * still checked; conversion never decides a reduction step. */
    if (n.kind == CC_GLUE_TERM) {
        cc_term projected = ck_whnf(k, n.child[1]);
        if (!projected)
            return 0;
        cc_node projection = k->nodes[projected];
        if (projection.kind == CC_UNGLUE && ck_alpha_equal(k, n.child[0], projection.child[0])) {
            bool agrees = true;
            for (cc_term system = n.child[2]; system && agrees;) {
                cc_node piece = k->nodes[system];
                const cc_formula *raw = cc_kernel_get_formula(k, piece.payload);
                cc_formula face;
                cc_init(&face, CC_FACE);
                if (!ck_formula_result(k, cc_copy(&face, raw), "Glue eta face allocation failed."))
                    return 0;
                for (size_t i = 0; i < face.length && agrees; ++i)
                    agrees = ck_alpha_equal(k, piece.child[0], ck_restrict(k, projection.child[1], face.clauses[i]));
                cc_clear(&face);
                system = piece.child[1];
            }
            if (agrees)
                return weak_again(next, projection.child[1]);
        }
    }
    if (n.kind == CC_UNGLUE) {
        cc_node type = k->nodes[n.child[0]];
        if (type.kind != CC_GLUE)
            return ck_fail(k, "Unchecked Glue projection reached reduction."), 0;
        for (cc_term system = type.child[1]; system;) {
            cc_node piece = k->nodes[system];
            const cc_formula *face = cc_kernel_get_formula(k, piece.payload);
            if (face->length == 1 && !face->clauses[0].positive && !face->clauses[0].negative) {
                cc_term function = ck_make(k, CC_FST, 0, piece.child[1], 0, 0, 0);
                return weak_again(next, app(k, function, n.child[1]));
            }
            system = piece.child[2];
        }
        cc_term value = ck_whnf(k, n.child[1]);
        if (!value)
            return 0;
        if (k->nodes[value].kind == CC_GLUE_TERM)
            return weak_again(next, k->nodes[value].child[1]);
        return value == n.child[1] ? term : ck_make(k, CC_UNGLUE, 0, n.child[0], value, 0, 0);
    }
    if (n.kind == CC_APP) {
        cc_term fn = ck_whnf(k, n.child[0]);
        if (fn && k->nodes[fn].kind == CC_ELIM) {
            bool reduced = false;
            cc_term result = ck_eliminate(k, fn, n.child[1], true, &reduced);
            return reduced ? weak_again(next, result) : result;
        }
        if (!fn)
            return 0;
        cc_node head = k->nodes[fn];
        if (head.kind == CC_LAM)
            return weak_again(next, ck_substitute(k, head.child[1], head.payload, n.child[1]));
        return fn == n.child[0] ? term : app(k, fn, n.child[1]);
    }
    /* ∀-β (G0 §2.7): instantiation of a level lambda substitutes the level. */
    if (n.kind == CC_LAPP) {
        cc_term fn = ck_whnf(k, n.child[0]);
        if (!fn)
            return 0;
        cc_node head = k->nodes[fn];
        if (head.kind == CC_LLAM)
            return weak_again(next, ck_level_instantiate(k, head.child[1], head.payload, n.child[1]));
        return fn == n.child[0] ? term : ck_make(k, CC_LAPP, 0, fn, n.child[1], 0, 0);
    }
    if (n.kind == CC_PAIR) {
        /* Surjective pairing: (fst p, snd p) is p. Inspect only projection
         * syntax here: forcing arbitrary components would destroy the
         * demand-driven strategy. The two projections must be of the same
         * term up to bound names, as for Glue eta above. */
        cc_node first = k->nodes[n.child[1]];
        cc_node second = k->nodes[n.child[2]];
        if (first.kind == CC_FST && second.kind == CC_SND &&
            ck_alpha_equal(k, first.child[0], second.child[0]))
            return weak_again(next, first.child[0]);
    }
    if (n.kind == CC_FST || n.kind == CC_SND) {
        cc_term pair = ck_whnf(k, n.child[0]);
        if (!pair)
            return 0;
        cc_node head = k->nodes[pair];
        if (head.kind == CC_PAIR)
            return weak_again(next, head.child[n.kind == CC_FST ? 1 : 2]);
        return pair == n.child[0] ? term : ck_make(k, n.kind, 0, pair, 0, 0, 0);
    }

    if (n.kind == CC_SUMREC) {
        cc_term value = ck_whnf(k, n.child[3]);
        if (!value)
            return 0;
        cc_node head = k->nodes[value];
        if (head.kind == CC_INL || head.kind == CC_INR)
            return weak_again(next, app(k, n.child[head.kind == CC_INL ? 1 : 2], head.child[1]));
        return value == n.child[3] ? term : ck_make(k, CC_SUMREC, 0, n.child[0], n.child[1], n.child[2], value);
    }
    if (n.kind == CC_UNITREC) {
        cc_term value = ck_whnf(k, n.child[2]);
        if (!value)
            return 0;
        if (k->nodes[value].kind == CC_POINT)
            return weak_again(next, n.child[1]);
        return value == n.child[2] ? term : ck_make(k, CC_UNITREC, 0, n.child[0], n.child[1], value, 0);
    }

    if (n.kind == CC_PAPP) {
        const cc_formula *arg = cc_kernel_get_formula(k, n.payload);
        if (!arg || arg->sort != CC_INTERVAL)
            return ck_fail(k, "Path application requires an interval expression."), 0;
        if (!n.child[1] || k->nodes[n.child[1]].kind != CC_PATH) {
            /* A raw head query may see an explicit path lambda before type
             * elaboration has reconstructed its annotation. Lambda beta is
             * purely syntactic and needs no endpoint/type assumption. A
             * neutral path still requires its independently checked type. */
            cc_formula argument;
            cc_init(&argument, CC_INTERVAL);
            if (!ck_formula_result(k, cc_copy(&argument, arg), "Interval copy failed."))
                return 0;
            cc_term path = ck_whnf(k, n.child[0]);
            cc_term result = 0;
            if (path && k->nodes[path].kind == CC_PLAM) {
                cc_node line = k->nodes[path];
                result = ck_dimension_substitute(k, line.child[1], line.payload, &argument);
            } else if (path) {
                ck_fail(k, "Unchecked path application reached reduction.");
            }
            cc_clear(&argument);
            return weak_again(next, result);
        }
        cc_node type = k->nodes[n.child[1]];
        if (!arg->length)
            return weak_again(next, type.child[1]);
        if (arg->length == 1 && !arg->clauses[0].positive && !arg->clauses[0].negative)
            return weak_again(next, type.child[2]);
        cc_formula argument;
        cc_init(&argument, CC_INTERVAL);
        if (!ck_formula_result(k, cc_copy(&argument, arg), "Interval copy failed."))
            return 0;
        cc_term path = ck_whnf(k, n.child[0]);
        cc_term result = 0;
        bool beta = path && k->nodes[path].kind == CC_PLAM;
        if (beta) {
            cc_node line = k->nodes[path];
            result = ck_dimension_substitute(k, line.child[1], line.payload, &argument);
        } else if (path) {
            result = path == n.child[0] ? term : ck_make(k, CC_PAPP, n.payload, path, n.child[1], 0, 0);
        }
        cc_clear(&argument);
        return beta ? weak_again(next, result) : result;
    }
    /* ∀-η: λ (x < ω). f {x} is f when x is not free in f. */
    if (n.kind == CC_LLAM) {
        cc_node head = k->nodes[n.child[1]];
        if (head.kind == CC_LAPP && k->nodes[head.child[1]].kind == CC_VAR &&
            k->nodes[head.child[1]].payload == n.payload && !ck_term_free(k, head.child[0], n.payload))
            return weak_again(next, head.child[0]);
        return term;
    }
    if (n.kind == CC_LAM || n.kind == CC_PLAM) {
        /* A lambda is already a weak head. Eta may inspect its syntax, but
         * must not evaluate the body before an argument is supplied. */
        cc_term body = n.child[1];
        cc_node head = k->nodes[body];
        if (n.kind == CC_LAM && head.kind == CC_APP) {
            cc_node argument = k->nodes[head.child[1]];
            if (argument.kind == CC_VAR && argument.payload == n.payload && !ck_term_free(k, head.child[0], n.payload))
                return weak_again(next, head.child[0]);
        }
        if (n.kind == CC_PLAM && head.kind == CC_PAPP) {
            const cc_formula *arg = cc_kernel_get_formula(k, head.payload);
            if (arg && n.payload < CC_DIMENSIONS && arg->length == 1 && !arg->clauses[0].negative &&
                arg->clauses[0].positive == (UINT64_C(1) << n.payload) &&
                !(ck_free_dims(k, head.child[0]) & (UINT64_C(1) << n.payload)))
                return weak_again(next, head.child[0]);
        }
        return body == n.child[1] ? term : ck_make(k, n.kind, n.payload, n.child[0], body, 0, 0);
    }
    if (n.kind == CC_COMP)
        return ck_reduce_composition(k, term);
    return term;
}

/* Tail reductions keep only the handles awaiting a completed head, for the
 * same cache publication that recursive returns used to perform. Failed work
 * never publishes these entries. Each weak-head request owns its buffer.
 * Once it is full, further tails still reduce but are not retained for caching;
 * ticks and the deadline bound execution independently of this memo storage. */
#define WEAK_LOCAL_TAILS 32
#define WEAK_MAX_TAILS 16384

static cc_term weak_tails(cc_kernel *k, cc_term term) {
    cc_term local[WEAK_LOCAL_TAILS], *pending = local;
    size_t count = 0, capacity = WEAK_LOCAL_TAILS;
    cc_term result = 0;
    for (;;) {
        cc_term next = 0;
        result = weak(k, term, &next);
        if (k->error[0] || !next)
            break;
        if (count == capacity && capacity < WEAK_MAX_TAILS) {
            size_t grown = capacity * 2;
            cc_term *buffer = pending == local ? malloc(grown * sizeof *buffer)
                : realloc(pending, grown * sizeof *buffer);
            if (!buffer) {
                ck_fail_as(k, CC_ERROR_RESOURCE, "Normalization stack allocation failed.");
                break;
            }
            if (pending == local)
                memcpy(buffer, local, count * sizeof *buffer);
            pending = buffer;
            capacity = grown;
        }
        if (count < capacity)
            pending[count++] = term;
        term = next;
        if (term >= k->count || !ck_tick(k)) {
            result = 0;
            break;
        }
        if (k->weak_cache[term]) {
            result = k->weak_cache[term];
            break;
        }
    }
    if (result && !k->error[0]) {
        k->weak_cache[term] = result;
        for (size_t i = 0; i < count; ++i)
            k->weak_cache[pending[i]] = result;
    } else {
        result = 0;
    }
    if (pending != local)
        free(pending);
    return result;
}

cc_term ck_whnf(cc_kernel *k, cc_term term) {
    if (!term || term >= k->count || !ck_tick(k))
        return 0;
    if (k->weak_cache[term])
        return k->weak_cache[term];
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail_as(k, CC_ERROR_RESOURCE, "Native reduction recursion depth exceeded."), 0;
    }
    cc_term result = weak_tails(k, term);
    --k->recursion;
    return result;
}

/* Full normalization owns an explicit continuation stack. Weak-head reduction,
 * substitution and comparison retain their own guards; this does not remove
 * the syntax-depth bound protecting those other traversals. A frame holds
 * handles and node copies, never pointers into an arena that can move. */
typedef struct {
    cc_term term, rebuilt, value, system;
    cc_node node;
    size_t clause;
    unsigned next, phase;
    /* A folded definition application, and the inner part of one's spine:
     * rebuilt from their normalized arguments, never reduced. */
    bool folded, spine;
} normal_frame;
enum { NORMAL_ENTER, NORMAL_CHILDREN, NORMAL_CHILD_DONE, NORMAL_GLUE,
       NORMAL_GLUE_DONE, NORMAL_REDUCE, NORMAL_REDUCED };
#define NORMAL_LOCAL_FRAMES 32
#define NORMAL_MAX_FRAMES 16384

typedef struct {
    normal_frame *frames;
    size_t count, capacity;
    normal_frame local[NORMAL_LOCAL_FRAMES];
} normal_stack;

static bool normal_push(cc_kernel *k, normal_stack *stack, cc_term term, bool spine) {
    if (stack->count == stack->capacity) {
        if (stack->capacity == NORMAL_MAX_FRAMES)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Native normal-form depth exceeded.");
        size_t capacity = stack->capacity * 2;
        normal_frame *frames = stack->frames == stack->local
            ? malloc(capacity * sizeof *frames)
            : realloc(stack->frames, capacity * sizeof *frames);
        if (!frames)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Normalization stack allocation failed.");
        if (stack->frames == stack->local)
            memcpy(frames, stack->local, stack->count * sizeof *frames);
        stack->frames = frames;
        stack->capacity = capacity;
    }
    stack->frames[stack->count++] = (normal_frame){.term = term, .spine = spine};
    return true;
}

/* The nodes of an application spine: applications, level applications,
 * projections and path applications, each applied to the part in its first
 * child. */
static bool spine_node(cc_term_kind kind) {
    return kind == CC_APP || kind == CC_LAPP || kind == CC_FST || kind == CC_SND || kind == CC_PAPP;
}

/* Whether a term is a definition, applied or projected. */
static bool definition_spine(const cc_kernel *k, cc_term term) {
    while (spine_node(k->nodes[term].kind))
        term = k->nodes[term].child[0];
    return k->nodes[term].kind == CC_DEFREF;
}

/* Whether a weak head is an elimination stuck on a value that is no
 * constructor: an eliminator applied, a recursor, an abort or an unglue, or
 * a projection or application of one. Its last step rebuilt it in place, the
 * stuck value reduced. A composition is none: its step also drops the tubes
 * on empty faces, which its head keeps dropped. */
static bool stuck_elimination(const cc_kernel *k, cc_term head) {
    bool applied = false;
    while (spine_node(k->nodes[head].kind)) {
        head = k->nodes[head].child[0];
        applied = true;
    }
    switch (k->nodes[head].kind) {
    case CC_ELIM:
        return applied;
    case CC_NATREC: case CC_WREC: case CC_SUMREC: case CC_UNITREC: case CC_PUSH_ELIM:
    case CC_ABORT: case CC_UNGLUE:
        return true;
    default:
        return false;
    }
}

/* Whether a step rebuilt `last` as `head` in place, reducing only its stuck
 * part: the same node, with at most one part changed. An eliminator applied
 * is stuck on its scrutinee, so there the eliminator itself must be the
 * one `last` applied, unreduced: an eliminator that a definition or a match
 * computed is another computation. Each part is compared with the weak head
 * the step took of it, never with another term, so interning cannot make a
 * computed part look unchanged. */
static bool rebuilt_in_place(const cc_kernel *k, cc_term last, cc_term head) {
    cc_node a = k->nodes[last], b = k->nodes[head];
    if (a.kind != b.kind || a.payload != b.payload)
        return false;
    if (b.kind == CC_APP && k->nodes[b.child[0]].kind == CC_ELIM && a.child[0] != b.child[0])
        return false;
    unsigned changed = 0;
    for (unsigned i = 0; i < 4; ++i)
        changed += a.child[i] != b.child[i];
    return changed <= 1;
}

/* Whether a weak head is data: a constructor applied, a pair, an injection,
 * a point or a glued element, or a variable applied or projected, as opposed
 * to a function, a path, a type, or an eliminator or composition stuck. */
static bool computed_data(const cc_kernel *k, cc_term head) {
    cc_term root = head;
    while (spine_node(k->nodes[root].kind))
        root = k->nodes[root].child[0];
    if (k->nodes[root].kind == CC_VAR || k->nodes[root].kind == CC_CON)
        return true;
    switch (k->nodes[head].kind) {
    case CC_PAIR: case CC_INL: case CC_INR: case CC_POINT: case CC_ZERO: case CC_SUCC: case CC_SUP:
    case CC_PUSH_LEFT: case CC_PUSH_RIGHT: case CC_GLUE_TERM:
        return true;
    default:
        return false;
    }
}

/* The weak head, by the steps ck_whnf takes, and the first definition spine
 * among the terms those steps pass through, where a folded normal form stops
 * when the head is no data. Only these steps are watched, not those that
 * compute a head for one of them: λ y. f(y) is f by eta there, so its
 * application to x reaches f's body without passing through f(x). `last` is
 * the term whose step gave the head: a stuck elimination rebuilt in place has
 * its stuck value replaced by its weak head, where `last` has it as written.
 * No weak
 * cache is read here, so the spine found does not depend on what was
 * computed before. */
static cc_term folding_head(cc_kernel *k, cc_term term, cc_term *spine, cc_term *last) {
    *spine = 0;
    if (!ck_tick(k))
        return 0;
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail_as(k, CC_ERROR_RESOURCE, "Native reduction recursion depth exceeded."), 0;
    }
    cc_term result = 0;
    for (;;) {
        if (!*spine && definition_spine(k, term))
            *spine = term;
        cc_term next = 0;
        *last = term;
        result = weak(k, term, &next);
        if (k->error[0] || !next)
            break;
        term = next;
        if (term >= k->count || !ck_tick(k)) {
            result = 0;
            break;
        }
    }
    --k->recursion;
    return k->error[0] ? 0 : result;
}

/* Normalize partial bodies only on the endpoints common to every clause of
 * their face. Preserve disjunctions and piece order. The tail belongs to its
 * own face, and a composition's direction never occurs in its tube faces. */
static bool normal_restrict(cc_kernel *k, cc_node *node) {
    if (node->kind != CC_TUBE && node->kind != CC_GLUE_SYSTEM)
        return true;
    const cc_formula *face = cc_kernel_get_formula(k, node->payload);
    if (!face || face->sort != CC_FACE)
        return ck_fail(k, "Unchecked partial face reached reduction.");
    if (face->length) {
        cc_clause common = face->clauses[0];
        for (size_t i = 1; i < face->length; ++i) {
            common.positive &= face->clauses[i].positive;
            common.negative &= face->clauses[i].negative;
        }
        unsigned parts = node->kind == CC_GLUE_SYSTEM ? 2 : 1;
        for (unsigned i = 0; i < parts; ++i) {
            node->child[i] = ck_restrict(k, node->child[i], common);
            if (!node->child[i])
                return false;
        }
    }
    return true;
}

/* The full normal form, or, folding, the folded one: there a definition
 * applied or projected whose weak head is stuck on an eliminator stays as it
 * was written, its arguments normalized, folded too. Each has its cache. */
static cc_term normal(cc_kernel *k, cc_term term, bool fold) {
    if (!term || term >= k->count)
        return 0;
    if (fold && !k->folded_cache) {
        k->folded_cache = calloc(k->capacity, sizeof *k->folded_cache);
        if (!k->folded_cache)
            return ck_fail_as(k, CC_ERROR_RESOURCE, "Normal cache allocation failed."), 0;
    }
    /* Each cache is looked up again after any allocation, which can move it. */
#define CACHE (fold ? k->folded_cache : k->normal_cache)
    /* Charge hits too: a warm cache cannot bypass a budget or deadline.
     * Misses take their entry step in ck_whnf, as before. A folded query's
     * term is unfolded, so the folded cache never answers it. */
    if (!fold && CACHE[term])
        return ck_tick(k) ? CACHE[term] : 0;
    /* Protect any re-entry through other, still recursive reducer APIs.
     * Traversing normal-form children does not consume native stack depth. */
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail_as(k, CC_ERROR_RESOURCE, "Native normal-form depth exceeded."), 0;
    }
    normal_stack stack = {.capacity = NORMAL_LOCAL_FRAMES};
    stack.frames = stack.local;
    normal_push(k, &stack, term, false);
    cc_term result = 0;
    while (stack.count && !k->error[0]) {
        normal_frame *frame = &stack.frames[stack.count - 1];
        switch (frame->phase) {
        case NORMAL_ENTER: {
            if (!frame->term || frame->term >= k->count)
                goto failed;
            if (frame->spine) {
                frame->node = k->nodes[frame->term];
                frame->phase = NORMAL_CHILDREN;
                break;
            }
            /* Folding, the term asked for is unfolded, and only it: its result
             * is not the one its occurrences inside other terms have. */
            bool root = fold && stack.count == 1;
            if (!root && CACHE[frame->term]) {
                result = ck_tick(k) ? CACHE[frame->term] : 0;
                goto complete;
            }
            cc_term spine = 0, last = 0, head = fold ? folding_head(k, frame->term, &spine, &last) : ck_whnf(k, frame->term);
            if (!head)
                goto failed;
            if (spine && !root && !computed_data(k, head)) {
                frame->node = k->nodes[spine];
                frame->folded = true;
                frame->phase = NORMAL_CHILDREN;
                break;
            }
            /* A stuck elimination that its last step rebuilt in place, its
             * stuck value reduced, is taken as that step's term, so that a
             * definition stuck inside it folds as written there. Any other
             * head is taken as computed: a transport's formal composition, a
             * composition with its empty tubes dropped, or an eliminator a
             * step computed, as f(x) does where f is an eliminator by eta, or
             * a match that computes f. */
            bool rebuilt = fold && last && stuck_elimination(k, head) && rebuilt_in_place(k, last, head);
            frame->node = k->nodes[rebuilt ? last : head];
            if (!normal_restrict(k, &frame->node))
                goto failed;
            frame->phase = NORMAL_CHILDREN;
            break;
        }
        case NORMAL_CHILD_DONE:
            frame->node.child[frame->next++] = result;
            frame->phase = NORMAL_CHILDREN;
            /* fall through */
        case NORMAL_CHILDREN: {
            while (frame->next < ck_arity(frame->node.kind) && !frame->node.child[frame->next])
                ++frame->next;
            if (frame->next < ck_arity(frame->node.kind)) {
                frame->phase = NORMAL_CHILD_DONE;
                bool spine = (frame->folded || frame->spine) && frame->next == 0 && spine_node(frame->node.kind);
                normal_push(k, &stack, frame->node.child[frame->next], spine);
                break;
            }
            cc_node n = frame->node;
            frame->rebuilt = ck_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], n.child[3]);
            if (!frame->rebuilt)
                goto failed;
            if (frame->folded || frame->spine) {
                result = frame->rebuilt;
                goto complete;
            }
            frame->value = frame->rebuilt;
            frame->phase = NORMAL_REDUCE;
            if (n.kind == CC_GLUE_TERM) {
                cc_term projected = ck_whnf(k, n.child[1]);
                if (!projected)
                    goto failed;
                cc_node projection = k->nodes[projected];
                if (projection.kind == CC_UNGLUE && ck_alpha_equal(k, n.child[0], projection.child[0])) {
                    frame->value = projection.child[1];
                    frame->system = n.child[2];
                    frame->phase = NORMAL_GLUE;
                }
            }
            break;
        }
        case NORMAL_GLUE_DONE:
            /* Restricting the projected value can create redexes. Compare
             * the completed normal form, never its intermediate weak head.
             * These are syntax side conditions, not conversion calls. */
            if (!ck_alpha_equal(k, k->nodes[frame->system].child[0], result)) {
                frame->value = frame->rebuilt;
                frame->phase = NORMAL_REDUCE;
                break;
            }
            frame->phase = NORMAL_GLUE;
            /* fall through */
        case NORMAL_GLUE: {
            if (!frame->system) {
                frame->phase = NORMAL_REDUCE;
                break;
            }
            cc_node piece = k->nodes[frame->system];
            const cc_formula *face = cc_kernel_get_formula(k, piece.payload);
            if (!face || face->sort != CC_FACE) {
                ck_fail(k, "Unchecked Glue face reached reduction.");
                goto failed;
            }
            if (frame->clause == face->length) {
                frame->system = piece.child[1];
                frame->clause = 0;
                break;
            }
            /* Copy the clause before restriction can grow the formula arena;
             * look the immutable face up again on the next continuation. */
            cc_clause clause = face->clauses[frame->clause++];
            cc_term restricted = ck_restrict(k, frame->value, clause);
            if (!restricted)
                goto failed;
            frame->phase = NORMAL_GLUE_DONE;
            normal_push(k, &stack, restricted, false);
            break;
        }
        case NORMAL_REDUCE:
            /* Folding, the parts are final and only eta contracts the whole:
             * a weak head would unfold the definitions folded inside it. */
            if (fold) {
                cc_term next = 0, kind = k->nodes[frame->value].kind;
                if (frame->value == frame->rebuilt && (kind == CC_LAM || kind == CC_PLAM || kind == CC_LLAM || kind == CC_PAIR)) {
                    weak(k, frame->value, &next);
                    if (k->error[0])
                        goto failed;
                } else if (frame->value != frame->rebuilt) {
                    next = frame->value;
                }
                if (!next) {
                    result = frame->rebuilt;
                    goto complete;
                }
                frame->phase = NORMAL_REDUCED;
                normal_push(k, &stack, next, false);
                break;
            }
            result = ck_whnf(k, frame->value);
            if (!result)
                goto failed;
            if (result != frame->rebuilt) {
                /* With interning off, a stuck weak head may be a fresh copy.
                 * Only a structural change warrants another full pass. */
                if (!ck_alpha_equal(k, result, frame->rebuilt)) {
                    if (k->error[0])
                        goto failed;
                    frame->phase = NORMAL_REDUCED;
                    normal_push(k, &stack, result, false);
                    break;
                }
                result = frame->rebuilt;
            }
            /* fall through */
        case NORMAL_REDUCED:
        complete:
            if (!result || k->error[0])
                goto failed;
            /* Completed siblings survive a later failure. Never publish a
             * partially rebuilt parent or an unfinished Glue side condition.
             * A spine's part is no normal form of its own. */
            if (!frame->spine && !(fold && stack.count == 1))
                CACHE[frame->term] = result;
            --stack.count;
            break;
        }
    }
    if (k->error[0])
        result = 0;
    goto cleanup;
failed:
    result = 0;
cleanup:
    if (stack.frames != stack.local)
        free(stack.frames);
    --k->recursion;
    return result;
#undef CACHE
}

cc_term ck_normal(cc_kernel *k, cc_term term) {
    return normal(k, term, false);
}

cc_term ck_normal_folded(cc_kernel *k, cc_term term) {
    return normal(k, term, true);
}

/* Heads whose normal form may still contract by eta once their parts are
 * normal: there, parts that differ do not show that the wholes do. */
static bool eta_sensitive(cc_term_kind kind) {
    return kind == CC_LAM || kind == CC_LLAM || kind == CC_PLAM || kind == CC_PAIR || kind == CC_GLUE_TERM;
}

static bool parts_agree(cc_kernel *k, cc_term a, cc_term b);

/* Whether two terms agree by syntax, reduced only as far as that takes: as
 * they are, as weak heads, part by part under a common head (the same kind
 * and payload, so the same binder), or else as normal forms. Parts already
 * equal, such as a large shared graph on both sides, are never normalized,
 * and each pair is compared once: the result is memoized, as the terms are
 * immutable. Every answer is reduction and syntax, never conversion. */
static bool normal_agree(cc_kernel *k, cc_term a, cc_term b) {
    if (!a || !b)
        return false;
    if (a == b)
        return true;
    uint64_t cached;
    if (ck_memo_get(k, 5, a, 0, b, &cached))
        return cached != 0;
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail_as(k, CC_ERROR_RESOURCE, "Native reduction recursion depth exceeded.");
    }
    bool agrees = parts_agree(k, a, b);
    --k->recursion;
    if (!k->error[0])
        ck_memo_put(k, 5, a, 0, b, agrees);
    return agrees && !k->error[0];
}

static bool parts_agree(cc_kernel *k, cc_term a, cc_term b) {
    if (ck_alpha_equal(k, a, b))
        return true;
    cc_term left = k->error[0] ? 0 : ck_whnf(k, a), right = left ? ck_whnf(k, b) : 0;
    if (!right)
        return false;
    if (ck_alpha_equal(k, left, right))
        return true;
    cc_node x = k->nodes[left], y = k->nodes[right];
    if (x.kind == y.kind && x.payload == y.payload) {
        bool parts = true;
        for (unsigned i = 0; i < ck_arity(x.kind) && parts; ++i)
            parts = x.child[i] == y.child[i] || normal_agree(k, x.child[i], y.child[i]);
        if (parts || k->error[0] || !eta_sensitive(x.kind))
            return parts;
    }
    if (k->error[0])
        return false;
    left = ck_normal(k, left);
    right = left ? ck_normal(k, right) : 0;
    return right && ck_alpha_equal(k, left, right);
}

static cc_term glue_step(cc_kernel *k, cc_term term);

/* The Glue step (CC_STEP_GLUE): glue [φ ↦ t] (unglue b) is b when the two
 * Glue types agree and t is b on φ. The unglue is the base's weak head, or,
 * where that is a Glue term, what its own Glue step exposes, as conversion
 * exposes it: nesting can be deeper than syntax, through definitions, so it
 * counts toward the reduction depth. Each side condition is compared by
 * syntax, its two sides reduced only as far as that takes (normal_agree),
 * and nothing else is reduced: the Glue types, and t and b restricted to
 * each clause of φ, since restricting can make a new redex, as p @ i at
 * i = 0 is p's left endpoint. b stays as it is, with whatever its
 * annotations carry. Weak heads and normal forms are reduction, so
 * conversion still decides no step. Returns b, the term itself when a side
 * condition fails, or 0 on error. */
cc_term ck_glue_step(cc_kernel *k, cc_term term) {
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail_as(k, CC_ERROR_RESOURCE, "Native reduction recursion depth exceeded."), 0;
    }
    cc_term result = glue_step(k, term);
    --k->recursion;
    return result;
}

static cc_term glue_step(cc_kernel *k, cc_term term) {
    cc_node n = k->nodes[term];
    cc_term projected = ck_whnf(k, n.child[1]);
    while (projected && k->nodes[projected].kind == CC_GLUE_TERM) {
        cc_term inner = ck_glue_step(k, projected);
        if (!inner)
            return 0;
        if (inner == projected)
            break;
        projected = ck_whnf(k, inner);
    }
    if (!projected)
        return 0;
    cc_node projection = k->nodes[projected];
    if (projection.kind != CC_UNGLUE)
        return term;
    if (!normal_agree(k, n.child[0], projection.child[0]))
        return k->error[0] ? 0 : term;
    for (cc_term system = n.child[2]; system; system = k->nodes[system].child[1]) {
        cc_node piece = k->nodes[system];
        const cc_formula *raw = cc_kernel_get_formula(k, piece.payload);
        cc_formula face;
        cc_init(&face, CC_FACE);
        if (!ck_formula_result(k, raw ? cc_copy(&face, raw) : CC_BAD_INPUT, "Glue eta face allocation failed.")) {
            cc_clear(&face);
            return 0;
        }
        bool agrees = true;
        for (size_t i = 0; i < face.length && agrees; ++i)
            agrees = normal_agree(k, ck_restrict(k, piece.child[0], face.clauses[i]),
                                  ck_restrict(k, projection.child[1], face.clauses[i]));
        cc_clear(&face);
        if (k->error[0])
            return 0;
        if (!agrees)
            return term;
    }
    return projection.child[1];
}
