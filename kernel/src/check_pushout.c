/* Computational pushouts, CHM "On Higher Inductive Types" §3.3.5.
 * The span C -> A, C -> B is an ordinary checked pair of functions.
 * The bridge case is a DEPENDENT path; its two endpoints are checked against
 * the point cases, so no user-supplied path or eliminator is postulated. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

cc_term ck_pushout_bridge_type(cc_kernel *k, cc_term P, cc_term motive,
                               cc_term left, cc_term right, cc_term c) {
    cc_term head = ck_whnf(k, P);
    if (!head || k->nodes[head].kind != CC_PUSHOUT)
        return ck_fail(k, "Expected a pushout type."), 0;
    cc_node span = k->nodes[head];
    uint64_t avoid = ck_free_dims(k, P) | ck_free_dims(k, motive) |
                     ck_free_dims(k, left) | ck_free_dims(k, right) | ck_free_dims(k, c);
    unsigned dim = ck_fresh_dimension(k, avoid);
    cc_term point = ck_make(k, CC_PUSH_PATH, ck_interval_variable(k, dim), P, c, 0, 0);
    cc_term f = ck_make(k, CC_FST, 0, span.child[3], 0, 0, 0);
    cc_term g = ck_make(k, CC_SND, 0, span.child[3], 0, 0, 0);
    return ck_make(k, CC_PATH, dim, app(k, motive, point),
                   app(k, left, app(k, f, c)), app(k, right, app(k, g, c)), 0);
}

bool ck_pushout(cc_kernel *k, cc_node n, const cc_context *ctx, uint64_t dims,
                 cc_judgement *out) {
    if (n.kind == CC_PUSHOUT) {
        cc_term C, A, B, maps;
        uint32_t lc, la, lb;
        if (!ck_type(k, n.child[0], ctx, dims, &C, &lc) ||
            !ck_type(k, n.child[1], ctx, dims, &A, &la) ||
            !ck_type(k, n.child[2], ctx, dims, &B, &lb))
            return false;
        uint32_t x = ck_fresh_symbol(k);
        uint32_t f = ck_fresh_symbol(k);
        cc_term to_left = ck_make(k, CC_PI, x, C, A, 0, 0);
        cc_term to_right = ck_make(k, CC_PI, x, C, B, 0, 0);
        cc_term pair_type = ck_make(k, CC_SIGMA, f, to_left, to_right, 0, 0);
        if (!ck_check(k, n.child[3], pair_type, ctx, dims, &maps))
            return false;
        uint32_t level = lc > la ? lc : la;
        if (lb > level)
            level = lb;
        out->expression = ck_make(k, CC_PUSHOUT, 0, C, A, B, maps);
        out->type = ck_make(k, CC_U, level, 0, 0, 0, 0);
        return !k->error[0];
    }
    if (n.kind == CC_PUSH_ELIM) {
        cc_judgement motive;
        if (!ck_infer(k, n.child[0], ctx, dims, &motive))
            return false;
        cc_term mt = ck_whnf(k, motive.type);
        if (!mt || k->nodes[mt].kind != CC_PI)
            return ck_fail(k, "Expected a pushout type family.");
        cc_node family = k->nodes[mt];
        cc_term P = ck_whnf(k, family.child[0]);
        cc_term sort = ck_whnf(k, family.child[1]);
        if (!P || k->nodes[P].kind != CC_PUSHOUT || !sort || k->nodes[sort].kind != CC_U)
            return ck_fail(k, "Expected a pushout type family.");
        cc_node span = k->nodes[P];
        uint32_t a = ck_fresh_symbol(k);
        uint32_t b = ck_fresh_symbol(k);
        uint32_t c = ck_fresh_symbol(k);
        uint32_t z = ck_fresh_symbol(k);
        cc_term lp = ck_make(k, CC_PUSH_LEFT, 0, P, ck_var(k, a), 0, 0);
        cc_term rp = ck_make(k, CC_PUSH_RIGHT, 0, P, ck_var(k, b), 0, 0);
        cc_term lt = ck_make(k, CC_PI, a, span.child[1], app(k, motive.expression, lp), 0, 0);
        cc_term rt = ck_make(k, CC_PI, b, span.child[2], app(k, motive.expression, rp), 0, 0);
        cc_term left, right, bridge;
        if (!ck_check(k, n.child[1], lt, ctx, dims, &left) ||
            !ck_check(k, n.child[2], rt, ctx, dims, &right))
            return false;
        cc_term path = ck_pushout_bridge_type(k, P, motive.expression, left, right, ck_var(k, c));
        cc_term bt = ck_make(k, CC_PI, c, span.child[0], path, 0, 0);
        if (!ck_check(k, n.child[3], bt, ctx, dims, &bridge))
            return false;
        out->expression = ck_make(k, CC_PUSH_ELIM, 0, motive.expression, left, right, bridge);
        out->type = ck_make(k, CC_PI, z, P, app(k, motive.expression, ck_var(k, z)), 0, 0);
        return !k->error[0];
    }
    cc_term P, value;
    uint32_t level;
    if (!ck_type(k, n.child[0], ctx, dims, &P, &level))
        return false;
    cc_term head = ck_whnf(k, P);
    if (!head || k->nodes[head].kind != CC_PUSHOUT)
        return ck_fail(k, "Expected a pushout type.");
    cc_node span = k->nodes[head];
    unsigned slot = n.kind == CC_PUSH_PATH ? 0 : n.kind == CC_PUSH_LEFT ? 1 : 2;
    if (!ck_check(k, n.child[1], span.child[slot], ctx, dims, &value))
        return false;
    if (n.kind == CC_PUSH_PATH) {
        const cc_formula *arg = cc_kernel_get_formula(k, n.payload);
        if (!arg || arg->sort != CC_INTERVAL)
            return ck_fail(k, "Pushout bridge requires an interval expression.");
        for (size_t i = 0; i < arg->length; ++i)
            if ((arg->clauses[i].positive | arg->clauses[i].negative) & ~dims)
                return ck_fail(k, "Pushout bridge uses an unbound dimension.");
    }
    out->expression = ck_make(k, n.kind, n.payload, P, value, 0, 0);
    out->type = P;
    return !k->error[0];
}
