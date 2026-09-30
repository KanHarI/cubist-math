/* The remaining fixed inductive rules retain their dependent motives. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

static bool family_on(cc_kernel *k, cc_term raw, cc_term domain,
                       const cc_context *ctx, uint64_t dims, cc_term *family) {
    cc_judgement f;
    if (!ck_infer(k, raw, ctx, dims, &f))
        return false;
    cc_term type = ck_whnf(k, f.type);
    if (!type || k->nodes[type].kind != CC_PI)
        return ck_fail(k, "Expected an inductive type family.");
    cc_node pi = k->nodes[type];
    cc_term range = ck_whnf(k, pi.child[1]);
    if (!ck_convertible(k, pi.child[0], domain) || !range || k->nodes[range].kind != CC_U)
        return ck_fail(k, "Induction motive has the wrong domain or sort.");
    *family = f.expression;
    return true;
}

bool ck_inductives(cc_kernel *k, cc_node n, const cc_context *ctx, uint64_t dims,
                    cc_judgement *out) {
    if (n.kind == CC_UNIT || n.kind == CC_VOID) {
        out->expression = ck_make(k, n.kind, 0, 0, 0, 0, 0);
        out->type = ck_universe_at(k, 0);
        return !k->error[0];
    }
    if (n.kind == CC_POINT) {
        out->expression = ck_make(k, n.kind, 0, 0, 0, 0, 0);
        out->type = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
        return !k->error[0];
    }

    if (n.kind == CC_ABORT) {
        cc_term type, impossible;
        uint32_t level;
        cc_term empty = ck_make(k, CC_VOID, 0, 0, 0, 0, 0);
        if (!ck_type(k, n.child[0], ctx, dims, &type, &level) ||
            !ck_check(k, n.child[1], empty, ctx, dims, &impossible))
            return false;
        out->expression = ck_make(k, CC_ABORT, 0, type, impossible, 0, 0);
        out->type = type;
        return !k->error[0];
    }
    if (n.kind == CC_SUM) {
        cc_term left, right;
        uint32_t left_level, right_level;
        if (!ck_type(k, n.child[0], ctx, dims, &left, &left_level) ||
            !ck_type(k, n.child[1], ctx, dims, &right, &right_level))
            return false;
        out->expression = ck_make(k, CC_SUM, 0, left, right, 0, 0);
        uint32_t level = left_level > right_level ? left_level : right_level;
        out->type = ck_universe_at(k, level);
        return !k->error[0];
    }
    if (n.kind == CC_INL || n.kind == CC_INR) {
        cc_term type, value;
        uint32_t level;
        if (!ck_type(k, n.child[0], ctx, dims, &type, &level))
            return false;
        cc_term head = ck_whnf(k, type);
        if (!head || k->nodes[head].kind != CC_SUM)
            return ck_fail(k, "A sum injection requires a sum type.");
        cc_term summand = k->nodes[head].child[n.kind == CC_INL ? 0 : 1];
        if (!ck_check(k, n.child[1], summand, ctx, dims, &value))
            return false;
        out->expression = ck_make(k, n.kind, 0, type, value, 0, 0);
        out->type = type;
        return !k->error[0];
    }
    if (n.kind == CC_SUMREC) {
        cc_judgement value;
        if (!ck_infer(k, n.child[3], ctx, dims, &value))
            return false;
        cc_term type = ck_whnf(k, value.type);
        if (!type || k->nodes[type].kind != CC_SUM)
            return ck_fail(k, "Sum induction requires a sum value.");
        cc_node sum = k->nodes[type];
        cc_term motive, branches[2];
        if (!family_on(k, n.child[0], type, ctx, dims, &motive))
            return false;
        for (unsigned side = 0; side < 2; ++side) {
            uint32_t name = ck_fresh_symbol(k);
            cc_term injected = ck_make(k, side ? CC_INR : CC_INL, 0, type, ck_var(k, name), 0, 0);
            cc_term branch_type = ck_make(k, CC_PI, name, sum.child[side], app(k, motive, injected), 0, 0);
            if (!ck_check(k, n.child[side + 1], branch_type, ctx, dims, &branches[side]))
                return false;
        }
        out->expression = ck_make(k, CC_SUMREC, 0, motive, branches[0], branches[1], value.expression);
        out->type = app(k, motive, value.expression);
        return !k->error[0];
    }
    if (n.kind == CC_UNITREC) {
        cc_term unit = ck_make(k, CC_UNIT, 0, 0, 0, 0, 0);
        cc_term point = ck_make(k, CC_POINT, 0, 0, 0, 0, 0);
        cc_term motive, branch, value;
        if (!family_on(k, n.child[0], unit, ctx, dims, &motive) ||
            !ck_check(k, n.child[1], app(k, motive, point), ctx, dims, &branch) ||
            !ck_check(k, n.child[2], unit, ctx, dims, &value))
            return false;
        out->expression = ck_make(k, CC_UNITREC, 0, motive, branch, value, 0);
        out->type = app(k, motive, value);
        return !k->error[0];
    }

    return ck_fail(k, "Unsupported inductive rule.");
}
