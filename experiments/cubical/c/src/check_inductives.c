/* Inductive rules retain their actual dependent motives. In particular W's
 * induction hypothesis is a FUNCTION providing a result for each child, not a
 * result for one selected child and not an assumption about the whole tree. */
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
    if (n.kind == CC_NAT || n.kind == CC_UNIT || n.kind == CC_VOID) {
        out->expression = ck_make(k, n.kind, 0, 0, 0, 0, 0);
        out->type = ck_make(k, CC_U, 0, 0, 0, 0, 0);
        return !k->error[0];
    }
    if (n.kind == CC_ZERO || n.kind == CC_POINT) {
        out->expression = ck_make(k, n.kind, 0, 0, 0, 0, 0);
        out->type = ck_make(k, n.kind == CC_ZERO ? CC_NAT : CC_UNIT, 0, 0, 0, 0, 0);
        return !k->error[0];
    }
    if (n.kind == CC_SUCC) {
        cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0), value;
        if (!ck_check(k, n.child[0], nat, ctx, dims, &value))
            return false;
        out->expression = ck_make(k, CC_SUCC, 0, value, 0, 0, 0);
        out->type = nat;
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
        out->type = ck_make(k, CC_U, level, 0, 0, 0, 0);
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
    if (n.kind == CC_NATREC) {
        cc_term nat = ck_make(k, CC_NAT, 0, 0, 0, 0, 0);
        cc_term motive, zero, step, value;
        if (!family_on(k, n.child[0], nat, ctx, dims, &motive) ||
            !ck_check(k, n.child[3], nat, ctx, dims, &value))
            return false;
        cc_term zero_value = ck_make(k, CC_ZERO, 0, 0, 0, 0, 0);
        if (!ck_check(k, n.child[1], app(k, motive, zero_value), ctx, dims, &zero))
            return false;
        uint32_t predecessor = ck_fresh_symbol(k), hypothesis = ck_fresh_symbol(k);
        cc_term pred = ck_var(k, predecessor);
        cc_term succ = ck_make(k, CC_SUCC, 0, pred, 0, 0, 0);
        cc_term step_type = ck_make(k, CC_PI, hypothesis, app(k, motive, pred), app(k, motive, succ), 0, 0);
        step_type = ck_make(k, CC_PI, predecessor, nat, step_type, 0, 0);
        if (!ck_check(k, n.child[2], step_type, ctx, dims, &step))
            return false;
        out->expression = ck_make(k, CC_NATREC, 0, motive, zero, step, value);
        out->type = app(k, motive, value);
        return !k->error[0];
    }
    if (n.kind == CC_W) {
        cc_term labels, arities;
        uint32_t label_level, arity_level;
        if (!ck_type(k, n.child[0], ctx, dims, &labels, &label_level))
            return false;
        uint32_t name = ck_fresh_symbol(k);
        cc_term body = ck_substitute(k, n.child[1], n.payload, ck_var(k, name));
        cc_context extended = {name, labels, ctx};
        if (!ck_type(k, body, &extended, dims, &arities, &arity_level))
            return false;
        out->expression = ck_make(k, CC_W, name, labels, arities, 0, 0);
        out->type = ck_make(k, CC_U, label_level > arity_level ? label_level : arity_level, 0, 0, 0, 0);
        return !k->error[0];
    }
    if (n.kind == CC_SUP) {
        cc_term type, label, children;
        uint32_t level;
        if (!ck_type(k, n.child[0], ctx, dims, &type, &level))
            return false;
        cc_term normal = ck_whnf(k, type);
        if (!normal || k->nodes[normal].kind != CC_W)
            return ck_fail(k, "sup requires a W-type.");
        cc_node w = k->nodes[normal];
        if (!ck_check(k, n.child[1], w.child[0], ctx, dims, &label))
            return false;
        cc_term arity = ck_substitute(k, w.child[1], w.payload, label);
        cc_term child_type = ck_make(k, CC_PI, ck_fresh_symbol(k), arity, type, 0, 0);
        if (!ck_check(k, n.child[2], child_type, ctx, dims, &children))
            return false;
        out->expression = ck_make(k, CC_SUP, 0, type, label, children, 0);
        out->type = type;
        return !k->error[0];
    }
    if (n.kind == CC_WREC) {
        cc_judgement value;
        if (!ck_infer(k, n.child[2], ctx, dims, &value))
            return false;
        cc_term type = ck_whnf(k, value.type);
        if (!type || k->nodes[type].kind != CC_W)
            return ck_fail(k, "W induction requires a W-tree.");
        cc_node w = k->nodes[type];
        cc_term motive, step;
        if (!family_on(k, n.child[0], type, ctx, dims, &motive))
            return false;
        uint32_t label_name = ck_fresh_symbol(k), child_name = ck_fresh_symbol(k);
        uint32_t index_name = ck_fresh_symbol(k), hypothesis_name = ck_fresh_symbol(k);
        cc_term label = ck_var(k, label_name), children = ck_var(k, child_name);
        cc_term index = ck_var(k, index_name);
        cc_term arity = ck_substitute(k, w.child[1], w.payload, label);
        cc_term child_type = ck_make(k, CC_PI, index_name, arity, type, 0, 0);
        cc_term hypothesis_type = ck_make(k, CC_PI, index_name, arity, app(k, motive, app(k, children, index)), 0, 0);
        cc_term tree = ck_make(k, CC_SUP, 0, type, label, children, 0);
        cc_term step_type = ck_make(k, CC_PI, hypothesis_name, hypothesis_type, app(k, motive, tree), 0, 0);
        step_type = ck_make(k, CC_PI, child_name, child_type, step_type, 0, 0);
        step_type = ck_make(k, CC_PI, label_name, w.child[0], step_type, 0, 0);
        if (!ck_check(k, n.child[1], step_type, ctx, dims, &step))
            return false;
        out->expression = ck_make(k, CC_WREC, 0, motive, step, value.expression, 0);
        out->type = app(k, motive, value.expression);
        return !k->error[0];
    }
    return ck_fail(k, "Unsupported inductive rule.");
}
