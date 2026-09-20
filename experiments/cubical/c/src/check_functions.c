/* Pi/Sigma rules. Formation uses max of the two universe levels; lambda
 * introduction discharges one freshly named assumption. Pair elimination
 * substitutes the first projection into the second component's type. */
#include "term_internal.h"

bool ck_functions(cc_kernel *k, cc_node n, const cc_context *ctx, uint64_t dims,
                    cc_judgement *out) {
    if (ck_term_binder(n.kind)) {
        cc_term domain, body;
        uint32_t domain_level, body_level;
        if (!ck_type(k, n.child[0], ctx, dims, &domain, &domain_level))
            return false;
        uint32_t name = ck_fresh_symbol(k);
        cc_term raw_body = ck_substitute(k, n.child[1], n.payload, ck_var(k, name));
        cc_context extended = {name, domain, ctx};
        if (n.kind == CC_LAM) {
            cc_judgement checked;
            if (!ck_infer(k, raw_body, &extended, dims, &checked))
                return false;
            out->expression = ck_make(k, CC_LAM, name, domain, checked.expression, 0, 0);
            out->type = ck_make(k, CC_PI, name, domain, checked.type, 0, 0);
        } else {
            if (!ck_type(k, raw_body, &extended, dims, &body, &body_level))
                return false;
            out->expression = ck_make(k, n.kind, name, domain, body, 0, 0);
            out->type = ck_make(k, CC_U, domain_level > body_level ? domain_level : body_level, 0, 0, 0, 0);
        }
        return !k->error[0];
    }
    if (n.kind == CC_APP) {
        cc_judgement fn;
        if (!ck_infer(k, n.child[0], ctx, dims, &fn))
            return false;
        cc_term type = ck_whnf(k, fn.type);
        if (!type || k->nodes[type].kind != CC_PI)
            return ck_fail(k, "Expected a function.");
        cc_node pi = k->nodes[type];
        cc_term arg;
        if (!ck_check(k, n.child[1], pi.child[0], ctx, dims, &arg))
            return false;
        out->expression = ck_make(k, CC_APP, 0, fn.expression, arg, 0, 0);
        out->type = ck_substitute(k, pi.child[1], pi.payload, arg);
        return !k->error[0];
    }
    if (n.kind == CC_PAIR) {
        cc_term type, first, second;
        uint32_t level;
        if (!ck_type(k, n.child[0], ctx, dims, &type, &level))
            return false;
        cc_term normal = ck_whnf(k, type);
        if (!normal || k->nodes[normal].kind != CC_SIGMA)
            return ck_fail(k, "Expected a dependent pair type.");
        cc_node sigma = k->nodes[normal];
        if (!ck_check(k, n.child[1], sigma.child[0], ctx, dims, &first))
            return false;
        cc_term second_type = ck_substitute(k, sigma.child[1], sigma.payload, first);
        if (!ck_check(k, n.child[2], second_type, ctx, dims, &second))
            return false;
        out->expression = ck_make(k, CC_PAIR, 0, type, first, second, 0);
        out->type = type;
        return !k->error[0];
    }
    if (n.kind == CC_FST || n.kind == CC_SND) {
        cc_judgement pair;
        if (!ck_infer(k, n.child[0], ctx, dims, &pair))
            return false;
        cc_term type = ck_whnf(k, pair.type);
        if (!type || k->nodes[type].kind != CC_SIGMA)
            return ck_fail(k, "Expected a dependent pair.");
        cc_node sigma = k->nodes[type];
        out->expression = ck_make(k, n.kind, 0, pair.expression, 0, 0, 0);
        cc_term first = ck_make(k, CC_FST, 0, pair.expression, 0, 0, 0);
        out->type = n.kind == CC_FST ? sigma.child[0] : ck_substitute(k, sigma.child[1], sigma.payload, first);
        return !k->error[0];
    }
    return ck_fail(k, "Unsupported function/pair rule.");
}
