/* Interval paths. A dependent family A(i) has endpoints in A(0) and A(1).
 * Application computes at endpoints even when the path itself is neutral.
 * The annotation used for that computation is reconstructed by this checker;
 * an input annotation is never accepted as evidence. */
#include "term_internal.h"

bool ck_paths(cc_kernel *k, cc_node n, const cc_context *ctx, uint64_t dims,
               cc_judgement *out) {
    if (n.kind == CC_PAPP) {
        cc_judgement path;
        if (!ck_infer(k, n.child[0], ctx, dims, &path))
            return false;
        cc_term type = ck_whnf(k, path.type);
        if (!type || k->nodes[type].kind != CC_PATH)
            return ck_fail(k, "Expected an interval path.");
        cc_node pt = k->nodes[type];
        const cc_formula *raw_arg = cc_kernel_get_formula(k, n.payload);
        if (!raw_arg || raw_arg->sort != CC_INTERVAL)
            return ck_fail(k, "Path application requires an interval expression.");
        cc_formula arg;
        cc_init(&arg, CC_INTERVAL);
        if (cc_copy(&arg, raw_arg) != CC_OK)
            return ck_fail(k, "Interval copy failed.");
        for (size_t i = 0; i < arg.length; ++i)
            if ((arg.clauses[i].positive | arg.clauses[i].negative) & ~dims) {
                cc_clear(&arg);
                return ck_fail(k, "Unbound interval dimension.");
            }
        out->type = ck_dimension_substitute(k, pt.child[0], pt.payload, &arg);
        cc_clear(&arg);
        out->expression = ck_make(k, CC_PAPP, n.payload, path.expression, type, 0, 0);
        return !k->error[0];
    }
    if (n.payload >= CC_DIMENSIONS)
        return ck_fail(k, "Dimension binder outside native range.");
    unsigned dim = n.payload;
    if (dims & (UINT64_C(1) << dim)) {
        uint64_t avoid = dims | ck_free_dims(k, n.child[0]);
        if (n.kind == CC_PLAM)
            avoid |= ck_free_dims(k, n.child[1]);
        unsigned fresh = ck_fresh_dimension(k, avoid);
        cc_formula variable;
        cc_init(&variable, CC_INTERVAL);
        if (cc_generator(&variable, fresh, true) != CC_OK)
            return ck_fail(k, "No fresh dimension available.");
        n.child[0] = ck_dimension_substitute(k, n.child[0], dim, &variable);
        if (n.kind == CC_PLAM)
            n.child[1] = ck_dimension_substitute(k, n.child[1], dim, &variable);
        cc_clear(&variable);
        dim = fresh;
    }
    uint64_t inner = dims | (UINT64_C(1) << dim);
    cc_term family;
    uint32_t level;
    if (!ck_type(k, n.child[0], ctx, inner, &family, &level))
        return false;
    if (n.kind == CC_PATH) {
        cc_term left, right;
        cc_term left_type = ck_endpoint_term(k, family, dim, 0);
        cc_term right_type = ck_endpoint_term(k, family, dim, 1);
        if (!ck_check(k, n.child[1], left_type, ctx, dims, &left) ||
            !ck_check(k, n.child[2], right_type, ctx, dims, &right))
            return false;
        out->expression = ck_make(k, CC_PATH, dim, family, left, right, 0);
        out->type = ck_make(k, CC_U, level, 0, 0, 0, 0);
    } else if (n.kind == CC_PLAM) {
        cc_term body;
        if (!ck_check(k, n.child[1], family, ctx, inner, &body))
            return false;
        cc_term left = ck_endpoint_term(k, body, dim, 0);
        cc_term right = ck_endpoint_term(k, body, dim, 1);
        out->expression = ck_make(k, CC_PLAM, dim, family, body, 0, 0);
        out->type = ck_make(k, CC_PATH, dim, family, left, right, 0);
    } else {
        return ck_fail(k, "Unsupported path rule.");
    }
    return !k->error[0];
}
