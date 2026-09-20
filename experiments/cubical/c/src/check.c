/* Checked entry point. A syntax handle is not a proof. Each assumption is
 * checked before extending the telescope, and every subterm is inferred before
 * conversion. Failures clear the public result and never invoke another kernel. */
#include "term_internal.h"

bool ck_type(cc_kernel *k, cc_term raw, const cc_context *ctx, uint64_t dims,
              cc_term *type, uint32_t *level) {
    cc_judgement checked;
    if (!ck_infer(k, raw, ctx, dims, &checked))
        return false;
    cc_term sort = ck_whnf(k, checked.type);
    if (!sort || k->nodes[sort].kind != CC_U)
        return ck_fail(k, "Expected a universe-valued type.");
    *type = checked.expression;
    *level = k->nodes[sort].payload;
    return true;
}

bool ck_check(cc_kernel *k, cc_term raw, cc_term expected, const cc_context *ctx,
               uint64_t dims, cc_term *term) {
    cc_judgement checked;
    if (!ck_infer(k, raw, ctx, dims, &checked) || !ck_expect(k, checked.type, expected))
        return false;
    *term = checked.expression;
    return true;
}

static bool infer(cc_kernel *k, cc_term raw, const cc_context *ctx, uint64_t dims,
                    cc_judgement *result) {
    if (!raw || raw >= k->count)
        return ck_fail(k, "Invalid term handle.");
    cc_node n = k->nodes[raw];
    switch (n.kind) {
    case CC_U:
        if (n.payload == UINT32_MAX)
            return ck_fail(k, "Universe successor overflow.");
        result->expression = raw;
        result->type = ck_make(k, CC_U, n.payload + 1, 0, 0, 0, 0);
        return result->type != 0;
    case CC_DEFREF:
        if (!n.payload || n.payload >= k->definition_count)
            return ck_fail(k, "Unknown checked definition reference.");
        result->expression = raw;
        result->type = k->definitions[n.payload].type;
        return true;
    case CC_VAR:
        for (; ctx; ctx = ctx->previous)
            if (ctx->name == n.payload) {
                result->expression = raw;
                result->type = ctx->type;
                return true;
            }
        return ck_fail(k, "Unbound term variable.");
    case CC_PI: case CC_LAM: case CC_APP: case CC_SIGMA: case CC_PAIR: case CC_FST: case CC_SND:
        return ck_functions(k, n, ctx, dims, result);
    case CC_NAT: case CC_ZERO: case CC_SUCC: case CC_NATREC: case CC_UNIT: case CC_POINT:
    case CC_VOID: case CC_ABORT: case CC_W: case CC_SUP: case CC_WREC:
    case CC_SUM: case CC_INL: case CC_INR: case CC_SUMREC: case CC_UNITREC:
        return ck_inductives(k, n, ctx, dims, result);
    case CC_PATH: case CC_PLAM: case CC_PAPP:
        return ck_paths(k, n, ctx, dims, result);
    case CC_COMP:
        return ck_composition(k, n, ctx, dims, result);
    case CC_GLUE: case CC_GLUE_TERM: case CC_UNGLUE:
        return ck_glue(k, n, ctx, dims, result);
    case CC_PUSHOUT: case CC_PUSH_LEFT: case CC_PUSH_RIGHT: case CC_PUSH_PATH: case CC_PUSH_ELIM:
        return ck_pushout(k, n, ctx, dims, result);
    case CC_GLUE_SYSTEM:
    case CC_TUBE:
        return ck_fail(k, "A partial tube is not a standalone term.");
    }
    return ck_fail(k, "Unsupported term constructor.");
}

bool ck_infer(cc_kernel *k, cc_term raw, const cc_context *ctx, uint64_t dims,
               cc_judgement *result) {
    if (!ck_tick(k, true))
        return false;
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail(k, "Native reference recursion depth exceeded.");
    }
    bool success = infer(k, raw, ctx, dims, result);
    --k->recursion;
    return success && !k->error[0];
}

bool cc_kernel_check_in_cube(cc_kernel *k, cc_term raw, cc_term expected,
                              const cc_assumption *assumptions, size_t count,
                              uint64_t dimensions, cc_checked_result *result) {
    if (!k || !result)
        return false;
    memset(result, 0, sizeof *result);
    k->error[0] = '\0';
    k->checking_steps = 0;
    k->reduction_steps = 0;
    k->budget = UINT64_C(10000000);
    k->recursion = 0;
    if ((count && !assumptions) || count > SIZE_MAX / sizeof(cc_context))
        return ck_fail(k, "Invalid assumption telescope.");
    cc_context *entries = count ? calloc(count, sizeof *entries) : NULL;
    if (count && !entries)
        return ck_fail(k, "Context allocation failed.");
    const cc_context *ctx = NULL;
    bool success = true;
    for (size_t i = 0; i < count && success; ++i) {
        for (size_t j = 0; j < i; ++j)
            if (assumptions[i].symbol == assumptions[j].symbol)
                success = ck_fail(k, "Duplicate context variable.");
        if (!success)
            break;
        uint32_t level;
        cc_term type;
        success = ck_type(k, assumptions[i].type, ctx, dimensions, &type, &level);
        if (!success)
            break;
        if (assumptions[i].symbol >= k->next_symbol) {
            if (assumptions[i].symbol == UINT32_MAX) {
                success = ck_fail(k, "Context symbol overflow.");
                break;
            }
            k->next_symbol = assumptions[i].symbol + 1;
        }
        entries[i] = (cc_context){assumptions[i].symbol, type, ctx};
        ctx = &entries[i];
    }
    cc_judgement checked;
    if (success)
        success = ck_infer(k, raw, ctx, dimensions, &checked);
    if (success && expected) {
        uint32_t level;
        cc_term checked_type;
        success = ck_type(k, expected, ctx, dimensions, &checked_type, &level) &&
                  ck_expect(k, checked.type, checked_type);
    }
    if (success) {
        result->expression = checked.expression;
        result->type = checked.type;
        result->normal = 0; /* Normalization is an explicit inspector operation. */
        result->arena_nodes = k->count - 1;
        result->arena_bytes = k->capacity * (sizeof(cc_node) + sizeof(cc_term)) +
                              k->definition_capacity * sizeof(cc_definition) +
                              (k->syntax_memo ? CC_SYNTAX_MEMO_SIZE * sizeof(cc_syntax_memo) : 0) +
                              (k->alpha_memo ? CC_ALPHA_MEMO_SIZE * sizeof(cc_alpha_memo) : 0);
        result->checking_steps = k->checking_steps;
        result->reduction_steps = k->reduction_steps;
        success = !k->error[0];
    }
    free(entries);
    if (!success)
        memset(result, 0, sizeof *result);
    return success;
}

bool cc_kernel_check(cc_kernel *k, cc_term raw, cc_term expected,
                      const cc_assumption *assumptions, size_t count,
                      cc_checked_result *result) {
    return cc_kernel_check_in_cube(k, raw, expected, assumptions, count, 0, result);
}

cc_term cc_kernel_normalize(cc_kernel *k, cc_term term) {
    if (!k || !term || term >= k->count || k->error[0])
        return 0;
    k->budget = UINT64_C(10000000);
    return ck_normal(k, term);
}
