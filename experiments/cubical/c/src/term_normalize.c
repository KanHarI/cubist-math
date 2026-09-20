/* Call-by-name weak-head reduction is the conversion engine's workhorse.
 * Application first exposes its FUNCTION, not its argument. Induction first
 * exposes the SCRUTINEE, not every branch or recursive hypothesis. Therefore a
 * branch that ignores its recursive hypothesis does not evaluate that subtree.
 * Full normalization is only requested for an explicit inspection result. */
#include "term_internal.h"

static cc_term app(cc_kernel *k, cc_term f, cc_term x) {
    return ck_make(k, CC_APP, 0, f, x, 0, 0);
}

static cc_term weak(cc_kernel *k, cc_term term) {
    cc_node n = k->nodes[term];
    if (n.kind == CC_APP) {
        cc_term fn = ck_whnf(k, n.child[0]);
        if (!fn)
            return 0;
        cc_node head = k->nodes[fn];
        if (head.kind == CC_LAM)
            return ck_whnf(k, ck_substitute(k, head.child[1], head.payload, n.child[1]));
        return fn == n.child[0] ? term : app(k, fn, n.child[1]);
    }
    if (n.kind == CC_FST || n.kind == CC_SND) {
        cc_term pair = ck_whnf(k, n.child[0]);
        if (!pair)
            return 0;
        cc_node head = k->nodes[pair];
        if (head.kind == CC_PAIR)
            return ck_whnf(k, head.child[n.kind == CC_FST ? 1 : 2]);
        return pair == n.child[0] ? term : ck_make(k, n.kind, 0, pair, 0, 0, 0);
    }
    if (n.kind == CC_NATREC) {
        cc_term value = ck_whnf(k, n.child[3]);
        if (!value)
            return 0;
        cc_node head = k->nodes[value];
        if (head.kind == CC_ZERO)
            return ck_whnf(k, n.child[1]);
        if (head.kind == CC_SUCC) {
            cc_term recursive = ck_make(k, CC_NATREC, 0, n.child[0], n.child[1], n.child[2], head.child[0]);
            return ck_whnf(k, app(k, app(k, n.child[2], head.child[0]), recursive));
        }
        return value == n.child[3] ? term : ck_make(k, CC_NATREC, 0, n.child[0], n.child[1], n.child[2], value);
    }
    if (n.kind == CC_SUMREC) {
        cc_term value = ck_whnf(k, n.child[3]);
        if (!value)
            return 0;
        cc_node head = k->nodes[value];
        if (head.kind == CC_INL || head.kind == CC_INR)
            return ck_whnf(k, app(k, n.child[head.kind == CC_INL ? 1 : 2], head.child[1]));
        return value == n.child[3] ? term : ck_make(k, CC_SUMREC, 0, n.child[0], n.child[1], n.child[2], value);
    }
    if (n.kind == CC_UNITREC) {
        cc_term value = ck_whnf(k, n.child[2]);
        if (!value)
            return 0;
        if (k->nodes[value].kind == CC_POINT)
            return ck_whnf(k, n.child[1]);
        return value == n.child[2] ? term : ck_make(k, CC_UNITREC, 0, n.child[0], n.child[1], value, 0);
    }
    if (n.kind == CC_WREC) {
        cc_term value = ck_whnf(k, n.child[2]);
        if (!value)
            return 0;
        cc_node head = k->nodes[value];
        if (head.kind == CC_SUP) {
            cc_term type = ck_whnf(k, head.child[0]);
            if (!type || k->nodes[type].kind != CC_W)
                return ck_fail(k, "Malformed checked W constructor."), 0;
            cc_node w = k->nodes[type];
            uint32_t name = ck_fresh_symbol(k);
            cc_term index = ck_var(k, name);
            cc_term arity = ck_substitute(k, w.child[1], w.payload, head.child[1]);
            cc_term child = app(k, head.child[2], index);
            cc_term recursive = ck_make(k, CC_WREC, 0, n.child[0], n.child[1], child, 0);
            cc_term hypothesis = ck_make(k, CC_LAM, name, arity, recursive, 0, 0);
            return ck_whnf(k, app(k, app(k, app(k, n.child[1], head.child[1]), head.child[2]), hypothesis));
        }
        return value == n.child[2] ? term : ck_make(k, CC_WREC, 0, n.child[0], n.child[1], value, 0);
    }
    if (n.kind == CC_PAPP) {
        const cc_formula *arg = cc_kernel_get_formula(k, n.payload);
        if (!arg || arg->sort != CC_INTERVAL || !n.child[1] || k->nodes[n.child[1]].kind != CC_PATH)
            return ck_fail(k, "Unchecked path application reached reduction."), 0;
        cc_node type = k->nodes[n.child[1]];
        if (!arg->length)
            return ck_whnf(k, type.child[1]);
        if (arg->length == 1 && !arg->clauses[0].positive && !arg->clauses[0].negative)
            return ck_whnf(k, type.child[2]);
        cc_formula argument;
        cc_init(&argument, CC_INTERVAL);
        if (cc_copy(&argument, arg) != CC_OK)
            return ck_fail(k, "Interval copy failed."), 0;
        cc_term path = ck_whnf(k, n.child[0]);
        cc_term result = 0;
        if (path && k->nodes[path].kind == CC_PLAM) {
            cc_node line = k->nodes[path];
            result = ck_whnf(k, ck_dimension_substitute(k, line.child[1], line.payload, &argument));
        } else if (path) {
            result = path == n.child[0] ? term : ck_make(k, CC_PAPP, n.payload, path, n.child[1], 0, 0);
        }
        cc_clear(&argument);
        return result;
    }
    if (n.kind == CC_LAM || n.kind == CC_PLAM) {
        cc_term body = ck_whnf(k, n.child[1]);
        if (!body)
            return 0;
        cc_node head = k->nodes[body];
        if (n.kind == CC_LAM && head.kind == CC_APP) {
            cc_node argument = k->nodes[head.child[1]];
            if (argument.kind == CC_VAR && argument.payload == n.payload && !ck_term_free(k, head.child[0], n.payload))
                return ck_whnf(k, head.child[0]);
        }
        if (n.kind == CC_PLAM && head.kind == CC_PAPP) {
            const cc_formula *arg = cc_kernel_get_formula(k, head.payload);
            if (arg && n.payload < CC_DIMENSIONS && arg->length == 1 && !arg->clauses[0].negative &&
                arg->clauses[0].positive == (UINT64_C(1) << n.payload) &&
                !(ck_free_dims(k, head.child[0]) & (UINT64_C(1) << n.payload)))
                return ck_whnf(k, head.child[0]);
        }
        return body == n.child[1] ? term : ck_make(k, n.kind, n.payload, n.child[0], body, 0, 0);
    }
    if (n.kind == CC_COMP)
        return ck_reduce_composition(k, term);
    return term;
}

cc_term ck_whnf(cc_kernel *k, cc_term term) {
    if (!term || term >= k->count || !ck_tick(k, false))
        return 0;
    if (k->weak_cache[term])
        return k->weak_cache[term];
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail(k, "Native reduction recursion depth exceeded."), 0;
    }
    cc_term result = weak(k, term);
    --k->recursion;
    if (result && !k->error[0])
        k->weak_cache[term] = result;
    return result;
}

cc_term ck_normal(cc_kernel *k, cc_term term) {
    cc_term head = ck_whnf(k, term);
    if (!head)
        return 0;
    if (++k->recursion > 1024) {
        --k->recursion;
        return ck_fail(k, "Native normal-form depth exceeded."), 0;
    }
    cc_node n = k->nodes[head];
    for (unsigned i = 0; i < ck_arity(n.kind); ++i)
        if (n.child[i])
            n.child[i] = ck_normal(k, n.child[i]);
    cc_term result = ck_make(k, n.kind, n.payload, n.child[0], n.child[1], n.child[2], n.child[3]);
    if (result)
        result = ck_whnf(k, result);
    --k->recursion;
    return result;
}
