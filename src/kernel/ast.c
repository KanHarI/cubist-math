#include "internal.h"

/* Compatibility-critical: upstream adds this depth to ALL children of a
 * constructor, including the domain of Pi/Sigma/W. This is not the usual
 * child-specific de Bruijn convention. See README.md and compatibility.md. */
unsigned binders(unsigned k) {
    switch (k) {
    case N_Lambda:
    case N_Pi:
    case N_Sigma:
    case N_W:
    case N_IndEq:
        return 1;
    case N_IndNat:
    case N_IndSigma:
    case N_IndSum:
    case N_IndW:
        return 2;
    default:
        return 0;
    }
}
bool universe(const tt_engine *e, tt_id a) {
    if (!a || a > e->nn)
        return false;
    unsigned k = e->nodes[a].kind;
    return k == N_U || k == N_UUOmega || k == N_UUKappa || k == N_UCRef;
}
tt_id max_universe(tt_engine *e, tt_id a, tt_id b) {
    if (a == b)
        return a;
    node x = e->nodes[a], y = e->nodes[b];
    if (x.kind == N_UUKappa || y.kind == N_UUKappa)
        return leaf(e, N_UUKappa, 0);
    if (x.kind == N_UUOmega || y.kind == N_UUOmega)
        return leaf(e, N_UUOmega, 0);
    if (x.kind == N_U && y.kind == N_U)
        return x.param > y.param ? a : b;
    if (x.kind == N_U && x.param == 0)
        return b;
    if (y.kind == N_U && y.param == 0)
        return a;
    return leaf(e, N_UUOmega, 0);
}

/* Simultaneous immutable substitution. Source nodes are copied before any
 * allocation; unchanged subtrees reuse their IDs. The key includes mode,
 * substitutions, binder depth, and rollback generation. See internal.h for the
 * distinct context, binding, instantiation, shift, and beta-substitution modes. */
tt_id transform(tt_engine *e, tt_id ast, unsigned mode, const tt_id *ctx, const tt_id *values,
                unsigned count, unsigned depth) {
    if (e->error || !ast)
        return 0;
    node n = e->nodes[ast];
    if ((mode == MAP_CONTEXT || mode == MAP_BIND || mode == MAP_W_MOTIVE) &&
        !(n.flags & HAS_CONTEXT))
        return ast;
    if ((mode == MAP_INSTANTIATE || mode == MAP_SHIFT || mode == MAP_BETA_SUBST) &&
        !(n.flags & HAS_VARIABLE))
        return ast;
    map_cache key = {
        .ast = ast, .mode = mode, .depth = depth, .n = count, .generation = e->map_generation};
    for (unsigned i = 0; i < count; i++) {
        key.ctx[i] = ctx ? ctx[i] : 0;
        key.values[i] = values ? values[i] : 0;
    }
    uint64_t h = tt_mix(ast + ((uint64_t)mode << 32) + depth);
    for (unsigned i = 0; i < count; i++)
        h = tt_mix(h ^ key.ctx[i] ^ ((uint64_t)key.values[i] << 32));
    size_t slot = h & (e->map_cap - 1);
    map_cache old = e->maps[slot];
    if (old.result && old.generation == e->map_generation && old.ast == ast && old.mode == mode &&
        old.depth == depth && old.n == count && !memcmp(old.ctx, key.ctx, sizeof(key.ctx)) &&
        !memcmp(old.values, key.values, sizeof(key.values)))
        return old.result;
    tt_id result = ast;
    if ((n.kind == N_CRef || n.kind == N_UCRef) &&
        (mode == MAP_CONTEXT || mode == MAP_BIND || mode == MAP_W_MOTIVE)) {
        for (unsigned i = 0; i < count; i++)
            if (ctx[i] && n.param == ctx[i]) {
                result = mode == MAP_BIND       ? leaf(e, N_VRef, depth + values[i])
                         : mode == MAP_W_MOTIVE ? make2(e, N_Ap, values[i], leaf(e, N_VRef, depth))
                                                : values[i];
                break;
            }
    } else if (n.kind == N_VRef) {
        if (mode == MAP_INSTANTIATE && n.param == depth)
            result = values[0];
        else if (mode == MAP_SHIFT && (int32_t)n.param >= (int32_t)depth) {
            int64_t v = (int64_t)(int32_t)n.param + (int32_t)values[0];
            if (v < INT32_MIN || v > INT32_MAX) {
                e->error = TT_INVALID;
                return 0;
            }
            result = leaf(e, N_VRef, (uint32_t)v);
        } else if (mode == MAP_BETA_SUBST) {
            if (n.param >= depth && n.param < depth + count) {
                tt_id delta = depth + (ctx ? ctx[0] : 0);
                if (values[n.param - depth])
                    result = transform(e, values[n.param - depth], MAP_SHIFT, NULL, &delta, 1, 0);
            } else if (n.param >= depth + count)
                result = leaf(e, N_VRef, n.param - count);
        }
    } else if (n.arity) {
        bool changed = false;
        for (unsigned i = 0; i < n.arity; i++) {
            tt_id r = transform(e, n.ch[i], mode, ctx, values, count, depth + binders(n.kind));
            changed |= r != n.ch[i];
            n.ch[i] = r;
        }
        if (changed)
            result = intern(e, n);
    }
    if (mode == MAP_REPLACE && result == ctx[0])
        result = values[0];
    if (!e->error) {
        key.result = result;
        e->maps[slot] = key;
    }
    return result;
}
tt_id replace_ctx(tt_engine *e, tt_id a, tt_id c, tt_id v) {
    return c ? transform(e, a, MAP_CONTEXT, &c, &v, 1, 0) : a;
}
tt_id bind_ctx(tt_engine *e, tt_id a, tt_id c, unsigned offset) {
    return c ? transform(e, a, MAP_BIND, &c, &offset, 1, 0) : a;
}
tt_id instantiate(tt_engine *e, tt_id a, tt_id v) {
    return transform(e, a, MAP_INSTANTIATE, NULL, &v, 1, 0);
}

bool reducible(const tt_engine *e, tt_id a, bool defs) {
    if (!a)
        return false;
    node n = e->nodes[a];
    if (defs && n.kind == N_DRef)
        return n.param && n.param <= e->nj;
    switch (n.kind) {
    case N_Ap:
        return e->nodes[n.ch[0]].kind == N_Lambda;
    case N_IndNat:
        return e->nodes[n.ch[2]].kind == N_ZN || e->nodes[n.ch[2]].kind == N_SN;
    case N_IndSigma:
        return e->nodes[n.ch[1]].kind == N_Tuple;
    case N_IndSum:
        return e->nodes[n.ch[2]].kind == N_Inl || e->nodes[n.ch[2]].kind == N_Inr;
    case N_IndEq:
        return e->nodes[n.ch[3]].kind == N_Refl;
    case N_IndUnit:
        return e->nodes[n.ch[1]].kind == N_Singleton;
    case N_IndW:
        return e->nodes[n.ch[1]].kind == N_WSup;
    case N_IndSusp: {
        node data = e->nodes[n.ch[3]];
        unsigned kind = e->nodes[data.ch[1]].kind;
        return kind == N_North || kind == N_South;
    }
    default:
        return false;
    }
}
static tt_id beta(tt_engine *e, tt_id a, bool defs) {
    node n = e->nodes[a];
    if (defs && n.kind == N_DRef)
        return e->judgements[n.param].expr;
    /* These negative shifts preserve the upstream eliminator representation.
     * They compensate for its node-wide binder depth; do not replace them with
     * ordinary lambda substitution without revisiting all dependent proofs. */
    tt_id vals[2] = {0}, bias[2] = {(uint32_t)-2, 0};
    switch (n.kind) {
    case N_Ap:
        vals[0] = n.ch[1];
        return transform(e, e->nodes[n.ch[0]].ch[0], MAP_BETA_SUBST, NULL, vals, 1, 0);
    case N_IndSigma: {
        node pair = e->nodes[n.ch[1]];
        vals[0] = pair.ch[1];
        vals[1] = pair.ch[0];
        return transform(e, n.ch[0], MAP_BETA_SUBST, bias, vals, 2, 0);
    }
    case N_IndNat: {
        node input = e->nodes[n.ch[2]];
        /* IndNat contributes two virtual levels to every child. The recursive
         * call retains those levels; the predecessor and zero branch do not. */
        tt_id lower = (uint32_t)-2;
        if (input.kind == N_ZN)
            return transform(e, n.ch[0], MAP_SHIFT, NULL, &lower, 1, 0);
        vals[0] = make3(e, N_IndNat, n.ch[0], n.ch[1], input.ch[0]);
        vals[1] = transform(e, input.ch[0], MAP_SHIFT, NULL, &lower, 1, 0);
        return transform(e, n.ch[1], MAP_BETA_SUBST, NULL, vals, 2, 0);
    }
    case N_IndSum: {
        node input = e->nodes[n.ch[2]];
        vals[input.kind == N_Inl ? 1 : 0] = input.ch[0];
        return transform(e, n.ch[input.kind == N_Inl ? 0 : 1], MAP_BETA_SUBST, bias, vals, 2, 0);
    }
    case N_IndEq:
        bias[0] = (uint32_t)-1;
        vals[0] = e->nodes[n.ch[3]].ch[0];
        return transform(e, n.ch[0], MAP_BETA_SUBST, bias, vals, 1, 0);
    case N_IndSusp: {
        node data = e->nodes[n.ch[3]];
        return n.ch[e->nodes[data.ch[1]].kind == N_North ? 1 : 2];
    }
    case N_IndUnit:
        vals[0] = leaf(e, N_Singleton, 0);
        return transform(e, n.ch[0], MAP_BETA_SUBST, NULL, vals, 1, 0);
    case N_IndW: {
        node input = e->nodes[n.ch[1]];
        tt_id lower = (uint32_t)-2;
        vals[0] = transform(e, input.ch[1], MAP_SHIFT, NULL, &lower, 1, 0);
        vals[1] = transform(e, input.ch[0], MAP_SHIFT, NULL, &lower, 1, 0);
        tt_id d = transform(e, n.ch[0], MAP_BETA_SUBST, NULL, vals, 2, 0);
        tt_id shift = 1;
        tt_id f = transform(e, input.ch[1], MAP_SHIFT, NULL, &shift, 1, 0);
        tt_id branch = transform(e, n.ch[0], MAP_SHIFT, NULL, &shift, 1, 2);
        /* The recursive argument lies under the new IndW's two virtual
         * levels as well as its surrounding lambda. */
        tt_id child = make2(e, N_Ap, f, leaf(e, N_VRef, 2));
        tt_id recursive = make1(e, N_Lambda, make2(e, N_IndW, branch, child));
        return make2(e, N_Ap, d, recursive);
    }
    default:
        return a;
    }
}
/* One bottom-up reduction pass, not an unbounded normalization loop.
 * recursive visits original children before reducing the root once; newly
 * produced redexes may require another explicit reduction inference. */
tt_id reduce(tt_engine *e, tt_id a, bool defs, bool recursive) {
    if (!a || e->error)
        return 0;
    tt_id original = a;
    unsigned mode = 100 + (unsigned)defs + 2 * (unsigned)recursive;
    size_t slot = tt_mix(a + ((uint64_t)mode << 32)) & (e->map_cap - 1);
    map_cache cached = e->maps[slot];
    if (cached.ast == a && cached.mode == mode && cached.generation == e->map_generation &&
        cached.result)
        return cached.result;
    node n = e->nodes[a];
    if (recursive) {
        bool changed = false;
        for (unsigned i = 0; i < n.arity; i++) {
            tt_id v = reduce(e, n.ch[i], defs, true);
            changed |= v != n.ch[i];
            n.ch[i] = v;
        }
        if (changed)
            a = intern(e, n);
    }
    tt_id result = !e->error && reducible(e, a, defs) ? beta(e, a, defs) : a;
    if (!e->error)
        e->maps[slot] = (map_cache){
            .ast = original, .mode = mode, .result = result, .generation = e->map_generation};
    return result;
}
tt_id pointed(const tt_engine *e, tt_id a, tt_id path) {
    while (path && a) {
        node p = e->nodes[path], n = e->nodes[a];
        if (p.param >= n.arity)
            return 0;
        a = n.ch[p.param];
        path = p.ch[0];
    }
    return a;
}
tt_id at_path(tt_engine *e, tt_id a, tt_id path, tt_id value) {
    if (!path)
        return value;
    node n = e->nodes[a], p = e->nodes[path];
    if (p.param >= n.arity) {
        e->error = TT_INVALID;
        return 0;
    }
    n.ch[p.param] = at_path(e, n.ch[p.param], p.ch[0], value);
    return intern(e, n);
}
tt_id path_append(tt_engine *e, tt_id p, unsigned child) {
    if (!p)
        return leaf(e, N_Path, child);
    node n = e->nodes[p];
    n.ch[0] = path_append(e, n.ch[0], child);
    n.arity = 1;
    return intern(e, n);
}
tt_id path_pop(tt_engine *e, tt_id p) {
    if (!p || !e->nodes[p].ch[0])
        return 0;
    node n = e->nodes[p];
    n.ch[0] = path_pop(e, n.ch[0]);
    n.arity = n.ch[0] ? 1 : 0;
    return intern(e, n);
}
