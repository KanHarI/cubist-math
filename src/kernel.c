#include "internal.h"
#include <inttypes.h>

static const tt_opcode_info metadata[204] = {
#include "metadata.inc"
};
const tt_opcode_info *tt_opcode_metadata(tt_opcode op) {
    return (unsigned)op < 204 && metadata[op].name ? &metadata[op] : NULL;
}
static void trace_result(tt_engine *e, const inference_cache *call, tt_status status,
                         tt_id result) {
    if (!e->trace)
        return;
    const tt_opcode_info *m = &metadata[call->op];
    fprintf(e->trace, "%u %u", call->op, m->judgements);
    for (unsigned i = 0; i < m->judgements; i++)
        fprintf(e->trace, " %u", call->j[i]);
    fprintf(e->trace, " %u %u", call->ctx, m->free_contexts);
    for (unsigned i = 0; i < m->free_contexts; i++)
        fprintf(e->trace, " %u", call->f[i]);
    uint64_t ef = 0, tf = 0, cf = 0;
    if (status == TT_OK) {
        tt_id set;
        if (m->returns_context) {
            context c = e->contexts[result];
            tf = fingerprint(e, c.type);
            set = c.set;
        } else {
            judgement j = e->judgements[result];
            ef = fingerprint(e, j.expr);
            tf = fingerprint(e, j.type);
            set = j.set;
        }
        for (tt_id s = set; s; s = e->nodes[s].ch[0])
            cf = tt_mix(cf ^ e->nodes[s].param);
    }
    fprintf(e->trace, " %u %u %" PRIu64 " %" PRIu64 " %" PRIu64 "\n", status, result, ef, tf, cf);
}

static bool context_matches(tt_engine *e, tt_id c, tt_id t) {
    return !c || e->contexts[c].type == t;
}
static bool check_contexts(tt_engine *e, const tt_opcode_info *m, const judgement *j,
                           const tt_id *f) {
    for (unsigned a = 0; a < m->free_contexts; a++)
        if (f[a]) {
            tt_id whitelist[4] = {0};
            for (unsigned b = 0; b < m->free_contexts; b++)
                if (f[b] && (m->pop_judgements[a] & m->pop_judgements[b])) {
                    if (m->allowed_free_contexts[b] & (1u << a))
                        whitelist[b] = f[b];
                    else if (set_has(e, e->contexts[f[b]].set, f[a]))
                        return false;
                }
            for (unsigned k = 0; k < m->judgements; k++)
                if (m->pop_judgements[a] & (1u << k)) {
                    for (tt_id s = j[k].set; s; s = e->nodes[s].ch[0]) {
                        tt_id c = e->nodes[s].param;
                        bool skip = c == f[a];
                        for (unsigned b = 0; b < 4; b++)
                            skip |= whitelist[b] && c == whitelist[b];
                        if (!skip && set_has(e, e->contexts[c].set, f[a]))
                            return false;
                    }
                }
        }
    return true;
}
static tt_id output_context(tt_engine *e, const tt_opcode_info *m, const judgement *j, tt_id ctx,
                            const tt_id *f) {
    tt_id out = 0;
    for (unsigned i = 0; i < m->judgements; i++)
        for (tt_id s = j[i].set; s; s = e->nodes[s].ch[0]) {
            tt_id c = e->nodes[s].param;
            bool pop = false;
            for (unsigned k = 0; k < m->free_contexts; k++)
                if (f[k] == c && (m->pop_judgements[k] & (1u << i)))
                    pop = true;
            if (!pop)
                out = set_add(e, out, c);
        }
    if (ctx) {
        out = set_add(e, out, ctx);
        for (tt_id s = e->contexts[ctx].set; s; s = e->nodes[s].ch[0])
            out = set_add(e, out, e->nodes[s].param);
    }
    return out;
}

bool infer_eliminator(tt_engine *, tt_opcode, const judgement *, const tt_id *, judgement *);

static bool infer(tt_engine *e, tt_opcode op, const tt_id *ids, const judgement *j, tt_id ctx,
                  const tt_id *f, judgement *r) {
#define E(i) (j[i].expr)
#define T(i) (j[i].type)
#define K(a) (e->nodes[(a)].kind)
#define CH(a, i) (e->nodes[(a)].ch[i])
#define REQUIRE(x)                                                                                 \
    do {                                                                                           \
        if (!(x))                                                                                  \
            return false;                                                                          \
    } while (0)
    node a = e->nodes[E(0)], t = e->nodes[T(0)];
    tt_id b = 0, c = 0, d = 0;
    switch (op) {
    case TT_UIntro0:
        r->expr = leaf(e, N_U, 0);
        r->type = leaf(e, N_U, 1);
        break;
    case TT_UIntroOmega:
        r->expr = leaf(e, N_UUOmega, 0);
        r->type = leaf(e, N_UUKappa, 0);
        break;
    case TT_UIntro:
        REQUIRE(a.kind == N_U && t.kind == N_U && a.param < INT32_MAX - 2);
        r->expr = leaf(e, N_U, a.param + 1);
        r->type = leaf(e, N_U, a.param + 2);
        break;
    case TT_UCumul:
        REQUIRE(t.kind == N_U && t.param < INT32_MAX - 1);
        r->expr = E(0);
        r->type = leaf(e, N_U, t.param + 1);
        break;
    case TT_UCumulOmega:
        REQUIRE(t.kind == N_U || t.kind == N_UCRef);
        r->expr = E(0);
        r->type = leaf(e, N_UUOmega, 0);
        break;
    case TT_UCumulKappa:
        REQUIRE(universe(e, T(0)) && t.kind != N_UUKappa && a.kind == N_U);
        r->expr = E(0);
        r->type = leaf(e, N_UUKappa, 0);
        break;
    case TT_UCumulContext:
        REQUIRE(universe(e, T(0)) && T(0) == E(1) && universe(e, T(1)));
        r->expr = E(0);
        r->type = T(1);
        break;
    case TT_UCumul0:
        REQUIRE(t.kind == N_U && t.param == 0 && universe(e, E(1)) && universe(e, T(1)));
        r->expr = E(0);
        r->type = E(1);
        break;
    case TT_Vble:
        r->expr = leaf(e, N_CRef, ctx);
        r->type = e->contexts[ctx].type;
        break;
    case TT_UVble:
        b = e->contexts[ctx].type;
        REQUIRE(K(b) == N_UUOmega || K(b) == N_UUKappa || K(b) == N_UCRef);
        r->expr = leaf(e, N_UCRef, ctx);
        r->type = b;
        break;
    case TT_Axiom:
        REQUIRE(e->conf.allow_axioms && universe(e, T(0)) && !j[0].set);
        r->expr = leaf(e, N_Axiom, ids[0]);
        r->type = E(0);
        break;
    case TT_Def:
        REQUIRE(!j[0].set);
        r->expr = make2(e, N_DefEq, leaf(e, N_DRef, ids[0]), E(0));
        r->type = T(0);
        break;
    case TT_DefEqRefl:
        r->expr = make2(e, N_DefEq, E(0), E(0));
        r->type = T(0);
        break;
    case TT_DefEqSwp:
        REQUIRE(a.kind == N_DefEq);
        r->expr = make2(e, N_DefEq, a.ch[1], a.ch[0]);
        r->type = T(0);
        break;
    case TT_DefEqExtL:
    case TT_DefEqExtR:
        REQUIRE(a.kind == N_DefEq);
        r->expr = a.ch[op == TT_DefEqExtR];
        r->type = T(0);
        break;
    case TT_DefLookup:
        REQUIRE(j[0].highlight);
        b = pointed(e, j[0].highlight == 1 ? E(0) : T(0), j[0].path);
        REQUIRE(b && K(b) == N_DRef);
        c = e->nodes[b].param;
        REQUIRE(c && c <= e->nj);
        r->expr = make2(e, N_DefEq, b, e->judgements[c].expr);
        r->type = e->judgements[c].type;
        break;
    case TT_PiForm:
    case TT_SigmaForm:
    case TT_WForm:
        REQUIRE(universe(e, T(0)) && universe(e, T(1)) && context_matches(e, f[0], E(0)));
        b = bind_ctx(e, E(1), f[0], 0);
        r->expr = make2(e, op == TT_PiForm ? N_Pi : op == TT_SigmaForm ? N_Sigma : N_W, E(0), b);
        r->type = max_universe(e, T(0), T(1));
        break;
    case TT_PiIntro:
        REQUIRE(universe(e, T(0)) && context_matches(e, f[0], E(0)));
        b = bind_ctx(e, E(1), f[0], 0);
        c = bind_ctx(e, T(1), f[0], 0);
        r->expr = make1(e, N_Lambda, b);
        r->type = make2(e, N_Pi, E(0), c);
        break;
    case TT_PiElim:
        REQUIRE(t.kind == N_Pi && t.ch[0] == T(1));
        r->expr = make2(e, N_Ap, E(0), E(1));
        r->type = instantiate(e, t.ch[1], E(1));
        break;
    case TT_PiComp:
        REQUIRE(context_matches(e, f[0], T(1)));
        b = make1(e, N_Lambda, bind_ctx(e, E(0), f[0], 0));
        c = make2(e, N_Ap, b, E(1));
        d = replace_ctx(e, E(0), f[0], E(1));
        r->expr = make2(e, N_DefEq, c, d);
        r->type = replace_ctx(e, T(0), f[0], E(1));
        break;
    case TT_PiUniq:
        REQUIRE(t.kind == N_Pi);
        b = make2(e, N_Ap, E(0), leaf(e, N_VRef, 0));
        r->expr = make2(e, N_DefEq, E(0), make1(e, N_Lambda, b));
        r->type = T(0);
        break;
    case TT_SigmaIntro:
    case TT_WIntro:
        REQUIRE(universe(e, T(1)) && context_matches(e, f[0], T(0)));
        b = bind_ctx(e, E(1), f[0], 0);
        c = replace_ctx(e, E(1), f[0], E(0));
        r->type = make2(e, op == TT_SigmaIntro ? N_Sigma : N_W, T(0), b);
        REQUIRE(T(2) == (op == TT_SigmaIntro ? c : make2(e, N_Pi, c, r->type)));
        r->expr = make2(e, op == TT_SigmaIntro ? N_Tuple : N_WSup, E(0), E(2));
        break;
    case TT_SumForm:
    case TT_SumIntroL:
    case TT_SumIntroR:
        REQUIRE(universe(e, T(0)) && universe(e, T(1)));
        b = make2(e, N_Sum, E(0), E(1));
        if (op == TT_SumForm) {
            r->expr = b;
            r->type = max_universe(e, T(0), T(1));
        } else {
            REQUIRE(T(2) == E(op == TT_SumIntroR));
            r->expr = make1(e, op == TT_SumIntroL ? N_Inl : N_Inr, E(2));
            r->type = b;
        }
        break;
    case TT_VoidForm:
        r->expr = leaf(e, N_Void, 0);
        r->type = leaf(e, N_U, 0);
        break;
    case TT_UnitForm:
        r->expr = leaf(e, N_Unit, 0);
        r->type = leaf(e, N_U, 0);
        break;
    case TT_UnitIntro:
        r->expr = leaf(e, N_Singleton, 0);
        r->type = leaf(e, N_Unit, 0);
        break;
    case TT_NatForm:
        r->expr = leaf(e, N_Nat, 0);
        r->type = leaf(e, N_U, 0);
        break;
    case TT_NatIntroZ:
        r->expr = leaf(e, N_ZN, 0);
        r->type = leaf(e, N_Nat, 0);
        break;
    case TT_NatIntroS:
        REQUIRE(t.kind == N_Nat);
        r->expr = make1(e, N_SN, E(0));
        r->type = T(0);
        break;
    case TT_EqForm:
        REQUIRE(universe(e, T(0)) && T(1) == E(0) && T(2) == E(0));
        r->expr = make3(e, N_Eq, E(0), E(1), E(2));
        r->type = T(0);
        break;
    case TT_EqIntro:
        r->expr = make1(e, N_Refl, E(0));
        r->type = make3(e, N_Eq, T(0), E(0), E(0));
        break;
    case TT_Subs:
    case TT_HighSubs: {
        REQUIRE(K(E(1)) == N_DefEq);
        b = CH(E(1), 0);
        c = CH(E(1), 1);
        r->expr = E(0);
        r->type = T(0);
        if (op == TT_HighSubs) {
            REQUIRE(j[0].highlight);
            r->highlight = j[0].highlight;
            r->path = j[0].path;
            tt_id *root = r->highlight == 1 ? &r->expr : &r->type;
            d = pointed(e, *root, r->path);
            REQUIRE(d);
            d = transform(e, d, MAP_REPLACE, &b, &c, 1, 0);
            *root = at_path(e, *root, r->path, d);
        } else {
            r->expr = transform(e, E(0), MAP_REPLACE, &b, &c, 1, 0);
            r->type = transform(e, T(0), MAP_REPLACE, &b, &c, 1, 0);
        }
        break;
    }
    case TT_HighExp:
    case TT_HighType:
        r->expr = E(0);
        r->type = T(0);
        r->highlight = op == TT_HighExp ? 1 : 2;
        break;
    case TT_UnHigh:
        REQUIRE(j[0].highlight);
        r->expr = E(0);
        r->type = T(0);
        break;
    case TT_HighUp:
        REQUIRE(j[0].highlight && j[0].path);
        r->expr = E(0);
        r->type = T(0);
        r->highlight = j[0].highlight;
        r->path = path_pop(e, j[0].path);
        break;
    case TT_High0:
    case TT_High1:
    case TT_High2:
    case TT_High3:
        REQUIRE(j[0].highlight);
        b = pointed(e, j[0].highlight == 1 ? E(0) : T(0), j[0].path);
        REQUIRE(b && (unsigned)(op - TT_High0) < e->nodes[b].arity);
        r->expr = E(0);
        r->type = T(0);
        r->highlight = j[0].highlight;
        r->path = path_append(e, j[0].path, op - TT_High0);
        break;
    case TT_BetaReduceGrossKnuth:
    case TT_BetaReducePointed:
    case TT_DefBetaReduceGrossKnuth:
    case TT_DefReducePointed: {
        bool defs = op == TT_DefBetaReduceGrossKnuth || op == TT_DefReducePointed;
        bool rec = op == TT_BetaReduceGrossKnuth || op == TT_DefBetaReduceGrossKnuth;
        REQUIRE(rec || j[0].highlight);
        r->expr = E(0);
        r->type = T(0);
        r->highlight = j[0].highlight;
        r->path = j[0].path;
        if (r->highlight) {
            tt_id *root = r->highlight == 1 ? &r->expr : &r->type;
            b = pointed(e, *root, r->path);
            REQUIRE(b && (rec || reducible(e, b, defs)));
            b = reduce(e, b, defs, rec);
            *root = at_path(e, *root, r->path, b);
        } else {
            r->expr = reduce(e, E(0), defs, true);
            r->type = reduce(e, T(0), defs, true);
        }
        break;
    }
    default:
        return infer_eliminator(e, op, j, f, r);
    }
    return !e->error && r->expr && r->type;
#undef E
#undef T
#undef K
#undef CH
#undef REQUIRE
}

tt_status tt_apply(tt_engine *e, tt_opcode op, const tt_id *ids, size_t nj, tt_id ctx,
                   const tt_id *free_ctx, size_t nf, tt_id *result) {
    if (result)
        *result = 0;
    if (!e || !result)
        return TT_INVALID;
    e->stats.inference_calls++;
    e->error = TT_OK;
    if (e->cache_cap && e->cache_cap < 65536 && e->stats.inference_calls > e->cache_cap * 4) {
        size_t cap = e->cache_cap * 2;
        inference_cache *cache = calloc(cap, sizeof(*cache));
        if (cache) {
            free(e->cache);
            e->cache = cache;
            e->cache_cap = cap;
        }
    }
    if (e->map_cap < 32768 && e->nn > e->map_cap * 4) {
        size_t cap = e->map_cap * 2;
        map_cache *maps = calloc(cap, sizeof(*maps));
        if (maps) {
            free(e->maps);
            e->maps = maps;
            e->map_cap = cap;
        }
    }
    const tt_opcode_info *m = tt_opcode_metadata(op);
    if (!m || m->judgements != nj || m->free_contexts != nf || !!ctx != m->context ||
        (nj && !ids) || (nf && !free_ctx) || ctx > e->nc) {
        e->stats.rejected++;
        return TT_INVALID;
    }
    inference_cache key = {.op = (uint32_t)op, .ctx = ctx};
    uint64_t hash = tt_mix(op + ((uint64_t)ctx << 32));
    judgement j[5] = {{0}};
    tt_id f[4] = {0};
    for (size_t i = 0; i < nj; i++) {
        if (!ids[i] || ids[i] > e->nj) {
            e->stats.rejected++;
            return TT_INVALID;
        }
        key.j[i] = ids[i];
        j[i] = e->judgements[ids[i]];
        hash = tt_mix(hash ^ ids[i]);
    }
    for (size_t i = 0; i < nf; i++) {
        if (free_ctx[i] > e->nc) {
            e->stats.rejected++;
            return TT_INVALID;
        }
        key.f[i] = f[i] = free_ctx[i];
        hash = tt_mix(hash ^ f[i]);
    }
    size_t ci = e->cache_cap ? hash & (e->cache_cap - 1) : 0;
    if (e->cache_cap && e->cache[ci].op == key.op && !memcmp(&e->cache[ci], &key, 44)) {
        e->stats.inference_cache_hits++;
        *result = e->cache[ci].result;
        if (*result && !m->returns_context && e->conf.max_expression_nodes) {
            judgement cached = e->judgements[*result];
            if (e->nodes[cached.expr].size > e->conf.max_expression_nodes ||
                e->nodes[cached.type].size > e->conf.max_expression_nodes) {
                *result = 0;
                e->stats.rejected++;
                return TT_LIMIT;
            }
        }
        if (e->cache[ci].status == TT_OK) {
            e->stats.accepted++;
            e->accepted_opcodes[op]++;
        } else
            e->stats.rejected++;
        trace_result(e, &key, (tt_status)e->cache[ci].status, *result);
        return (tt_status)e->cache[ci].status;
    }
    tt_status status = TT_INVALID;
    uint32_t node_mark = e->nn;
    if (check_contexts(e, m, j, f)) {
        if (op == TT_CtxExt) {
            if (universe(e, j[0].type) && context_matches(e, f[0], j[0].expr)) {
                uint32_t counter = f[0] ? e->contexts[f[0]].counter + 1 : 0;
                if (counter <= e->conf.max_counter) {
                    context c = {j[0].expr, j[0].set, counter, ids[0]};
                    *result = save_context(e, c);
                    if (*result)
                        status = TT_OK;
                } else
                    status = TT_LIMIT;
            }
        } else {
            judgement r = {.op = (uint16_t)op, .ctx = ctx};
            if (infer(e, op, ids, j, ctx, f, &r)) {
                uint32_t limit = e->conf.max_expression_nodes;
                if (limit && (e->nodes[r.expr].size > limit || e->nodes[r.type].size > limit))
                    status = TT_LIMIT;
                else {
                    r.set = output_context(e, m, j, ctx, f);
                    memcpy(r.inputs, key.j, sizeof(key.j));
                    memcpy(r.free_ctx, f, sizeof(f));
                    *result = save_judgement(e, r);
                    if (*result)
                        status = TT_OK;
                }
            }
        }
    }
    if (e->error)
        status = e->error;
    if (status != TT_OK) {
        *result = 0;
        rollback_nodes(e, node_mark);
    }
    if (e->cache_cap && (status == TT_OK || status == TT_INVALID)) {
        key.result = *result;
        key.status = status;
        e->cache[ci] = key;
    }
    if (status == TT_OK) {
        e->stats.accepted++;
        e->accepted_opcodes[op]++;
    } else
        e->stats.rejected++;
    trace_result(e, &key, status, *result);
    return status;
}
