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

/* The sole public publication path for contexts and judgements.
 * Order matters: validate handles -> validate discharge -> check rule -> enforce
 * bounds -> compute assumptions -> publish. Rejected attempts roll back ASTs.
 * Cache entries are hints keyed by the complete request, never proof evidence. */
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
    /* Copy premises: rule construction can realloc every arena. Never retain
     * pointers into an arena across a constructor call. Unused premise slots
     * and arena element zero are initialized sentinels for nullary rules. */
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
    /* The hash chooses a slot only. Compare every request field on a hit. */
    size_t ci = e->cache_cap ? hash & (e->cache_cap - 1) : 0;
    if (e->cache_cap && e->cache[ci].op == key.op &&
        !memcmp(&e->cache[ci], &key, offsetof(inference_cache, result))) {
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
    /* No accepted judgement/context is published until all checks succeed. */
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
            if (infer_rule(e, op, ids, j, ctx, f, &r)) {
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
    /* Discard only this call's temporary nodes. Transformation cache generation
     * changes on rollback so a recycled temporary ID cannot yield a stale hit. */
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

/* Stored judgements have already passed tt_apply. Verification checks that
 * the proof and proposition are closed and that their types line up exactly. */
bool tt_verify(const tt_engine *e, tt_id proposition, tt_id proof) {
    if (!e || !proposition || !proof || proposition > e->nj || proof > e->nj)
        return false;
    judgement p = e->judgements[proposition], q = e->judgements[proof];
    return !p.set && !q.set && universe(e, p.type) && p.expr == q.type;
}
