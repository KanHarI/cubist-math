/* Reuse only successful native judgements in the exact same telescope and
 * interval scope. A hash locates an entry; exact key comparison authorizes
 * reuse. Context identities are never recycled, including after eviction.
 * Syntax sharing alone is NOT evidence of typing. */
#include "term_internal.h"

cc_context ck_extend(cc_kernel *k, uint32_t name, cc_term type, const cc_context *previous) {
    ck_trace(k, CC_TRACE_EXTEND, name, type, 0);
    uint64_t parent = previous ? previous->identity : 0;
    if (!k->contexts) k->contexts = calloc(CC_CHECK_MEMO_SIZE, sizeof *k->contexts);
    size_t slot = ((parent * UINT64_C(1099511628211) ^ name) * UINT64_C(1099511628211) ^ type) % CC_CHECK_MEMO_SIZE;
    cc_context_memo *entry = k->contexts ? &k->contexts[slot] : NULL;
    uint64_t identity;
    if (entry && entry->identity && entry->parent == parent && entry->name == name && entry->type == type) {
        identity = entry->identity;
    } else {
        if (k->next_context == UINT64_MAX) ck_fail(k, "Context identity exhausted.");
        identity = k->next_context == UINT64_MAX ? UINT64_MAX : ++k->next_context;
        if (entry) *entry = (cc_context_memo){name, type, parent, identity};
    }
    return (cc_context){name, type, previous, identity};
}

static size_t slot(cc_term raw, uint64_t context, uint64_t dims) {
    return ((context * UINT64_C(1099511628211) ^ dims) * UINT64_C(1099511628211) ^ raw) % CC_CHECK_MEMO_SIZE;
}
bool ck_inference_get(cc_kernel *k, cc_term raw, const cc_context *ctx, uint64_t dims, cc_judgement *out) {
    if (!(k->optimizations & CC_REUSE_CHECKS) || !k->inferred || !raw) return false;
    uint64_t context = ctx ? ctx->identity : 0;
    cc_infer_memo entry = k->inferred[slot(raw, context, dims)];
    if (entry.raw != raw || entry.context != context || entry.dimensions != dims) return false;
    *out = entry.checked;
    return true;
}
void ck_inference_put(cc_kernel *k, cc_term raw, const cc_context *ctx, uint64_t dims, cc_judgement checked) {
    if (!(k->optimizations & CC_REUSE_CHECKS)) return;
    if (!k->inferred) k->inferred = calloc(CC_CHECK_MEMO_SIZE, sizeof *k->inferred);
    uint64_t context = ctx ? ctx->identity : 0;
    if (k->inferred) k->inferred[slot(raw, context, dims)] = (cc_infer_memo){raw, context, dims, checked};
}
void ck_clear_check_cache(cc_kernel *k) {
    if (k->inferred) memset(k->inferred, 0, CC_CHECK_MEMO_SIZE * sizeof *k->inferred);
    if (k->contexts) memset(k->contexts, 0, CC_CHECK_MEMO_SIZE * sizeof *k->contexts);
}
