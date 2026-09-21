/* Discard an unsuccessful diagnostic attempt. Syntax is immutable and only
 * points backwards, so earlier definitions cannot refer to discarded nodes.
 * Cached reductions can point forwards: every such cache must be cleared. */
#include "term_internal.h"
void cc_kernel_checkpoint(cc_kernel *k) {
    if (!k) return;
    free(k->relocation); k->relocation = NULL;
    k->relocation_count = 0;
    k->checkpoint_count = k->count;
    k->checkpoint_definitions = k->definition_count;
}
void cc_kernel_rollback(cc_kernel *k) {
    if (!k || !k->checkpoint_count) return;
    if (k->weak_cache) memset(k->weak_cache, 0, k->count * sizeof *k->weak_cache);
    if (k->syntax_memo) memset(k->syntax_memo, 0, CC_SYNTAX_MEMO_SIZE * sizeof *k->syntax_memo);
    if (k->alpha_memo) memset(k->alpha_memo, 0, CC_ALPHA_MEMO_SIZE * sizeof *k->alpha_memo);
    k->count = k->checkpoint_count;
    k->definition_count = k->checkpoint_definitions;
    k->checkpoint_count = 0;
    k->unfolding_hint_count = 0;
    k->recursion = 0;
    cc_kernel_clear_error(k);
}

cc_term cc_kernel_relocated(const cc_kernel *k, cc_term term) {
    if (!k || !term) return 0;
    if (!k->relocation || term < k->relocation_base) return term;
    size_t offset = (size_t)term - k->relocation_base;
    return offset < k->relocation_count ? k->relocation[offset] : 0;
}

bool cc_kernel_commit_checkpoint(cc_kernel *k) {
    if (!k || !k->checkpoint_count || k->error[0]) return false;
    size_t base = k->checkpoint_count, count = k->count - base;
    cc_term *map = calloc(count ? count : 1, sizeof *map);
    if (!map) return ck_fail(k, "Checkpoint compaction allocation failed.");
    /* Every new checked definition is a root. References are roots too, so
     * clients can recover their handles without re-registering definitions. */
    for (size_t i = k->checkpoint_definitions; i < k->definition_count; ++i) {
        cc_definition d = k->definitions[i];
        if (d.value >= base) map[d.value - base] = 1;
        if (d.type >= base) map[d.type - base] = 1;
    }
    for (size_t i = base; i < k->count; ++i)
        if (k->nodes[i].kind == CC_DEFREF) map[i - base] = 1;
    /* Children always precede their parent in the immutable syntax arena.
     * A backwards pass therefore marks the complete reachable DAG. */
    for (size_t i = k->count; i-- > base;)
        if (map[i - base])
            for (unsigned j = 0; j < 4; ++j) {
                cc_term child = k->nodes[i].child[j];
                if (child >= base) map[child - base] = 1;
            }
    if (k->weak_cache) memset(k->weak_cache, 0, k->count * sizeof *k->weak_cache);
    if (k->syntax_memo) memset(k->syntax_memo, 0, CC_SYNTAX_MEMO_SIZE * sizeof *k->syntax_memo);
    if (k->alpha_memo) memset(k->alpha_memo, 0, CC_ALPHA_MEMO_SIZE * sizeof *k->alpha_memo);
    size_t next = base;
    for (size_t i = base; i < k->count; ++i) if (map[i - base]) {
        cc_node node = k->nodes[i];
        for (unsigned j = 0; j < 4; ++j)
            if (node.child[j] >= base) node.child[j] = map[node.child[j] - base];
        map[i - base] = (cc_term)next;
        k->nodes[next++] = node;
    }
    for (size_t i = k->checkpoint_definitions; i < k->definition_count; ++i) {
        cc_definition *d = &k->definitions[i];
        if (d->value >= base) d->value = map[d->value - base];
        if (d->type >= base) d->type = map[d->type - base];
    }
    k->count = next; k->checkpoint_count = 0;
    k->relocation = map; k->relocation_base = base; k->relocation_count = count;
    return true;
}
