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
    k->checkpoint_store[0] = k->fact_count;
    k->checkpoint_store[1] = k->entry_count;
    k->checkpoint_store[2] = k->context_set_count;
    k->checkpoint_store[3] = k->context_item_count;
    k->checkpoint_store[4] = k->position_count;
    ck_signatures_checkpoint(k);
}

/* Instruction judgements made since the checkpoint refer to syntax that a
 * rollback discards or a commit compacts, so both drop them. Definitions
 * they published survive a commit; their lookups can be issued again. */
static void truncate_store(cc_kernel *k) {
    k->fact_count = k->checkpoint_store[0];
    k->entry_count = k->checkpoint_store[1];
    k->context_set_count = k->checkpoint_store[2];
    k->context_item_count = k->checkpoint_store[3];
    k->position_count = k->checkpoint_store[4];
}
void cc_kernel_rollback(cc_kernel *k) {
    if (!k || !k->checkpoint_count) return;
    if (k->weak_cache) memset(k->weak_cache, 0, k->count * sizeof *k->weak_cache);
    if (k->syntax_memo) memset(k->syntax_memo, 0, CC_SYNTAX_MEMO_SIZE * sizeof *k->syntax_memo);
    if (k->alpha_memo) memset(k->alpha_memo, 0, CC_ALPHA_MEMO_SIZE * sizeof *k->alpha_memo);
    k->count = k->checkpoint_count;
    k->definition_count = k->checkpoint_definitions;
    truncate_store(k);
    ck_signatures_rollback(k);
    k->checkpoint_count = 0;
    k->recursion = 0;
    cc_kernel_clear_error(k);
}

cc_term cc_kernel_relocated(const cc_kernel *k, cc_term term) {
    if (!k || !term) return 0;
    if (!k->relocation || term < k->relocation_base) return term;
    size_t offset = (size_t)term - k->relocation_base;
    return offset < k->relocation_count ? k->relocation[offset] : 0;
}

/* An admitted signature's recorded syntax: a commit keeps it, as it keeps a
 * definition's value and type (H1 specification, section 5.1). */
static void signature_terms(cc_kernel *k, size_t base, cc_term *map, bool relocate) {
    for (size_t i = 1; i < k->signature_count; ++i) {
        cc_signature *s = &k->signatures[i];
        cc_term *terms[] = {&s->former, &s->level};
        for (size_t j = 0; j < 2; ++j)
            if (*terms[j] >= base) { if (relocate) *terms[j] = map[*terms[j] - base]; else map[*terms[j] - base] = 1; }
        for (uint32_t j = 0; j < s->parameter_count; ++j) {
            cc_term *t = &s->parameter_types[j];
            if (*t >= base) { if (relocate) *t = map[*t - base]; else map[*t - base] = 1; }
        }
        for (uint32_t j = 0; j < s->constructor_count; ++j) {
            cc_term *t = &s->constructors[j].type;
            if (*t >= base) { if (relocate) *t = map[*t - base]; else map[*t - base] = 1; }
        }
    }
}

bool cc_kernel_commit_checkpoint(cc_kernel *k) {
    if (!k || !k->checkpoint_count || k->error[0]) return false;
    ck_standalone(k);
    /* An open signature depends on judgements that a commit truncates. */
    if (ck_signatures_open(k))
        return ck_fail(k, "A signature is still open; close it before committing.");
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
    signature_terms(k, base, map, false);
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
    signature_terms(k, base, map, true);
    k->count = next; k->checkpoint_count = 0;
    /* The survivors have new handles: index them again. */
    for (size_t i = base; i < next; ++i) ck_intern(k, (cc_term)i);
    truncate_store(k);
    k->relocation = map; k->relocation_base = base; k->relocation_count = count;
    return true;
}
