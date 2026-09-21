/* Discard an unsuccessful diagnostic attempt. Syntax is immutable and only
 * points backwards, so earlier definitions cannot refer to discarded nodes.
 * Cached reductions can point forwards: every such cache must be cleared. */
#include "term_internal.h"
void cc_kernel_checkpoint(cc_kernel *k) {
    if (!k) return;
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
