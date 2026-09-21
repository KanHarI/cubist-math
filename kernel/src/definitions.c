/* Checked global definitions are an acyclic environment, not hypotheses.
 * Bodies are checked closed. They may reference only earlier checked entries.
 * References preserve source names; conversion unfolds their stored bodies on
 * demand. Source-level opacity does not introduce a new logical assumption. */
#include "term_internal.h"

cc_term cc_kernel_define(cc_kernel *k, uint32_t symbol, cc_term value, cc_term expected) {
    if (!k || k->error[0])
        return 0;
    for (size_t i = 1; i < k->definition_count; ++i)
        if (k->definitions[i].symbol == symbol)
            return ck_fail(k, "Definition symbol is already registered."), 0;
    if (k->definition_count >= UINT32_MAX)
        return ck_fail(k, "Definition handle space exhausted."), 0;
    cc_checked_result checked;
    if (!cc_kernel_check(k, value, expected, NULL, 0, &checked))
        return 0;
    if (k->definition_count >= k->definition_capacity) {
        size_t capacity = k->definition_capacity ? 2 * k->definition_capacity : 64;
        if (capacity < k->definition_capacity || capacity > SIZE_MAX / sizeof(cc_definition))
            return ck_fail(k, "Definition registry allocation overflow."), 0;
        cc_definition *grown = realloc(k->definitions, capacity * sizeof *grown);
        if (!grown)
            return ck_fail(k, "Definition registry allocation failed."), 0;
        k->definitions = grown;
        k->definition_capacity = capacity;
    }
    uint32_t index = (uint32_t)k->definition_count;
    cc_term reference = ck_make(k, CC_DEFREF, index, 0, 0, 0, 0);
    if (!reference)
        return 0;
    /* Publish only after checking and all allocations have succeeded. */
    k->definitions[index] = (cc_definition){symbol, checked.expression, checked.type};
    ++k->definition_count;
    return reference;
}

bool cc_kernel_definition(const cc_kernel *k, cc_term reference, uint32_t *symbol,
                           cc_term *value, cc_term *type) {
    if (!k || !reference || reference >= k->count)
        return false;
    cc_node node = k->nodes[reference];
    if (node.kind != CC_DEFREF || !node.payload || node.payload >= k->definition_count)
        return false;
    cc_definition definition = k->definitions[node.payload];
    if (symbol)
        *symbol = definition.symbol;
    if (value)
        *value = definition.value;
    if (type)
        *type = definition.type;
    return true;
}

cc_term cc_kernel_whnf(cc_kernel *k, cc_term term) {
    if (!k || !term || term >= k->count || k->error[0])
        return 0;
    k->budget = k->operation_budget;
    k->recursion = 0;
    return ck_whnf(k, term);
}
