/* Definitions are an acyclic environment, not hypotheses: instruction Define
 * registers a derived closed judgement, which may reference only earlier
 * definitions, and Lookup reads it back. References preserve source names;
 * Step(Delta) unfolds their stored bodies on demand. */
#include "term_internal.h"

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
