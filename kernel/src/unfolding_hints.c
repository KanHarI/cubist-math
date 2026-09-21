/* Unfolding priorities guide conversion. They grant no assumptions, erase no
 * premises, and never report equality: conversion must still prove it. */
#include "term_internal.h"

bool cc_kernel_set_unfolding_hints(cc_kernel *k, const cc_term *references, size_t count) {
    if (!k)
        return false;
    /* Clearing must work in a finally block after a failed kernel operation. */
    if (!count) {
        free(k->unfolding_hints);
        k->unfolding_hints = NULL;
        k->unfolding_hint_count = 0;
        return true;
    }
    if (!references || count > SIZE_MAX / sizeof(uint32_t))
        return ck_fail(k, "Invalid unfolding hint list.");
    uint32_t *hints = malloc(count * sizeof *hints);
    if (!hints)
        return ck_fail(k, "Unfolding hint allocation failed.");
    size_t length = 0;
    for (size_t i = 0; i < count; ++i) {
        cc_term reference = references[i];
        if (!reference || reference >= k->count || k->nodes[reference].kind != CC_DEFREF ||
            !k->nodes[reference].payload || k->nodes[reference].payload >= k->definition_count) {
            free(hints);
            return ck_fail(k, "An unfolding hint needs a checked definition reference.");
        }
        uint32_t index = k->nodes[reference].payload;
        bool duplicate = false;
        for (size_t j = 0; j < length; ++j)
            if (hints[j] == index)
                duplicate = true;
        if (!duplicate)
            hints[length++] = index;
    }
    free(k->unfolding_hints);
    k->unfolding_hints = hints;
    k->unfolding_hint_count = length;
    return true;
}
