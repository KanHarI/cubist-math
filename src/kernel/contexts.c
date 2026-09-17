#include "internal.h"

/* A zero free-context slot means no abstraction was requested. Nonzero
 * contexts must have exactly the expected interned type. */
bool context_matches(tt_engine *e, tt_id context_id, tt_id expected_type) {
    return !context_id || e->contexts[context_id].type == expected_type;
}
/* Discharging x is illegal if an assumption that survives the rule still
 * depends on x. Metadata identifies which premises discharge each context and
 * which other discharged contexts may depend on it. All IDs are validated by
 * tt_apply before this function reads them. */
bool check_contexts(tt_engine *e, const tt_opcode_info *rule, const judgement *premises,
                    const tt_id *free_contexts) {
    for (unsigned discharged = 0; discharged < rule->free_contexts; discharged++)
        if (free_contexts[discharged]) {
            tt_id allowed_dependencies[4] = {0};
            for (unsigned other = 0; other < rule->free_contexts; other++)
                if (free_contexts[other] &&
                    (rule->pop_judgements[discharged] & rule->pop_judgements[other])) {
                    if (rule->allowed_free_contexts[other] & (1u << discharged))
                        allowed_dependencies[other] = free_contexts[other];
                    else if (set_has(e, e->contexts[free_contexts[other]].set,
                                     free_contexts[discharged]))
                        return false;
                }
            for (unsigned premise = 0; premise < rule->judgements; premise++)
                if (rule->pop_judgements[discharged] & (1u << premise)) {
                    for (tt_id set = premises[premise].set; set; set = e->nodes[set].ch[0]) {
                        tt_id context_id = e->nodes[set].param;
                        bool permitted = context_id == free_contexts[discharged];
                        for (unsigned other = 0; other < 4; other++)
                            permitted |= allowed_dependencies[other] &&
                                         context_id == allowed_dependencies[other];
                        if (!permitted &&
                            set_has(e, e->contexts[context_id].set, free_contexts[discharged]))
                            return false;
                    }
                }
        }
    return true;
}
/* Union premise assumptions after the permitted discharges, then include the
 * explicitly injected context and its dependencies. Do not merely drop every
 * free context: the discharge mask is different for each premise. */
tt_id output_context(tt_engine *e, const tt_opcode_info *rule, const judgement *premises, tt_id ctx,
                     const tt_id *free_contexts) {
    tt_id out = 0;
    for (unsigned premise = 0; premise < rule->judgements; premise++)
        for (tt_id set = premises[premise].set; set; set = e->nodes[set].ch[0]) {
            tt_id context_id = e->nodes[set].param;
            bool pop = false;
            for (unsigned discharge_slot = 0; discharge_slot < rule->free_contexts;
                 discharge_slot++)
                if (free_contexts[discharge_slot] == context_id &&
                    (rule->pop_judgements[discharge_slot] & (1u << premise)))
                    pop = true;
            if (!pop)
                out = set_add(e, out, context_id);
        }
    if (ctx) {
        out = set_add(e, out, ctx);
        for (tt_id set = e->contexts[ctx].set; set; set = e->nodes[set].ch[0])
            out = set_add(e, out, e->nodes[set].param);
    }
    return out;
}
