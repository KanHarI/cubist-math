/* CHM §3.2: homogeneous composition and transport for the pushout HIT.
 * HComp binds its direction only in tube terms. Trans binds its direction only
 * in the type family; its face and starting value live in the outer cube.
 * General composition checking certifies the box. Transport additionally
 * requires its family to be constant on the supplied face. */
#include "dimension_scope.h"

static cc_term rename_tubes(cc_kernel *k, cc_term system, unsigned dim,
                             const cc_formula *variable) {
    if (!system)
        return 0;
    cc_node tube = k->nodes[system];
    if (tube.kind != CC_TUBE)
        return ck_fail(k, "Malformed homogeneous composition system."), 0;
    cc_term body = ck_dimension_substitute(k, tube.child[0], dim, variable);
    cc_term tail = rename_tubes(k, tube.child[1], dim, variable);
    return ck_make(k, CC_TUBE, tube.payload, body, tail, 0, 0);
}

bool ck_hit_composition(cc_kernel *k, cc_node n, const cc_context *ctx,
                         uint64_t dims, cc_judgement *out) {
    if (n.payload >= CC_DIMENSIONS)
        return ck_fail(k, "HIT composition dimension outside native range.");
    dims = ck_live_dimensions(k, n, ctx, dims);
    uint64_t avoid = dims | ck_free_dims(k, n.child[0]) | ck_free_dims(k, n.child[1]) |
                     ck_free_dims(k, n.child[2]) | (UINT64_C(1) << n.payload);
    unsigned dim = ck_fresh_dimension(k, avoid);
    if (dim >= CC_DIMENSIONS)
        return false;
    cc_formula variable;
    cc_init(&variable, CC_INTERVAL);
    if (cc_generator(&variable, dim, true) != CC_OK) {
        cc_clear(&variable);
        return ck_fail(k, "HIT checking dimension allocation failed.");
    }
    cc_term family = n.child[0];
    cc_term system = n.child[1];
    cc_formula_id face = 0;
    if (n.kind == CC_HCOMP) {
        system = rename_tubes(k, system, n.payload, &variable);
    } else {
        if (!system || k->nodes[system].kind != CC_TUBE || k->nodes[system].child[1]) {
            cc_clear(&variable);
            return ck_fail(k, "Transport requires a single face descriptor.");
        }
        face = k->nodes[system].payload;
        family = ck_dimension_substitute(k, family, n.payload, &variable);
        system = ck_make(k, CC_TUBE, face, n.child[2], 0, 0, 0);
    }
    cc_clear(&variable);
    cc_node box = {CC_COMP, dim, {family, system, n.child[2], 0}, 0};
    cc_judgement checked;
    if (!ck_composition(k, box, ctx, dims, &checked))
        return false;
    cc_node result = k->nodes[checked.expression];
    cc_term head = ck_whnf(k, result.child[0]);
    if (!head || k->nodes[head].kind != CC_PUSHOUT)
        return ck_fail(k, "HComp/Trans currently require a pushout family.");
    if (n.kind == CC_TRANS) {
        /* Copy before conversion: its temporary formulas may grow the arena. */
        cc_formula phi;
        cc_init(&phi, CC_FACE);
        const cc_formula *raw = cc_kernel_get_formula(k, face);
        if (!raw || raw->sort != CC_FACE || cc_copy(&phi, raw) != CC_OK) {
            cc_clear(&phi);
            return ck_fail(k, "Transport face allocation failed.");
        }
        cc_term start = ck_endpoint_term(k, result.child[0], dim, 0);
        for (size_t i = 0; i < phi.length && !k->error[0]; ++i)
            if (!ck_convertible(k, ck_restrict(k, result.child[0], phi.clauses[i]),
                                   ck_restrict(k, start, phi.clauses[i])))
                ck_fail(k, "Transport family is not constant on its specified face.");
        cc_clear(&phi);
        if (k->error[0])
            return false;
        result.child[1] = ck_make(k, CC_TUBE, face, result.child[2], 0, 0, 0);
    }
    out->expression = ck_make(k, n.kind, dim, result.child[0], result.child[1], result.child[2], 0);
    out->type = checked.type;
    return !k->error[0];
}
