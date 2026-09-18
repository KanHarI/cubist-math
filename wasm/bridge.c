/* Browser adapter: checked construction goes through tt_apply only.
 * The private representation is read here for inspection, never mutated.
 * Integer session tokens avoid accepting raw C pointers from JavaScript. */
#include "kernel/internal.h"
#include <stdint.h>

typedef struct {
    tt_engine *engine;
    uint32_t token;
    tt_id result;
} session;
static session sessions[8];
static uint32_t next_token = 1;
static session *lookup(uint32_t token) {
    for (unsigned i = 0; i < 8; i++)
        if (sessions[i].engine && sessions[i].token == token)
            return &sessions[i];
    return NULL;
}
uint32_t wb_new(unsigned axioms) {
    if (!next_token)
        return 0;
    for (unsigned i = 0; i < 8; i++)
        if (!sessions[i].engine) {
            tt_config config = tt_default_config();
            config.allow_axioms = axioms != 0;
            /* Higher path equalities repeat their endpoint types in the tree view.
             * Storage pools already double on demand. Let allocation, rather
             * than fixed AST/judgement counts, determine their capacity. The
             * expression/depth guards and WASM address-space ceiling remain. */
            config.max_expression_nodes = 16777216;
            config.max_ast_nodes = 0;
            config.max_judgements = 0;
            config.max_counter = 16384;
            tt_engine *engine = tt_new(&config);
            if (!engine)
                return 0;
            sessions[i] = (session){engine, next_token++, 0};
            return sessions[i].token;
        }
    return 0;
}
void wb_free(uint32_t token) {
    session *s = lookup(token);
    if (s) {
        tt_free(s->engine);
        *s = (session){0};
    }
}
int wb_apply(uint32_t token, unsigned op, tt_id j0, tt_id j1, tt_id j2, tt_id j3, tt_id j4,
             tt_id context_id, tt_id f0, tt_id f1, tt_id f2, tt_id f3) {
    session *s = lookup(token);
    const tt_opcode_info *m = tt_opcode_metadata((tt_opcode)op);
    if (!s)
        return TT_INVALID;
    s->result = 0;
    if (!m)
        return TT_INVALID;
    tt_id js[] = {j0, j1, j2, j3, j4}, fs[] = {f0, f1, f2, f3};
    return tt_apply(s->engine, (tt_opcode)op, js, m->judgements, context_id, fs, m->free_contexts,
                    &s->result);
}
uint32_t wb_result(uint32_t token) {
    const session *s = lookup(token);
    return s ? s->result : 0;
}
const char *wb_name(unsigned op) {
    const tt_opcode_info *m = tt_opcode_metadata((tt_opcode)op);
    return m ? m->name : "";
}
int wb_meta(unsigned op, unsigned field) {
    const tt_opcode_info *m = tt_opcode_metadata((tt_opcode)op);
    if (!m)
        return -1;
    switch (field) {
    case 0:
        return m->judgements;
    case 1:
        return m->context;
    case 2:
        return m->free_contexts;
    case 3:
        return m->returns_context;
    default:
        return -1;
    }
}
uint32_t wb_view(uint32_t token, unsigned is_context, tt_id id, unsigned field) {
    const session *s = lookup(token);
    if (!s || !id)
        return 0;
    const tt_engine *e = s->engine;
    if (is_context) {
        if (id > e->nc)
            return 0;
        context c = e->contexts[id];
        switch (field) {
        case 0:
            return c.type;
        case 1:
            return c.set;
        case 2:
            return c.counter;
        default:
            return 0;
        }
    }
    if (id > e->nj)
        return 0;
    judgement j = e->judgements[id];
    switch (field) {
    case 0:
        return j.expr;
    case 1:
        return j.type;
    case 2:
        return j.set;
    case 3:
        return j.path;
    case 4:
        return j.highlight;
    case 5:
        return j.op;
    default:
        return 0;
    }
}
uint32_t wb_node(uint32_t token, tt_id id, unsigned field) {
    const session *s = lookup(token);
    if (!s || !id || id > s->engine->nn)
        return 0;
    node n = s->engine->nodes[id];
    switch (field) {
    case 0:
        return n.kind;
    case 1:
        return n.param;
    case 2:
        return n.arity;
    case 3:
        return n.size;
    case 4:
        return n.depth;
    case 5:
    case 6:
    case 7:
    case 8:
        return n.ch[field - 5];
    case 9:
        return reducible(s->engine, id, false);
    case 10:
        return reducible(s->engine, id, true);
    default:
        return 0;
    }
}
const char *wb_node_name(uint32_t token, tt_id id) {
    const session *s = lookup(token);
    tt_ast_view view;
    return s && tt_ast(s->engine, id, &view) ? view.kind : "";
}
double wb_stats(uint32_t token, unsigned field) {
    const session *s = lookup(token);
    tt_stats stats;
    if (!s)
        return 0;
    tt_get_stats(s->engine, &stats);
    switch (field) {
    case 0:
        return (double)stats.inference_calls;
    case 1:
        return (double)stats.inference_cache_hits;
    case 2:
        return stats.ast_nodes;
    case 3:
        return stats.judgements;
    case 4:
        return stats.contexts;
    case 5:
        return (double)stats.reserved_bytes;
    default:
        return 0;
    }
}
int wb_verify(uint32_t token, tt_id proposition, tt_id proof) {
    const session *s = lookup(token);
    return s && tt_verify(s->engine, proposition, proof);
}
