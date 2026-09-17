#include "internal.h"

uint64_t tt_mix(uint64_t x) {
    x ^= x >> 30;
    x *= UINT64_C(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    x *= UINT64_C(0x94d049bb133111eb);
    return x ^ (x >> 31);
}
static uint64_t words_hash(const void *ptr, size_t n) {
#ifdef TT_TEST_CONSTANT_HASH
    (void)ptr;
    (void)n;
    return 0; /* Test every key in one collision cluster. */
#else
    uint64_t h = UINT64_C(0x9e3779b97f4a7c15);
    const unsigned char *p = ptr;
    for (size_t i = 0; i < n; i++) {
        uint32_t word;
        memcpy(&word, p + 4 * i, 4);
        h = tt_mix(h ^ word);
    }
    return h;
#endif
}
static bool grow_table(tt_engine *e, table *t) {
    size_t cap = t->cap ? t->cap * 2 : 1024;
    if (cap > SIZE_MAX / sizeof(slot)) {
        e->error = TT_OOM;
        return false;
    }
    slot *s = calloc(cap, sizeof(*s));
    if (!s) {
        e->error = TT_OOM;
        return false;
    }
    for (size_t i = 0; i < t->cap; i++)
        if (t->slots[i].id) {
            size_t j = t->slots[i].hash & (cap - 1);
            while (s[j].id)
                j = (j + 1) & (cap - 1);
            s[j] = t->slots[i];
        }
    free(t->slots);
    t->slots = s;
    t->cap = cap;
    return true;
}
static bool ensure(tt_engine *e, void **p, uint32_t *cap, uint32_t count, size_t width) {
    if (count < *cap)
        return true;
    if (*cap > UINT32_MAX / 2) {
        e->error = TT_LIMIT;
        return false;
    }
    uint32_t c = *cap ? *cap * 2 : 1024;
    if (c > SIZE_MAX / width) {
        e->error = TT_OOM;
        return false;
    }
    void *q = realloc(*p, (size_t)c * width);
    if (!q) {
        e->error = TT_OOM;
        return false;
    }
    if (!*cap)
        memset(q, 0, width);
    *p = q;
    *cap = c;
    return true;
}
static size_t lookup_start(tt_engine *e, table *t, uint64_t hash) {
    if ((t->used + 1) * 10 >= t->cap * 7 && !grow_table(e, t))
        return SIZE_MAX;
    return hash & (t->cap - 1);
}
/* Canonical structural interning. The key includes every constructor field;
 * hash matches still require full-key equality. Derived metadata is recomputed
 * only for new nodes. Accepted nodes are immutable for the engine lifetime. */
tt_id intern(tt_engine *e, node n) {
    if (e->error)
        return 0;
    uint64_t hash = words_hash((uint32_t *)&n, 6);
    size_t pos = lookup_start(e, &e->nt, hash);
    if (pos == SIZE_MAX)
        return 0;
    while (e->nt.slots[pos].id) {
        slot s = e->nt.slots[pos];
        if (s.hash == hash && !memcmp(&e->nodes[s.id], &n, offsetof(node, size)))
            return s.id;
        pos = (pos + 1) & (e->nt.cap - 1);
    }
    if (e->nn == UINT32_MAX - 1 || (e->conf.max_ast_nodes && e->nn >= e->conf.max_ast_nodes)) {
        e->error = TT_LIMIT;
        return 0;
    }
    n.size = 1;
    n.depth = 1;
    n.flags = 0;
    if (n.kind == N_CRef || n.kind == N_UCRef)
        n.flags = HAS_CONTEXT;
    if (n.kind == N_VRef)
        n.flags = HAS_VARIABLE;
    if (n.kind == N_DRef)
        n.flags = HAS_DEF;
    for (unsigned i = 0; i < n.arity; i++) {
        if (!n.ch[i] || n.ch[i] > e->nn) {
            e->error = TT_INVALID;
            return 0;
        }
        node child = e->nodes[n.ch[i]];
        n.size = UINT32_MAX - n.size < child.size ? UINT32_MAX : n.size + child.size;
        if (child.depth >= n.depth)
            n.depth = child.depth + 1;
        n.flags |= child.flags;
    }
    if (n.depth > e->conf.max_depth) {
        e->error = TT_LIMIT;
        return 0;
    }
    if (!ensure(e, (void **)&e->nodes, &e->cn, e->nn + 1, sizeof(node)))
        return 0;
    tt_id id = ++e->nn;
    e->nodes[id] = n;
    e->nt.slots[pos] = (slot){hash, id, 0};
    e->nt.used++;
    return id;
}
/* Remove a suffix of unpublished nodes. Backward-shift deletion preserves
 * the probe chain even when every key has the same hash (collision test).
 * Accepted judgements/contexts must never reference this suffix. */
void rollback_nodes(tt_engine *e, uint32_t mark) {
    if (mark == e->nn)
        return;
    size_t mask = e->nt.cap - 1;
    while (e->nn > mark) {
        tt_id id = e->nn--;
        uint64_t hash = words_hash(&e->nodes[id], 6);
        size_t hole = hash & mask;
        while (e->nt.slots[hole].id != id)
            hole = (hole + 1) & mask;
        size_t scan = (hole + 1) & mask;
        while (e->nt.slots[scan].id) {
            size_t home = e->nt.slots[scan].hash & mask;
            if (((scan - home) & mask) >= ((scan - hole) & mask)) {
                e->nt.slots[hole] = e->nt.slots[scan];
                hole = scan;
            }
            scan = (scan + 1) & mask;
        }
        e->nt.slots[hole] = (slot){0};
        e->nt.used--;
    }
    if (++e->map_generation == 0) {
        memset(e->maps, 0, e->map_cap * sizeof(*e->maps));
        e->map_generation = 1;
    }
}
tt_id leaf(tt_engine *e, node_kind k, uint32_t p) {
    return intern(e, (node){.kind = k, .param = p});
}
tt_id make1(tt_engine *e, node_kind k, tt_id a) {
    return intern(e, (node){.kind = k, .ch = {a}, .arity = 1});
}
tt_id make2(tt_engine *e, node_kind k, tt_id a, tt_id b) {
    return intern(e, (node){.kind = k, .ch = {a, b}, .arity = 2});
}
tt_id make3(tt_engine *e, node_kind k, tt_id a, tt_id b, tt_id c) {
    return intern(e, (node){.kind = k, .ch = {a, b, c}, .arity = 3});
}
tt_id make4(tt_engine *e, node_kind k, tt_id a, tt_id b, tt_id c, tt_id d) {
    return intern(e, (node){.kind = k, .ch = {a, b, c, d}, .arity = 4});
}
tt_id set_add(tt_engine *e, tt_id s, tt_id id) {
    if (!id)
        return s;
    if (!s)
        return leaf(e, N_Set, id);
    node n = e->nodes[s];
    if (n.param == id)
        return s;
    if (n.param > id)
        return intern(e, (node){.kind = N_Set, .param = id, .ch = {s}, .arity = 1});
    tt_id tail = set_add(e, n.ch[0], id);
    n.ch[0] = tail;
    n.arity = tail ? 1 : 0;
    return intern(e, n);
}
bool set_has(const tt_engine *e, tt_id s, tt_id id) {
    while (s) {
        node n = e->nodes[s];
        if (n.param == id)
            return true;
        if (n.param > id)
            return false;
        s = n.ch[0];
    }
    return false;
}
uint32_t set_count(const tt_engine *e, tt_id s) {
    return s ? e->nodes[s].size : 0;
}
tt_id save_judgement(tt_engine *e, judgement j) {
    if (e->error)
        return 0;
    /* Semantic deduplication, retaining the first checked derivation. */
    uint64_t h = words_hash((uint32_t *)&j, 5);
    size_t p = lookup_start(e, &e->jt, h);
    if (p == SIZE_MAX)
        return 0;
    while (e->jt.slots[p].id) {
        slot s = e->jt.slots[p];
        if (s.hash == h && !memcmp(&j, &e->judgements[s.id], offsetof(judgement, op)))
            return s.id;
        p = (p + 1) & (e->jt.cap - 1);
    }
    if (e->nj == UINT32_MAX - 1 || (e->conf.max_judgements && e->nj >= e->conf.max_judgements)) {
        e->error = TT_LIMIT;
        return 0;
    }
    if (!ensure(e, (void **)&e->judgements, &e->cj, e->nj + 1, sizeof(j)))
        return 0;
    tt_id id = ++e->nj;
    e->judgements[id] = j;
    e->jt.slots[p] = (slot){h, id, 0};
    e->jt.used++;
    return id;
}
tt_id save_context(tt_engine *e, context c) {
    if (e->error)
        return 0;
    /* A context is identified by type, assumptions and explicit counter. */
    uint64_t h = words_hash((uint32_t *)&c, 3);
    size_t p = lookup_start(e, &e->ct, h);
    if (p == SIZE_MAX)
        return 0;
    while (e->ct.slots[p].id) {
        slot s = e->ct.slots[p];
        if (s.hash == h && !memcmp(&c, &e->contexts[s.id], offsetof(context, source)))
            return s.id;
        p = (p + 1) & (e->ct.cap - 1);
    }
    if (e->nc == UINT32_MAX - 1) {
        e->error = TT_LIMIT;
        return 0;
    }
    if (!ensure(e, (void **)&e->contexts, &e->cc, e->nc + 1, sizeof(c)))
        return 0;
    tt_id id = ++e->nc;
    e->contexts[id] = c;
    e->ct.slots[p] = (slot){h, id, 0};
    e->ct.used++;
    return id;
}
tt_config tt_default_config(void) {
    return (tt_config){.max_expression_nodes = 256,
                       .max_depth = 256,
                       .max_counter = 32,
                       .allow_axioms = false,
                       .cache_inference = true};
}
tt_engine *tt_new(const tt_config *config) {
    tt_engine *e = calloc(1, sizeof(*e));
    if (!e)
        return NULL;
    e->conf = config ? *config : tt_default_config();
    if (!e->conf.max_depth)
        e->conf.max_depth = 256;
    if (e->conf.max_depth > 1024) {
        free(e);
        return NULL;
    }
    /* Start small for short proofs; the kernel grows caches for long walks. */
    e->cache_cap = e->conf.cache_inference ? 1024 : 0;
    e->map_cap = 1024;
    if (e->cache_cap)
        e->cache = calloc(e->cache_cap, sizeof(*e->cache));
    e->maps = calloc(e->map_cap, sizeof(*e->maps));
    if ((e->cache_cap && !e->cache) || !e->maps) {
        tt_free(e);
        return NULL;
    }
    if (!ensure(e, (void **)&e->nodes, &e->cn, 1, sizeof(node)) ||
        !ensure(e, (void **)&e->judgements, &e->cj, 1, sizeof(judgement)) ||
        !ensure(e, (void **)&e->contexts, &e->cc, 1, sizeof(context))) {
        tt_free(e);
        return NULL;
    }
    return e;
}
void tt_free(tt_engine *e) {
    if (e) {
        free(e->nodes);
        free(e->judgements);
        free(e->contexts);
        free(e->nt.slots);
        free(e->jt.slots);
        free(e->ct.slots);
        free(e->cache);
        free(e->maps);
        free(e);
    }
}
void tt_get_stats(const tt_engine *e, tt_stats *s) {
    if (!e || !s)
        return;
    *s = e->stats;
    s->ast_nodes = e->nn;
    s->judgements = e->nj;
    s->contexts = e->nc;
    s->reserved_bytes = sizeof(*e) + (size_t)e->cn * sizeof(node) +
                        (size_t)e->cj * sizeof(judgement) + (size_t)e->cc * sizeof(context) +
                        (e->nt.cap + e->jt.cap + e->ct.cap) * sizeof(slot) +
                        e->cache_cap * sizeof(inference_cache) + e->map_cap * sizeof(map_cache);
}
bool tt_judgement(const tt_engine *e, tt_id id, tt_judgement_view *v) {
    if (!e || !id || id > e->nj || !v)
        return false;
    judgement j = e->judgements[id];
    *v =
        (tt_judgement_view){j.expr, j.type, set_count(e, j.set), (tt_opcode)j.op, j.highlight != 0};
    return true;
}
static const char *names[] = {
    "?",       "Axiom",   "CRef",  "UCRef",     "VRef",   "DRef",     "U",      "UUOmega",
    "UUKappa", "Void",    "Unit",  "Singleton", "Nat",    "ZN",       "SN",     "Lambda",
    "Ap",      "Pi",      "Sigma", "Tuple",     "Sum",    "Eq",       "Inl",    "Inr",
    "Refl",    "DefEq",   "W",     "WSup",      "IndNat", "IndSigma", "IndSum", "IndEq",
    "IndVoid", "IndUnit", "IndW",  "Temp",      "Set",    "Path"};
bool tt_ast(const tt_engine *e, tt_id id, tt_ast_view *v) {
    if (!e || !id || id > e->nn || !v)
        return false;
    node n = e->nodes[id];
    *v = (tt_ast_view){.kind = names[n.kind],
                       .parameter = n.param,
                       .tree_nodes = n.size,
                       .depth = n.depth,
                       .arity = n.arity};
    memcpy(v->children, n.ch, sizeof(n.ch));
    return true;
}
void tt_set_trace(tt_engine *e, FILE *f) {
    if (e)
        e->trace = f;
}
uint64_t fingerprint(const tt_engine *e, tt_id id) {
    if (!id)
        return 0;
    node n = e->nodes[id];
    uint64_t h = tt_mix(n.kind + ((uint64_t)n.param << 32));
    for (unsigned i = 0; i < n.arity; i++)
        h = tt_mix(h ^ fingerprint(e, n.ch[i]));
    return h;
}
static void print_node(const tt_engine *e, tt_id id, FILE *f, unsigned depth) {
    if (!id || id > e->nn) {
        fputs("?", f);
        return;
    }
    node n = e->nodes[id];
    fprintf(f, "%s", names[n.kind]);
    if (depth > 32) {
        fputs("(...) ", f);
        return;
    }
    if (n.kind <= N_U || n.kind == N_Temp)
        fprintf(f, "[%u]", n.param);
    if (n.arity) {
        fputc('(', f);
        for (unsigned i = 0; i < n.arity; i++) {
            if (i)
                fputs(", ", f);
            print_node(e, n.ch[i], f, depth + 1);
        }
        fputc(')', f);
    }
}
void tt_print_judgement(const tt_engine *e, tt_id id, FILE *f) {
    if (!e || !id || id > e->nj || !f)
        return;
    judgement j = e->judgements[id];
    fprintf(f, "[%u assumptions] |- ", set_count(e, j.set));
    print_node(e, j.expr, f, 0);
    fputs(" : ", f);
    print_node(e, j.type, f, 0);
    fputc('\n', f);
}
