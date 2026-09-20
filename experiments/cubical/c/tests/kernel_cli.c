/* Machine-readable native test adapter. WASM callers use the same C API
 * directly, without this line protocol. Exactly one query is accepted:
 * F sort length (positive-mask negative-mask)*
 * N kind payload child0 child1 child2 child3
 * D symbol value-handle expected-type-handle (appends a term alias)
 * A symbol type-handle
 * Q term-handle expected-type-handle normalize-flag
 * Formula and term handles are logical 1-based aliases, independent of nodes
 * allocated internally while checking definitions. */
#include "cubical_kernel.h"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

static void formula(const cc_formula *f) {
    putchar('[');
    for (size_t i = 0; i < f->length; ++i) {
        if (i) putchar(',');
        putchar('[');
        bool comma = false;
        for (unsigned d = 0; d < CC_DIMENSIONS; ++d)
            for (unsigned end = 0; end < 2; ++end)
                if ((end ? f->clauses[i].positive : f->clauses[i].negative) & (UINT64_C(1) << d)) {
                    if (comma) putchar(',');
                    printf("\"d%u:%u\"", d, end);
                    comma = true;
                }
        putchar(']');
    }
    putchar(']');
}

static void term(cc_kernel *k, cc_term t, unsigned depth);
static void field(cc_kernel *k, const char *name, cc_term t, unsigned depth) {
    printf(",\"%s\":", name);
    term(k, t, depth + 1);
}
static void term(cc_kernel *k, cc_term t, unsigned depth) {
    static const char *tags[] = {"", "U", "Var", "Pi", "Lam", "App", "Sigma", "Pair", "Fst", "Snd",
        "Nat", "Zero", "Succ", "NatRec", "Unit", "Point", "Path", "PLam", "PApp", "Comp", "Tube",
        "Void", "Abort", "W", "Sup", "WRec", "Sum", "Inl", "Inr", "SumRec", "UnitRec", "Glue", "GlueSystem", "GlueTerm", "Unglue", "Ref"};
    cc_term_kind kind;
    uint32_t payload;
    cc_term ch[4];
    if (depth > 1024 || !cc_kernel_node(k, t, &kind, &payload, ch)) {
        fputs("null", stdout);
        return;
    }
    printf("{\"tag\":\"%s\"", tags[kind]);
    if (kind == CC_U) printf(",\"level\":%u", payload);
    if (kind == CC_DEFREF) {
        uint32_t symbol;
        if (cc_kernel_definition(k, t, &symbol, NULL, NULL))
            printf(",\"name\":\"v%u\"", symbol);
    }
    if (kind == CC_VAR) printf(",\"name\":\"v%u\"", payload);
    if (kind == CC_PI || kind == CC_LAM || kind == CC_SIGMA || kind == CC_W) {
        printf(",\"name\":\"v%u\"", payload);
        field(k, "domain", ch[0], depth);
        field(k, "body", ch[1], depth);
    }
    if (kind == CC_APP) { field(k, "fn", ch[0], depth); field(k, "arg", ch[1], depth); }
    if (kind == CC_PAIR) { field(k, "as", ch[0], depth); field(k, "first", ch[1], depth); field(k, "second", ch[2], depth); }
    if (kind == CC_FST || kind == CC_SND) field(k, "pair", ch[0], depth);
    if (kind == CC_SUCC) field(k, "value", ch[0], depth);
    if (kind == CC_NATREC) { field(k, "motive", ch[0], depth); field(k, "zero", ch[1], depth); field(k, "step", ch[2], depth); field(k, "value", ch[3], depth); }
    if (kind == CC_PATH || kind == CC_PLAM || kind == CC_COMP) {
        printf(",\"dim\":\"d%u\"", payload);
        field(k, "family", ch[0], depth);
        if (kind == CC_PATH) { field(k, "left", ch[1], depth); field(k, "right", ch[2], depth); }
        if (kind == CC_PLAM) field(k, "body", ch[1], depth);
        if (kind == CC_COMP) {
            fputs(",\"system\":[", stdout);
            bool comma = false;
            for (cc_term tube = ch[1]; tube;) {
                cc_term_kind tube_kind; uint32_t face; cc_term data[4];
                if (!cc_kernel_node(k, tube, &tube_kind, &face, data) || tube_kind != CC_TUBE) break;
                if (comma) putchar(',');
                fputs("{\"face\":", stdout);
                formula(cc_kernel_get_formula(k, face));
                fputs(",\"term\":", stdout);
                term(k, data[0], depth + 1);
                putchar('}'); comma = true; tube = data[1];
            }
            putchar(']'); field(k, "base", ch[2], depth);
        }
    }
    if (kind == CC_PAPP) {
        field(k, "path", ch[0], depth);
        fputs(",\"arg\":", stdout);
        formula(cc_kernel_get_formula(k, payload));
        if (ch[1]) field(k, "pathType", ch[1], depth);
    }
    if (kind == CC_ABORT) { field(k, "as", ch[0], depth); field(k, "impossible", ch[1], depth); }
    if (kind == CC_SUP) { field(k, "as", ch[0], depth); field(k, "label", ch[1], depth); field(k, "children", ch[2], depth); }
    if (kind == CC_WREC) { field(k, "motive", ch[0], depth); field(k, "step", ch[1], depth); field(k, "value", ch[2], depth); }
    if (kind == CC_UNGLUE) { field(k, "as", ch[0], depth); field(k, "value", ch[1], depth); }
    if (kind == CC_GLUE || kind == CC_GLUE_TERM) {
        bool type = kind == CC_GLUE;
        if (!type) field(k, "as", ch[0], depth);
        field(k, "base", ch[type ? 0 : 1], depth);
        fputs(",\"system\":[", stdout);
        cc_term cursor = ch[type ? 1 : 2];
        bool comma = false;
        while (cursor) {
            cc_term_kind part_kind;
            uint32_t face;
            cc_term part[4];
            if (!cc_kernel_node(k, cursor, &part_kind, &face, part)) break;
            if (comma) putchar(',');
            fputs("{\"face\":", stdout);
            formula(cc_kernel_get_formula(k, face));
            field(k, type ? "type" : "term", part[0], depth);
            if (type) field(k, "equiv", part[1], depth);
            putchar('}');
            comma = true;
            cursor = part[type ? 2 : 1];
        }
        putchar(']');
    }
    if (kind == CC_SUM) { field(k, "left", ch[0], depth); field(k, "right", ch[1], depth); }
    if (kind == CC_INL || kind == CC_INR) { field(k, "as", ch[0], depth); field(k, "value", ch[1], depth); }
    if (kind == CC_SUMREC) {
        field(k, "motive", ch[0], depth);
        field(k, "left", ch[1], depth);
        field(k, "right", ch[2], depth);
        field(k, "value", ch[3], depth);
    }
    if (kind == CC_UNITREC) {
        field(k, "motive", ch[0], depth);
        field(k, "point", ch[1], depth);
        field(k, "value", ch[2], depth);
    }
    putchar('}');
}

typedef struct {
    uint32_t *items;
    size_t count, capacity;
} aliases;

static bool append_alias(aliases *table, uint32_t handle) {
    if (!handle)
        return false;
    if (table->count == table->capacity) {
        size_t capacity = table->capacity ? table->capacity * 2 : 256;
        if (capacity < table->capacity || capacity > SIZE_MAX / sizeof(uint32_t))
            return false;
        uint32_t *grown = realloc(table->items, capacity * sizeof *grown);
        if (!grown)
            return false;
        table->items = grown;
        table->capacity = capacity;
    }
    table->items[table->count++] = handle;
    return true;
}

static uint32_t resolve(const aliases *table, uint32_t alias) {
    return alias && alias <= table->count ? table->items[alias - 1] : 0;
}

int main(void) {
    cc_kernel *k = cc_kernel_new();
    if (!k) return 2;
    cc_assumption *assumptions = NULL;
    size_t count = 0;
    aliases terms = {0}, formulas = {0};
    char command;
    int status = 1;
    while (scanf(" %c", &command) == 1) {
        if (command == 'N') {
            unsigned kind, payload, a, b, c, d;
            if (scanf(" %u %u %u %u %u %u", &kind, &payload, &a, &b, &c, &d) != 6)
                break;
            if ((a && !resolve(&terms, a)) || (b && !resolve(&terms, b)) ||
                (c && !resolve(&terms, c)) || (d && !resolve(&terms, d)))
                break;
            if (kind == CC_PAPP || kind == CC_TUBE || kind == CC_GLUE_SYSTEM) {
                payload = resolve(&formulas, payload);
                if (!payload)
                    break;
            }
            cc_term value = cc_kernel_term(k, (cc_term_kind)kind, payload,
                resolve(&terms, a), resolve(&terms, b), resolve(&terms, c), resolve(&terms, d));
            if (!append_alias(&terms, value))
                break;
        } else if (command == 'D') {
            unsigned symbol, value, expected;
            if (scanf(" %u %u %u", &symbol, &value, &expected) != 3 ||
                !resolve(&terms, value) || (expected && !resolve(&terms, expected)))
                break;
            cc_term reference = cc_kernel_define(k, symbol, resolve(&terms, value), resolve(&terms, expected));
            if (!reference) {
                printf("{\"ok\":false,\"error\":\"%s\"}\n", cc_kernel_error(k));
                status = 0;
                break;
            }
            if (!append_alias(&terms, reference))
                break;
        } else if (command == 'F') {
            unsigned sort; size_t length;
            if (scanf(" %u %zu", &sort, &length) != 2 || sort > CC_FACE || length > 100000) break;
            cc_formula f;
            cc_init(&f, (cc_sort)sort);
            f.clauses = length ? calloc(length, sizeof *f.clauses) : NULL;
            if (length && !f.clauses) break;
            f.length = f.capacity = length;
            bool ok = true;
            for (size_t i = 0; i < length; ++i)
                if (scanf(" %" SCNu64 " %" SCNu64, &f.clauses[i].positive, &f.clauses[i].negative) != 2) { ok = false; break; }
            if (ok) ok = append_alias(&formulas, cc_kernel_formula(k, &f));
            cc_clear(&f);
            if (!ok) break;
        } else if (command == 'A') {
            unsigned symbol, type;
            if (scanf(" %u %u", &symbol, &type) != 2 || count > SIZE_MAX / sizeof *assumptions - 1) break;
            cc_assumption *grown = realloc(assumptions, (count + 1) * sizeof *assumptions);
            if (!grown) break;
            assumptions = grown;
            if (!resolve(&terms, type))
                break;
            assumptions[count++] = (cc_assumption){symbol, resolve(&terms, type)};
        } else if (command == 'Q') {
            unsigned value, expected, normalize;
            if (scanf(" %u %u %u", &value, &expected, &normalize) != 3) break;
            if (!resolve(&terms, value) || (expected && !resolve(&terms, expected)))
                break;
            value = resolve(&terms, value);
            expected = resolve(&terms, expected);
            cc_checked_result result;
            if (cc_kernel_check(k, value, expected, assumptions, count, &result)) {
                if (normalize) {
                    result.normal = cc_kernel_normalize(k, result.expression);
                    result.type = cc_kernel_normalize(k, result.type);
                    if (!result.normal || !result.type) {
                        printf("{\"ok\":false,\"error\":\"%s\"}\n", cc_kernel_error(k));
                        status = 0;
                        break;
                    }
                }
                fputs("{\"ok\":true,\"type\":", stdout); term(k, result.type, 0);
                fputs(",\"normal\":", stdout); term(k, normalize ? result.normal : result.expression, 0);
                printf(",\"arenaNodes\":%zu,\"arenaBytes\":%zu", result.arena_nodes, result.arena_bytes);
                printf(",\"checkingSteps\":%" PRIu64 ",\"reductionSteps\":%" PRIu64 "}\n", result.checking_steps, result.reduction_steps);
            } else printf("{\"ok\":false,\"error\":\"%s\"}\n", cc_kernel_error(k));
            status = 0;
            break;
        } else break;
    }
    if (status) fprintf(stderr, "Invalid native syntax request: %s\n", cc_kernel_error(k));
    free(terms.items);
    free(formulas.items);
    free(assumptions);
    cc_kernel_free(k);
    return status;
}
