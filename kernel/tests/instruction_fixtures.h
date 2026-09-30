/* Optional snapshots of successful typing/equality judgements and rejected
 * native requests. Definitions expand while their checkpoint is alive.
 * This is test serialization, never an admission or conversion service. */
#include <inttypes.h>
#include <stdlib.h>

static FILE *fixture_file;
static void fixture_node(cc_term term);

static void fixture_formula(cc_formula_id id) {
    const cc_formula *formula = cc_kernel_get_formula(k, id);
    assert(formula);
    fprintf(fixture_file, "{\"sort\":%u,\"clauses\":[", (unsigned)formula->sort);
    for (size_t c = 0; c < formula->length; ++c) {
        if (c) fputc(',', fixture_file);
        fprintf(fixture_file, "[\"%" PRIu64 "\",\"%" PRIu64 "\"]",
                formula->clauses[c].positive, formula->clauses[c].negative);
    }
    fputs("]}", fixture_file);
}

static void fixture_entry(cc_entry_id entry) {
    uint32_t symbol;
    cc_term type;
    bool dimension;
    assert(cc_kernel_entry(k, entry, &symbol, &type, &dimension, NULL));
    fprintf(fixture_file, "[%u,%s,", symbol, dimension ? "true" : "false");
    fixture_node(type);
    fputc(']', fixture_file);
}

static void fixture_node(cc_term term) {
    if (!term) { fputs("null", fixture_file); return; }
    cc_term_kind kind;
    uint32_t payload;
    cc_term children[4];
    assert(cc_kernel_node(k, term, &kind, &payload, children));
    if (kind == CC_DEFREF) {
        cc_term value;
        assert(cc_kernel_definition(k, term, NULL, &value, NULL));
        fixture_node(value);
        return;
    }
    fprintf(fixture_file, "[%u,", (unsigned)kind);
    if (kind == CC_PAPP || kind == CC_PUSH_PATH || kind == CC_TUBE || kind == CC_GLUE_SYSTEM) {
        fixture_formula(payload);
    } else fprintf(fixture_file, "%u", payload);
    fputs(",[", fixture_file);
    for (unsigned c = 0; c < 4; ++c) {
        if (c) fputc(',', fixture_file);
        fixture_node(children[c]);
    }
    fputs("]]", fixture_file);
}

static void fixture_fact(uint32_t id, int line) {
    cc_judgement_info info;
    assert(cc_kernel_judgement(k, id, &info));
    fprintf(fixture_file, "{\"line\":%d,\"kind\":%u,\"rule\":%u,\"context\":[", line, info.kind, (unsigned)info.rule);
    for (size_t c = 0; ; ++c) {
        cc_entry_id entry = cc_kernel_judgement_context(k, id, c);
        if (!entry) break;
        uint32_t symbol;
        cc_term type;
        bool dimension;
        assert(cc_kernel_entry(k, entry, &symbol, &type, &dimension, NULL));
        if (c) fputc(',', fixture_file);
        fprintf(fixture_file, "[%u,%s,", symbol, dimension ? "true" : "false");
        fixture_node(type);
        fputc(']', fixture_file);
    }
    fputs("],\"term\":", fixture_file); fixture_node(info.term);
    fputs(",\"type\":", fixture_file); fixture_node(info.type);
    fputs(",\"other\":", fixture_file); fixture_node(info.other);
    if (info.kind == 3) {
        fputs(",\"inputs\":[", fixture_file);
        for (unsigned slot = 0; slot < 4; ++slot) {
            if (slot) fputc(',', fixture_file);
            if (info.premise[slot]) fixture_fact(info.premise[slot], line);
            else fputs("null", fixture_file);
        }
        fputs("],\"entry\":", fixture_file);
        if (info.entry) fixture_entry(info.entry);
        else fputs("null", fixture_file);
        fprintf(fixture_file, ",\"operand\":%u,\"face\":", info.operand[0]);
        if (info.rule == CC_INSTR_SYSTEM_TUBE || info.rule == CC_INSTR_GLUE_PIECE)
            fixture_formula(info.operand[0]);
        else fputs("null", fixture_file);
    }
    fputc('}', fixture_file);
}

static void fixture_judgement(uint32_t id, const char *request, int line) {
    if (!fixture_file || strncmp(request, "cc_instr_extend(", 16) == 0 ||
        strncmp(request, "cc_instr_dimension(", 19) == 0 || strncmp(request, "cc_instr_level(", 15) == 0)
        return;
    cc_judgement_info info;
    if (!cc_kernel_judgement(k, id, &info) || (info.kind != 1 && info.kind != 2)) return;
    fixture_fact(id, line);
    fputc('\n', fixture_file);
}

/* The rejected request itself matters: a transport's malformed clause list
 * cannot be represented by an ill-typed Trans term. Keep its input system. */
static void fixture_refusal(const char *operation, const cc_judgement_id *arguments,
                            size_t count, cc_formula_id face, cc_entry_id entry, uint32_t operand, int line) {
    if (!fixture_file) return;
    fprintf(fixture_file, "{\"operation\":\"%s\",\"line\":%d,\"arguments\":[", operation, line);
    for (size_t index = 0; index < count; ++index) {
        if (index) fputc(',', fixture_file);
        if (arguments[index]) fixture_fact(arguments[index], line);
        else fputs("null", fixture_file);
    }
    fputs("],\"face\":", fixture_file);
    if (face) fixture_formula(face);
    else fputs("null", fixture_file);
    fputs(",\"entry\":", fixture_file);
    if (entry) fixture_entry(entry);
    else fputs("null", fixture_file);
    fprintf(fixture_file, ",\"operand\":%u", operand);
    fputs("}\n", fixture_file);
}

static void fixture_unadmitted(cc_term reference, int line) {
    if (!fixture_file) return;
    cc_term type, value;
    assert(cc_kernel_definition(k, reference, NULL, &value, &type));
    fprintf(fixture_file, "{\"operation\":\"lookup\",\"line\":%d,\"arguments\":[{\"kind\":1,\"context\":[],\"term\":", line);
    fixture_node(value);
    fputs(",\"type\":", fixture_file); fixture_node(type);
    fputs(",\"other\":null}],\"face\":null,\"entry\":null,\"operand\":0}\n", fixture_file);
}

static void fixture_closed_equality(cc_term term, cc_term type, cc_term other, int line) {
    if (!fixture_file) return;
    fprintf(fixture_file, "{\"line\":%d,\"kind\":2,\"rule\":0,\"context\":[],\"term\":", line);
    fixture_node(term);
    fputs(",\"type\":", fixture_file); fixture_node(type);
    fputs(",\"other\":", fixture_file); fixture_node(other);
    fputs("}\n", fixture_file);
}
