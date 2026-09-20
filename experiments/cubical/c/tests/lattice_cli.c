/* Line-oriented test adapter, not a term/proof import format.
 * N expr; E0/E1 expr; SI dimension expr replacement;
 * SF dimension face-as-interval replacement; IMPL left right.
 * expr = 0 | 1 | (v n) | (not expr) | (and expr expr) | (or expr expr). */
#include "cubical.h"
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void spaces(const char **p) { while (isspace((unsigned char)**p)) ++*p; }
static bool token(const char **p, char *word, size_t capacity) {
    spaces(p); size_t n = 0;
    while (**p && !isspace((unsigned char)**p) && **p != '(' && **p != ')') {
        if (n + 1 >= capacity) return false;
        word[n++] = *(*p)++;
    }
    word[n] = '\0'; return n != 0;
}
static bool number(const char **p, unsigned *out) {
    char word[24], *end; if (!token(p, word, sizeof word)) return false;
    if (!isdigit((unsigned char)word[0])) return false;
    unsigned long value = strtoul(word, &end, 10);
    if (*end || value >= CC_DIMENSIONS) return false;
    *out = (unsigned)value; return true;
}
static bool expression(const char **p, cc_formula *out, unsigned depth) {
    if (depth > 128) return false;
    spaces(p);
    if (**p != '(') {
        char word[16]; if (!token(p, word, sizeof word)) return false;
        return !strcmp(word, "0") ? cc_zero(out) == CC_OK :
               !strcmp(word, "1") ? cc_one(out) == CC_OK : false;
    }
    ++*p; char op[16]; if (!token(p, op, sizeof op)) return false;
    cc_formula a, b; cc_init(&a, CC_INTERVAL); cc_init(&b, CC_INTERVAL);
    bool ok = false;
    if (!strcmp(op, "v")) { unsigned d; ok = number(p, &d) && cc_generator(out, d, true) == CC_OK; }
    else if (!strcmp(op, "not")) ok = expression(p, &a, depth + 1) && cc_reverse(out, &a) == CC_OK;
    else if (!strcmp(op, "and") || !strcmp(op, "or")) {
        ok = expression(p, &a, depth + 1) && expression(p, &b, depth + 1);
        if (ok) ok = (!strcmp(op, "and") ? cc_meet(out, &a, &b) : cc_join(out, &a, &b)) == CC_OK;
    }
    cc_clear(&a); cc_clear(&b); spaces(p);
    if (!ok || **p != ')') return false;
    ++*p; return true;
}
static void print_formula(const cc_formula *f) {
    putchar('[');
    for (size_t c = 0; c < f->length; ++c) {
        if (c) putchar(','); putchar('['); bool comma = false;
        for (unsigned d = 0; d < CC_DIMENSIONS; ++d) for (unsigned end = 0; end < 2; ++end) {
            uint64_t bit = UINT64_C(1) << d;
            if ((end ? f->clauses[c].positive : f->clauses[c].negative) & bit) {
                if (comma) putchar(','); printf("\"d%u:%u\"", d, end); comma = true;
            }
        }
        putchar(']');
    }
    puts("]");
}
int main(void) {
    static char line[1048576];
    while (fgets(line, sizeof line, stdin)) {
        const char *p = line; char command[16]; bool ok = token(&p, command, sizeof command), boolean = false, implication = false;
        cc_formula a, b, output, left, right;
        cc_init(&a, CC_INTERVAL); cc_init(&b, CC_INTERVAL); cc_init(&output, CC_INTERVAL);
        cc_init(&left, CC_FACE); cc_init(&right, CC_FACE);
        if (ok && (!strcmp(command, "SI") || !strcmp(command, "SF"))) {
            unsigned d; ok = number(&p, &d) && expression(&p, &a, 0) && expression(&p, &b, 0);
            if (ok && !strcmp(command, "SI")) ok = cc_interval_substitute(&output, &a, d, &b) == CC_OK;
            else if (ok) {
                cc_clear(&output); cc_init(&output, CC_FACE);
                ok = cc_endpoint(&left, &a, 1) == CC_OK && cc_face_substitute(&output, &left, d, &b) == CC_OK;
            }
        } else if (ok && !strcmp(command, "IMPL")) {
            implication = true;
            ok = expression(&p, &a, 0) && expression(&p, &b, 0) && cc_endpoint(&left, &a, 1) == CC_OK &&
                 cc_endpoint(&right, &b, 1) == CC_OK && cc_face_entails(&left, &right, &boolean) == CC_OK;
        } else if (ok && (!strcmp(command, "N") || !strcmp(command, "E0") || !strcmp(command, "E1"))) {
            ok = expression(&p, &a, 0);
            if (ok && !strcmp(command, "N")) ok = cc_copy(&output, &a) == CC_OK;
            else if (ok) {
                cc_clear(&output); cc_init(&output, CC_FACE);
                ok = cc_endpoint(&output, &a, command[1] == '1') == CC_OK;
            }
        } else ok = false;
        spaces(&p); ok = ok && !*p;
        if (ok) { if (implication) puts(boolean ? "true" : "false"); else print_formula(&output); }
        cc_clear(&a); cc_clear(&b); cc_clear(&output); cc_clear(&left); cc_clear(&right);
        if (!ok) { fputs("Invalid experimental lattice request.\n", stderr); return 1; }
    }
    return ferror(stdin) ? 1 : 0;
}
