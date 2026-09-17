#include "internal.h"

#ifndef TT_TEST_CONSTANT_HASH
#error This test requires the constant-hash build of the entire library
#endif
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "Collision check failed: %s:%d: %s\n", __FILE__, __LINE__, #x);        \
            exit(1);                                                                               \
        }                                                                                          \
    } while (0)

int main(void) {
    tt_engine *e = tt_new(NULL);
    CHECK(e);
    tt_id nodes[1200], contexts[1200], judgements[1200];
    for (unsigned i = 0; i < 1200; ++i) {
        nodes[i] = leaf(e, N_U, i);
        CHECK(nodes[i] == i + 1);
        contexts[i] = save_context(e, (context){.type = nodes[i], .counter = i});
        judgements[i] = save_judgement(e, (judgement){.expr = nodes[i], .type = nodes[0]});
        CHECK(contexts[i] == i + 1 && judgements[i] == i + 1);
    }
    for (unsigned i = 0; i < 1200; ++i) {
        CHECK(leaf(e, N_U, i) == nodes[i]);
        CHECK(save_context(e, (context){.type = nodes[i], .counter = i}) == contexts[i]);
        CHECK(save_judgement(e, (judgement){.expr = nodes[i], .type = nodes[0]}) == judgements[i]);
    }
    for (size_t i = 0; i < e->nt.cap; ++i)
        if (e->nt.slots[i].id)
            CHECK(e->nt.slots[i].hash == 0);
    uint32_t mark = e->nn;
    for (unsigned i = 0; i < 400; ++i)
        CHECK(make2(e, N_Ap, nodes[i], nodes[i + 1]));
    rollback_nodes(e, mark);
    CHECK(e->nn == mark && e->nt.used == mark);
    for (unsigned i = 0; i < 1200; ++i)
        CHECK(leaf(e, N_U, i) == nodes[i]);
    for (unsigned i = 0; i < 400; ++i) {
        tt_id a = make2(e, N_Ap, nodes[i], nodes[i + 1]);
        tt_id b = make2(e, N_Ap, nodes[i + 1], nodes[i]);
        CHECK(a && b && a != b);
        CHECK(make2(e, N_Ap, nodes[i], nodes[i + 1]) == a);
    }
    tt_free(e);
    e = tt_new(NULL);
    CHECK(e);
    tt_id unit, one, zero, out;
    CHECK(tt_apply(e, TT_UnitForm, NULL, 0, 0, NULL, 0, &unit) == TT_OK);
    CHECK(tt_apply(e, TT_UnitIntro, NULL, 0, 0, NULL, 0, &one) == TT_OK);
    CHECK(tt_apply(e, TT_NatIntroZ, NULL, 0, 0, NULL, 0, &zero) == TT_OK);
    CHECK(tt_verify(e, unit, one));
    CHECK(!tt_verify(e, unit, zero));
    CHECK(tt_apply(e, TT_NatIntroS, &one, 1, 0, NULL, 0, &out) == TT_INVALID);
    CHECK(tt_apply(e, TT_NatIntroS, &zero, 1, 0, NULL, 0, &out) == TT_OK);
    tt_free(e);
    puts("Constant-hash collisions: distinct keys, deduplication, growth, rollback, and inference "
         "checks passed");
    return 0;
}
