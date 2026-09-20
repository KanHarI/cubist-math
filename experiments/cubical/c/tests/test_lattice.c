#include "cubical.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    cc_formula i, reversed, meet, face, other;
    cc_init(&i, CC_INTERVAL); cc_init(&reversed, CC_INTERVAL); cc_init(&meet, CC_INTERVAL);
    cc_init(&face, CC_FACE); cc_init(&other, CC_FACE);
    assert(cc_generator(&i, 63, true) == CC_OK);
    assert(cc_reverse(&reversed, &i) == CC_OK);
    assert(cc_meet(&meet, &i, &reversed) == CC_OK && meet.length == 1);
    assert(cc_endpoint(&face, &meet, 1) == CC_OK && face.length == 0);
    assert(cc_endpoint(&face, &i, 0) == CC_OK);
    assert(cc_endpoint(&other, &i, 1) == CC_OK);
    assert(cc_join(&face, &face, &other) == CC_OK);
    assert(cc_one(&other) == CC_OK);
    bool entails = true;
    assert(cc_face_entails(&other, &face, &entails) == CC_OK && !entails);
    assert(cc_face_forall(&other, 63, &face) == CC_OK && other.length == 0);
    assert(cc_face_forall(&face, 63, &face) == CC_OK && face.length == 0);
    assert(cc_one(&other) == CC_OK);
    assert(cc_face_forall(&other, 0, &other) == CC_OK && other.length == 1);
    assert(cc_face_forall(&other, 64, &other) == CC_BAD_INPUT);
    assert(cc_face_forall(&other, 0, &i) == CC_BAD_INPUT);
    assert(cc_generator(&i, 64, true) == CC_BAD_INPUT);
    assert(i.length == 1 && i.clauses[0].positive == (UINT64_C(1) << 63));
    assert(cc_endpoint(&face, &i, 2) == CC_BAD_INPUT);
    assert(cc_join(&i, &i, &face) == CC_BAD_INPUT);
    assert(cc_face_entails(&i, &face, &entails) == CC_BAD_INPUT);
    assert(cc_reverse(&i, &i) == CC_OK && cc_equal(&i, &reversed));
    assert(cc_interval_substitute(&i, &i, 63, &reversed) == CC_OK);
    assert(i.clauses[0].positive == (UINT64_C(1) << 63));
    cc_clear(&i); cc_clear(&reversed); cc_clear(&meet); cc_clear(&face); cc_clear(&other);
    puts("Native interval/face invariants passed.");
    return 0;
}
