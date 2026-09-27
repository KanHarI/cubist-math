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
    /* Sixteen compact clauses reverse to 2^16 clauses. The native algebra
     * must report a limit without changing its output or doing that work. */
    cc_formula compact, left, right, pair, output, variable;
    cc_init(&compact, CC_INTERVAL); cc_init(&left, CC_INTERVAL);
    cc_init(&right, CC_INTERVAL); cc_init(&pair, CC_INTERVAL);
    cc_init(&output, CC_INTERVAL); cc_init(&variable, CC_INTERVAL);
    for (unsigned d = 0; d < 32; d += 2) {
        assert(cc_generator(&left, d, true) == CC_OK);
        assert(cc_generator(&right, d + 1, true) == CC_OK);
        assert(cc_meet(&pair, &left, &right) == CC_OK);
        assert(cc_join(&compact, &compact, &pair) == CC_OK);
    }
    assert(compact.length == 16);
    assert(cc_one(&output) == CC_OK);
    assert(cc_reverse(&output, &compact) == CC_LIMIT_EXCEEDED);
    assert(output.length == 1 && output.clauses[0].positive == 0 && output.clauses[0].negative == 0);
    assert(cc_generator(&variable, 63, true) == CC_OK);
    assert(cc_interval_substitute(&output, &variable, 63, &compact) == CC_OK);
    assert(cc_equal(&output, &compact));
    cc_formula positive_face, negative_face, direct_face, substituted_face;
    cc_init(&positive_face, CC_FACE); cc_init(&negative_face, CC_FACE);
    cc_init(&direct_face, CC_FACE); cc_init(&substituted_face, CC_FACE);
    assert(cc_endpoint(&direct_face, &compact, 1) == CC_OK && direct_face.length == 16);
    assert(cc_endpoint(&positive_face, &variable, 1) == CC_OK);
    assert(cc_face_substitute(&substituted_face, &positive_face, 63, &compact) == CC_OK);
    assert(cc_equal(&substituted_face, &direct_face));
    assert(cc_endpoint(&negative_face, &variable, 0) == CC_OK);
    assert(cc_one(&substituted_face) == CC_OK);
    assert(cc_face_substitute(&substituted_face, &negative_face, 63, &compact) == CC_LIMIT_EXCEEDED);
    assert(substituted_face.length == 1 && substituted_face.clauses[0].positive == 0);
    assert(cc_generator(&variable, 62, true) == CC_OK);
    assert(cc_interval_substitute(&output, &variable, 63, &compact) == CC_OK);
    assert(cc_equal(&output, &variable));
    assert(cc_endpoint(&positive_face, &variable, 1) == CC_OK);
    assert(cc_face_substitute(&substituted_face, &positive_face, 63, &compact) == CC_OK);
    assert(cc_equal(&substituted_face, &positive_face));
    cc_clear(&positive_face); cc_clear(&negative_face); cc_clear(&direct_face);
    cc_clear(&substituted_face);
    cc_clear(&compact); cc_clear(&left); cc_clear(&right); cc_clear(&pair);
    cc_clear(&output); cc_clear(&variable);
    puts("Native interval/face invariants passed.");
    return 0;
}
