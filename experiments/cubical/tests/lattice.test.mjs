import test from "node:test";
import assert from "node:assert/strict";
import { interval as I, face as F } from "../lattice.mjs";
const i = I.variable("i"), j = I.variable("j"), ni = I.reverse(i);
test("the interval is De Morgan, not Boolean", () => {
  assert(!I.equal(I.meet(i, ni), I.zero));
  assert(!I.equal(I.join(i, ni), I.one));
  assert(I.equal(I.reverse(I.reverse(i)), i));
  assert(I.equal(I.reverse(I.meet(i, j)), I.join(ni, I.reverse(j))));
});
test("endpoints are disjoint, but do not cover the interval", () => {
  const a = F.endpoint("i", 0), b = F.endpoint("i", 1);
  assert(F.equal(F.meet(a, b), F.bottom));
  assert(!F.entails(F.top, F.join(a, b)));
  assert(F.entails(F.bottom, a));
});
test("endpoint equations for compound interval expressions", () => {
  assert(F.equal(F.equalEndpoint(I.meet(i, j), 0), F.join(F.endpoint("i", 0), F.endpoint("j", 0))));
  assert(F.equal(F.equalEndpoint(I.meet(i, ni), 1), F.bottom));
  assert(F.equal(F.equalEndpoint(I.join(i, ni), 1), F.join(F.endpoint("i", 0), F.endpoint("i", 1))));
});
test("face substitution uses interval equations, not Boolean substitution", () => {
  const phi = F.join(F.endpoint("i", 0), F.endpoint("i", 1));
  assert(F.equal(F.substitute(phi, "i", I.meet(j, I.reverse(j))), F.join(F.endpoint("j", 0), F.endpoint("j", 1))));
  // r = j /\ ~j is always 0 on the endpoints, but not in the interior.
  // Therefore the disjunction above is NOT globally true.
});
test("lattice laws and substitution commute on every generated small term", () => {
  const base = [I.zero, I.one, i, ni, j, I.reverse(j)];
  const terms = [...base, ...base.flatMap(a => base.flatMap(b => [I.meet(a,b), I.join(a,b)]))];
  for (const a of terms) {
    assert(I.equal(I.reverse(I.reverse(a)), a));
    assert(I.equal(I.join(a, I.meet(a, j)), a));
    for (const endpoint of [I.zero, I.one]) {
      const sub = I.substitute(a, "i", endpoint);
      assert(I.equal(I.substitute(I.reverse(a), "i", endpoint), I.reverse(sub)));
      for (const e of [0,1]) assert(F.equal(F.substitute(F.equalEndpoint(a,e),"i",endpoint),F.equalEndpoint(sub,e)));
    }
  }
});
test("malformed terms and endpoints are rejected", () => {
  assert.throws(() => I.variable("bad:1"));
  assert.throws(() => I.normalize([["i:2"]]));
  assert.throws(() => F.endpoint("i", 2));
});
