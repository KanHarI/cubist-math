import test from "node:test";
import assert from "node:assert/strict";
import { T, freeNames, isTerm } from "../../web/translator/core.mjs";
import { freeDimensions } from "../../web/translator/dimension-slots.mjs";
import { displayFreeNames } from "../../web/translator/display-names.mjs";
import { interval as I } from "../../web/translator/lattice.mjs";

test("display analyses share term and universe binding while accepting display records", () => {
  const term = T.pi("x", T.variable("x"), T.levelPi("U",
    T.sigma("y", T.universe(T.variable("U")), T.app(T.variable("x"), T.variable("z")))));
  assert.deepEqual([...freeNames(term)].sort(), ["x", "z"]);
  const free = displayFreeNames();
  assert.deepEqual([...free(term)].sort(), ["x", "z"]);
  assert.deepEqual([...free({ tag: "Display", parts: [term, T.variable("extra")] })].sort(), ["extra", "x", "z"]);
  const reference = { tag: "Ref", name: "opaque" };
  assert.equal(isTerm(reference), false, "display/transport references do not become strict terms");
  assert.deepEqual([...free(reference)], []);
  assert.deepEqual([...freeDimensions(reference)], []);
});

test("display caches visit shared nodes once and stay local to a display pass", () => {
  let reads = 0;
  const leaf = { get child() { reads++; return T.variable("free"); } };
  let shared = leaf;
  for (let i = 0; i < 24; i++) shared = { left: shared, right: shared };
  assert.deepEqual([...displayFreeNames()(shared)], ["free"]);
  assert.equal(reads, 1);
  const record = { child: T.variable("before") };
  assert.deepEqual([...displayFreeNames()(record)], ["before"]);
  record.child = T.variable("after");
  assert.deepEqual([...displayFreeNames()(record)], ["after"]);
});

test("composition faces and homogeneous families stay outside their dimension binder", () => {
  const at = name => T.at(T.variable("p"), I.variable(name));
  const system = [{ face: I.variable("i"), term: at("i") }];
  assert.deepEqual([...freeDimensions(T.comp("i", at("i"), system, at("outer")))].sort(), ["i", "outer"]);
  assert.deepEqual([...freeDimensions(T.hcomp("i", at("i"), [], at("outer")))].sort(), ["i", "outer"]);
  assert.deepEqual([...freeDimensions(T.comp("i", at("i"), [], at("outer")))], ["outer"]);
});
