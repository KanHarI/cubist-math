import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { reduceView, reductionStep, checkReduction, reductionAt, reductionRule, termAtPath } from "../web/cubical-reduction.mjs";
import { cubicalMathTree } from "../web/cubical-notation.mjs";

const module = await createCubical(), nat = { tag: "Nat" }, zero = { tag: "Zero" };
const variable = name => ({ tag: "Var", name });
const lambda = (name, body) => ({ tag: "Lam", name, domain: nat, body });
const app = (fn, arg) => ({ tag: "App", fn, arg });
const programFor = async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  await program.check("def N := Nat; def id(n : Nat) := n; def value := typed(N, id(0));", "demo");
  return program;
};

test("delta unfolds one closed kernel definition; beta leaves other definitions intact", async t => {
  const program = await programFor(t), before = program.inspect("demo__value");
  const original = structuredClone(before.expression);
  const delta = reduceView(program, before, "expression", "delta");
  assert.equal(delta.change.name, "demo__id");
  assert.equal(delta.view.expression.arg.fn.tag, "Lam");
  assert.deepEqual(before.expression, original);
  const beta = reduceView(program, before, "expression", "beta");
  assert.equal(beta.view.expression.fn.name, "demo__id");
  assert.equal(reduceView(program, beta.view, "expression", "beta").change, null);
  const unfolded = reduceView(program, beta.view, "expression", "delta");
  assert.equal(reduceView(program, unfolded.view, "expression", "beta").view.expression.tag, "Zero");
});

test("type delta and beta are retained even when the inferred type uses an alias", async t => {
  const program = await programFor(t), original = program.inspect("demo__value");
  const delta = reduceView(program, original, "type", "delta");
  assert.deepEqual(delta.view.type, nat);
  assert.deepEqual(delta.view.expression, original.expression);
  const appliedType = app({ tag: "Lam", name: "A", domain: { tag: "U", level: 0 }, body: variable("A") }, nat);
  const beta = reduceView(program, { ...original, type: appliedType }, "type", "beta");
  assert.deepEqual(beta.view.type, nat);
  assert.equal(reduceView(program, beta.view, "type", "delta").change, null);
});

test("reduction must preserve definitional equality, not just inhabitation", async t => {
  const program = await programFor(t), original = program.inspect("demo__value");
  assert.throws(() => checkReduction(program, original, "expression", { tag: "Succ", value: zero }), /mismatch/i);
  assert.throws(() => checkReduction(program, original, "type", { tag: "Unit" }), /mismatch/i);
});

test("term beta avoids capture and preserves named definitions under lambdas", async t => {
  const program = await programFor(t);
  const term = app(lambda("x", lambda("y", variable("x"))), variable("y"));
  const view = { expression: term, type: { tag: "Pi", name: "z", domain: nat, body: nat },
    context: [{ name: "y", type: nat }], dimensions: [] };
  const result = reduceView(program, view, "expression", "beta");
  assert.notEqual(result.view.expression.name, "y");
  assert.equal(result.view.expression.body.name, "y");
  const named = app(lambda("x", app({ tag: "DefRef", name: "demo__id" }, variable("x"))), zero);
  assert.equal(reductionStep(named, "beta").term.fn.tag, "DefRef");
});

test("beta avoids free interval capture and evaluates path application in its cube", async t => {
  const program = await programFor(t);
  const pType = { tag: "Path", dim: "j", family: nat, left: zero, right: zero };
  const argument = { tag: "PApp", path: variable("p"), arg: [["i:1"]] };
  const term = app(lambda("x", { tag: "PLam", dim: "i", family: nat, body: variable("x") }), argument);
  const view = { expression: term, type: { tag: "Path", dim: "k", family: nat, left: argument, right: argument },
    context: [{ name: "p", type: pType }], dimensions: [["i", 0]] };
  const reduced = reduceView(program, view, "expression", "beta").view;
  assert.notEqual(reduced.expression.dim, "i");
  assert.deepEqual(reduced.expression.body.arg, [["i:1"]]);
  const pathApp = { tag: "PApp", path: { tag: "PLam", dim: "j", family: nat,
    body: { tag: "PApp", path: variable("p"), arg: [["j:1"]] } }, arg: [["i:1"]] };
  const result = reduceView(program, { ...view, expression: pathApp, type: nat }, "expression", "beta");
  assert.deepEqual(result.view.expression.arg, [["i:1"]]);
});

test("delta retains explicit assumption arguments rather than opening an unbound body", async t => {
  const program = await programFor(t);
  await program.check("def Mere(A : U1) := Truncate(U1, A);", "truncation");
  const before = program.inspect("truncation__Mere");
  const view = { ...before, expression: app({ tag: "DefRef", name: "truncation__Mere" }, variable(before.context[0].name)) };
  const reduced = reduceView(program, view, "expression", "delta");
  assert.equal(reduced.view.expression.fn.tag, "Lam");
  assert.deepEqual(reduced.view.context, view.context);
});

test("selecting a shared occurrence reduces only that occurrence", async t => {
  const program = await programFor(t), view = program.inspect("demo__value");
  const ref = { tag: "DefRef", name: "demo__id" };
  const expression = app(ref, app(ref, zero));
  const delta = reduceView(program, { ...view, expression }, "expression", "delta", ["arg", "fn"]);
  assert.equal(delta.view.expression.fn.tag, "DefRef");
  assert.equal(delta.view.expression.arg.fn.tag, "Lam");
  const beta = reduceView(program, delta.view, "expression", "beta", ["arg"]);
  assert.deepEqual(beta.view.expression, app(ref, zero));
  assert.throws(() => reductionAt(expression, "beta", ["fn"]), /does not support/);
  assert.throws(() => reductionAt(expression, "delta", ["missing"]), /Invalid reduction location/);
});

test("selection notation exposes every occurrence, including annotations and inner applications", () => {
  const shared = app(lambda("x", variable("x")), zero);
  const pair = { tag: "Pair", as: { tag: "DefRef", name: "PairType" }, first: shared, second: shared };
  const term = app(lambda("p", variable("p")), pair);
  const tree = cubicalMathTree(term, {}, 5000, { paths: true });
  const paths = [];
  const walk = node => {
    if (!node || typeof node !== "object") return;
    if (node.sourcePath && reductionRule(termAtPath(term, node.sourcePath), "beta")) paths.push(node.sourcePath);
    Object.values(node).forEach(walk);
  };
  walk(tree);
  assert.deepEqual(paths, [[], ["arg", "first"], ["arg", "second"]]);
  assert.deepEqual(tree.args[0].args[0].sourcePath, ["arg", "as"]);
  const nested = cubicalMathTree(app(shared, zero), {}, 5000, { paths: true });
  assert.deepEqual(nested.fn.sourcePath, ["fn"]);
});
