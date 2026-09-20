import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { T, Checker } from "../experiments/cubical/core.mjs";
import { interval as I, face as F } from "../experiments/cubical/lattice.mjs";
import { identityEquivalence } from "../experiments/cubical/equivalence.mjs";
import { Translator } from "../experiments/cubical/translate.mjs";
import { readFile } from "node:fs/promises";

const module = await createCubical();
function session(t) {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  return kernel;
}

test("WASM independently checks functions and leaves reduction explicit", t => {
  const k = session(t), nat = k.term("Nat"), zero = k.term("Zero"), x = k.symbol("x");
  const body = k.term("Succ", 0, k.term("Var", x));
  const fn = k.term("Lam", x, nat, body), application = k.term("App", 0, fn, zero);
  assert.throws(() => k.normalize(application), /recent successful check/);
  const result = k.check(application, nat);
  assert.equal(k.node(result.expression).kind, "App");
  assert.equal(result.normal, 0);
  const normal = k.node(k.normalize(result.expression));
  assert.equal(normal.kind, "Succ");
  assert.equal(k.node(normal.children[0]).kind, "Zero");
  assert.throws(() => k.check(application, k.term("Unit")));
  assert.equal(module._cb_result(k.handle, 0), 0, "rejection must clear the previous certificate");
});

test("WASM checks contexts and path endpoints instead of trusting annotations", t => {
  const k = session(t), nat = k.term("Nat"), zero = k.term("Zero"), one = k.term("Succ", 0, zero);
  const x = k.symbol("x"), variable = k.term("Var", x);
  assert.throws(() => k.check(variable, nat));
  assert.equal(k.node(k.check(variable, nat, [[x, nat]]).type).kind, "Nat");
  assert.equal(k.node(variable).name, "x");
  assert.throws(() => k.check(variable, nat, [[x, zero]]));
  const path = k.term("PLam", 0, nat, zero);
  const good = k.term("Path", 0, nat, zero, zero), forged = k.term("Path", 0, nat, zero, one);
  assert.equal(k.node(k.check(path, good).type).kind, "Path");
  assert.throws(() => k.check(path, forged));
});

test("WASM retains both halves of dimension masks and the face/interval distinction", t => {
  const k = session(t), high = 1n << 63n, mixed = high | 1n;
  const interval = k.formula("interval", [[mixed, high]]);
  assert.deepEqual(k.inspectFormula(interval), { sort: "interval", clauses: [[mixed, high]] });
  const impossible = k.formula("face", [[mixed, high]]);
  assert.deepEqual(k.inspectFormula(impossible), { sort: "face", clauses: [] });
  assert.throws(() => k.formula("interval", [[1n << 64n, 0n]]), /64-bit/);
  const nat = k.term("Nat"), zero = k.term("Zero"), path = k.term("PLam", 0, nat, zero);
  const atOne = k.term("PApp", k.formula("interval", [[0n, 0n]]), path);
  const checked = k.check(atOne, nat);
  assert.equal(k.node(k.normalize(checked.expression)).kind, "Zero");
  assert.throws(() => k.check(k.term("PApp", impossible, path), nat));
});

test("WASM checks exponentially large Nat computations without building their unary values", t => {
  const k = session(t), nat = k.term("Nat"), zero = k.term("Zero");
  const n = k.symbol("n"), p = k.symbol("p"), ih = k.symbol("ih");
  const motive = k.term("Lam", n, nat, nat);
  const step = k.term("Lam", p, nat, k.term("Lam", ih, nat,
    k.term("Succ", 0, k.term("Succ", 0, k.term("Var", ih)))));
  const twice = k.term("Lam", n, nat, k.term("NatRec", 0, motive, zero, step, k.term("Var", n)));
  let large = k.term("Succ", 0, zero);
  for (let i = 0; i < 22; i++) large = k.term("App", 0, twice, large);
  const checked = k.check(large, nat);
  assert.equal(checked.normal, 0);
  assert.ok(checked.arenaNodes < 20000, JSON.stringify(checked));
  assert.ok(checked.arenaBytes < 2 * 1024 * 1024, JSON.stringify(checked));
  const ignored = k.term("App", 0, k.term("Lam", k.symbol("unused"), nat, zero), large);
  const ignoredChecked = k.check(ignored, nat);
  assert.equal(k.node(k.normalize(ignoredChecked.expression)).kind, "Zero", "a discarded argument must not be evaluated");
});

test("disposed WASM sessions cannot accidentally access a new session", t => {
  const old = session(t), token = old.handle;
  old.dispose();
  const next = session(t);
  assert.notEqual(next.handle, token);
  assert.equal(module._cb_check(token, 1, 0), 0);
  assert.throws(() => old.term("Nat"), /disposed/);
});

test("named syntax preserves path binders and sharing across WASM checks", t => {
  const k = session(t), syntax = new CubicalSyntax(k), reference = new Checker();
  const pt = T.path("i", T.nat, T.zero, T.zero), p = T.variable("p");
  const term = T.lam("p", pt, T.line("j", T.nat, T.at(p, I.reverse(I.variable("j")))));
  const checked = syntax.check(term);
  const checkedType = reference.verify(checked.type).term;
  assert.ok(reference.equal(reference.verify(term).type, checkedType));
  assert.equal(syntax.encode(term), syntax.encode(term));
  const roundTrip = syntax.check(checked.term, checked.type);
  assert.ok(reference.equal(reference.verify(roundTrip.type).term, checkedType));
  assert.throws(() => { term.name = "changed"; }, TypeError);
});

test("the actual W binary source checks entirely in cubical WASM", async t => {
  const syntax = new CubicalSyntax(session(t));
  const nativeCheck = (term, expected, context) => {
    try { return { ok: true, ...syntax.check(term, expected, context) }; }
    catch (error) { return { ok: false, error: error.message }; }
  };
  const source = await readFile(new URL("../web/proofs/binary_naturals.proof", import.meta.url), "utf8");
  const result = new Translator({ normalize: false, nativeCheck }).translate(source);
  assert.equal(result.declarations.length, 13);
  for (const declaration of result.declarations)
    assert.equal(declaration.status, "checked-native-cubical", `${declaration.name}: ${declaration.reason}`);
  const bad = new Translator({ normalize: false, nativeCheck }).translate(
    "theorem bad_binary_literal : 0b110 = 0b111 { exact refl(0b110); }", result.env);
  assert.equal(bad.declarations[0].status, "not-translated");
});

test("cubical WASM computes transport through Glue without a univalence axiom", t => {
  const k = session(t), syntax = new CubicalSyntax(k), e = identityEquivalence(T.nat);
  const ua = T.line("ua", T.universe(0), T.glueType(T.nat, [
    { face: F.endpoint("ua", 0), type: T.nat, equiv: e },
    { face: F.endpoint("ua", 1), type: T.nat, equiv: e },
  ]));
  syntax.check(ua, T.path("i", T.universe(0), T.nat, T.nat));
  const moved = T.comp("j", T.at(ua, I.variable("j")), [], T.succ(T.zero));
  const checked = syntax.check(moved, T.nat);
  assert.deepEqual(syntax.decode(k.normalize(checked.expression)), T.succ(T.zero));
  const forged = T.glueType(T.nat, [{ face: F.top, type: T.nat, equiv: T.lam("x", T.nat, T.variable("x")) }]);
  assert.throws(() => syntax.check(forged), /Type mismatch/);
});

test("native elaboration checks all manual factorial sources while retaining checked definitions", async t => {
  const k = session(t), checker = new NativeCubicalElaborator(k);
  const translator = new Translator({ normalize: false, checker });
  let env = new Map(), last;
  for (const name of ["binary_naturals", "binary_arithmetic", "binary_induction", "radix_naturals", "radix_arithmetic", "radix_factorial"]) {
    const source = await readFile(new URL(`../web/proofs/${name}.proof`, import.meta.url), "utf8");
    const result = translator.translate(source, env);
    env = result.env;
    for (const declaration of result.declarations) {
      assert.equal(declaration.status, "checked-native-cubical", `${declaration.name}: ${declaration.reason}`);
      assert.equal(env.get(declaration.name).tag, "DefRef");
      last = declaration.native;
    }
  }
  for (const name of ["binary_factorial_ten", "radix_factorial_ten_base_two", "radix_factorial_ten_base_ten"]) {
    const reference = k.definitions.get(name), definition = k.definition(reference);
    assert.equal(k.node(reference).kind, "DefRef");
    k.check(reference, definition.type);
  }
  assert.ok(last.arenaNodes < 500000, JSON.stringify(last));
  assert.ok(last.arenaBytes < 32 * 1024 * 1024, JSON.stringify(last));
  const bad = translator.translate("theorem wrong_factorial : binary_factorial(3) = 0b111 { exact refl(0b111); }", env);
  assert.equal(bad.declarations[0].status, "not-translated");
  assert.equal(k.definitions.has("wrong_factorial"), false);
});
