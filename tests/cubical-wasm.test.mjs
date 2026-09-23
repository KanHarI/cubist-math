import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { T, Checker } from "../lib/cubical/core.mjs";
import { interval as I, face as F } from "../lib/cubical/lattice.mjs";
import { identityEquivalence } from "../lib/cubical/equivalence.mjs";
import { Translator } from "../lib/cubical/translate.mjs";
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
  const source = await readFile(new URL("../web/proofs/binary_naturals.cubist", import.meta.url), "utf8");
  const result = new Translator({ normalize: false, nativeCheck }).translate(source);
  assert.equal(result.declarations.length, 13);
  for (const declaration of result.declarations)
    assert.equal(declaration.status, "checked-native-cubical", `${declaration.name}: ${declaration.reason}`);
  const bad = new Translator({ normalize: false, nativeCheck }).translate(
    "def bad_binary_literal : 0b110 = 0b111 { exact refl(0b110); }", result.env);
  assert.equal(bad.declarations[0].status, "not-translated");
});

test("dependent pair induction checks its motive and both branch arguments natively", t => {
  const k = session(t), checker = new NativeCubicalElaborator(k);
  const translator = new Translator({ normalize: false, checker });
  const result = translator.translate(`
    def second(A : U0, B : A -> U0, p : (exists x : A, B(x))) =
      pair_induction((fun (q : (exists x : A, B(x))) => B(unpack q as (a, b) return A { a; })),
        (fun (a : A) => fun (b : B(a)) => b), p);
    def wrong(p : Nat and Nat) = pair_induction(
      (fun (q : Nat and Nat) => Nat), (fun (a : Nat) => fun (b : Unit) => a), p);
  `);
  assert.equal(result.declarations[0].status, "checked-native-cubical", result.declarations[0].reason);
  assert.equal(result.declarations[1].status, "not-translated");
  assert.equal(k.definitions.has("wrong"), false);
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
    const source = await readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");
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
  const bad = translator.translate("def wrong_factorial : binary_factorial(3) = 0b111 { exact refl(0b111); }", env);
  assert.equal(bad.declarations[0].status, "not-translated");
  assert.equal(k.definitions.has("wrong_factorial"), false);
});

test("the existing Nat factorial theorem checks cubically without a million-successor expression", async t => {
  const k = session(t), checker = new NativeCubicalElaborator(k);
  const translator = new Translator({ normalize: false, checker });
  let env = new Map(), theorem;
  // The full generic equivalence API is not used by this compatibility proof.
  // Those separate declarations are explicitly rejected as untranslated;
  // no assumptions are registered in their place.
  for (const name of ["primes", "binary_naturals", "binary_arithmetic", "binary_induction", "binary_equivalence", "binary_arithmetic_correct"]) {
    const source = await readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");
    const result = translator.translate(source, env);
    env = result.env;
    for (const d of result.declarations) {
      if (["binary_nat_equiv", "nat_binary_equiv"].includes(d.name)) {
        assert.equal(d.status, "not-translated");
        assert.equal(k.definitions.has(d.name), false);
      } else assert.equal(d.status, "checked-native-cubical", `${d.name}: ${d.reason}`);
      if (d.name === "factorial_ten_from_binary") theorem = d;
    }
  }
  assert.ok(theorem);
  const { arenaNodes, arenaBytes } = theorem.native;
  assert.ok(arenaNodes < 1000000, JSON.stringify(theorem.native));
  assert.ok(arenaBytes < 64 * 1024 * 1024, JSON.stringify(theorem.native));
  const lengths = new Map();
  let maximum = 0;
  for (let id = 1; id <= arenaNodes; id++) {
    const node = k.node(id);
    if (node.kind === "Zero") lengths.set(id, 0);
    if (node.kind === "Succ" && lengths.has(node.children[0])) {
      const length = lengths.get(node.children[0]) + 1;
      lengths.set(id, length);
      maximum = Math.max(maximum, length);
    }
  }
  assert.equal(maximum, 10);
  const signature = k.definition(k.definitions.get("factorial_ten_from_binary")).type;
  const type = checker.syntax.decode(signature);
  assert.equal(type.tag, "Path");
  assert.equal(type.left.fn.name, "factorial");
  assert.equal(type.right.name, "nat_3628800");
});

test("open cubes check dependent contexts and preserve dimension names across decoding", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  const dimensions = new Map([["i", 63]]);
  const family = T.path("j", T.universe(0), T.nat, T.nat);
  const atI = T.at(T.variable("family"), I.variable("i"));
  const context = [["family", family], ["x", atI]];
  const checked = syntax.check(T.variable("x"), atI, context, dimensions);
  assert.deepEqual(checked.type.arg, I.variable("i"));
  assert.equal(syntax.check(checked.term, checked.type, context, dimensions).type.tag, "PApp");
  assert.throws(() => syntax.check(T.variable("x"), atI, context), /Unbound cubical dimension/);
  const rawContext = context.map(([name, type]) => [k.symbol(name), syntax.encode(type, dimensions)]);
  assert.throws(() => k.check(syntax.encode(T.variable("x")), syntax.encode(atI, dimensions), rawContext, 1n));
  assert.throws(() => k.define("escaped", syntax.encode(T.variable("x")), syntax.encode(atI, dimensions)));
  assert.throws(() => syntax.check(T.zero, null, [], new Map([["i", 0], ["j", 0]])), /distinct/);
  // A user name resembling the decoder's generated binder must not be captured.
  const collision = new Map([["d0", 63]]);
  const line = T.line("j", T.nat, T.at(T.variable("p"), I.variable("d0")));
  const decoded = syntax.check(line, null, [["p", T.path("k", T.nat, T.zero, T.zero)]], collision).term;
  assert.notEqual(decoded.dim, "d0");
  assert.deepEqual(decoded.body.arg, I.variable("d0"));
  syntax.check(decoded, null, [["p", T.path("k", T.nat, T.zero, T.zero)]], collision);
});

test("Cubist expresses cubical paths, composition and pushout induction with checked boundaries", async t => {
  const kernel = session(t), checker = new NativeCubicalElaborator(kernel);
  const translator = new Translator({ checker, normalize: false });
  const source = await readFile(new URL("../web/proofs/cubical_paths.cubist", import.meta.url), "utf8");
  const library = translator.translate(await readFile(new URL("../web/proofs/suspension_types.cubist", import.meta.url), "utf8"));
  assert.ok(library.declarations.every(d => d.status === "checked-native-cubical"));
  const result = translator.translate(source, library.env);
  assert.deepEqual(result.declarations.filter(d => d.status !== "checked-native-cubical"), []);
  assert.equal(result.declarations.length, 15);
  const invalid = translator.translate(`
    def escaped = path(fun (i : Interval) => Nat, fun (i : Interval) => i);
    def wrong : 0 = 1 { exact path(fun (i : Interval) => Nat, fun (i : Interval) => 0); }
    def malformed = comp(fun (i : Interval) => Nat, 0, face(i, 0, fun (j : Interval) => 0));
    def bad_bridge = pushout_induction(fun (p : Susp(Unit)) => Nat,
      fun (a : Unit) => 0, fun (b : Unit) => 1,
      fun (a : Unit) => refl(0), push_left(Susp(Unit), tt));
  `, result.env);
  assert.ok(invalid.declarations.every(d => d.status === "not-translated"), JSON.stringify(invalid.declarations));
  assert.equal(checker.dimensions.size, 0, "failed elaboration must restore the outer cube");
});

test("WASM round trips pushout boxes and corrected transport across changing maps", async t => {
  const { pushout, suspension, north } = await import("../lib/cubical/pushouts.mjs");
  const k = session(t), syntax = new CubicalSyntax(k);
  const C = suspension(T.unit), g = T.lam("x", T.unit, T.point);
  const family = r => pushout(T.unit, C, T.unit, T.lam("x", T.unit, T.pushPath(C, T.point, r)), g);
  const old = family(I.zero), last = family(I.one);
  const source = T.pushPath(old, T.point, I.variable("r"));
  const moved = T.line("r", last, T.trans("i", family(I.variable("i")), F.bottom, source));
  const left = T.pushLeft(last, T.comp("i", C, [], north(T.unit))), right = T.pushRight(last, T.point);
  const expected = T.path("r", last, left, right);
  const checked = syntax.check(moved, expected);
  const normal = syntax.decode(k.normalize(checked.expression));
  assert.equal(normal.body.tag, "HComp");
  syntax.check(normal, expected);
  syntax.check(checked.term, checked.type);
  assert.throws(() => syntax.check(T.line("r", last, T.pushPath(last, T.point, I.variable("r"))), expected));
  assert.throws(() => syntax.check(T.trans("i", family(I.variable("i")), F.top, T.pushLeft(old, north(T.unit))), last));
});

test("source-defined suspension induction uses a proved PathP bridge", async t => {
  const kernel = session(t), checker = new NativeCubicalElaborator(kernel);
  const translator = new Translator({ checker, normalize: false });
  const library = translator.translate(await readFile(new URL("../web/proofs/suspension_types.cubist", import.meta.url), "utf8"));
  assert.ok(library.declarations.every(d => d.status === "checked-native-cubical"));
  const result = translator.translate(`
    def C = Suspension(Unit);
    def family(p : C) = Unit;
    def unique(u : Unit) = unit_induction(fun (x : Unit) => x = tt, refl(tt), u);
    def boundary(a : Unit) = unique(transport(family, north(Unit), south(Unit), meridian(Unit, a), tt));
    def collapse(p : C) = suspension_induction(Unit, family, tt, tt, boundary, p);
    def point_beta : collapse(north(Unit)) = tt { exact refl(tt); }
    def bridge_beta(a : Unit) :
      apd(collapse, north(Unit), south(Unit), meridian(Unit, a)) = boundary(a) {
      exact suspension_meridian_beta(Unit, family, tt, tt, boundary, a);
    }
  `, library.env);
  assert.deepEqual(result.declarations.filter(d => d.status !== "checked-native-cubical"), []);
  assert.equal(result.declarations.length, 7);
});

test("native operations grow exhausted budgets without accepting invalid proofs", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  k.stepBudget = 1n; module._cb_step_budget(k.handle, 1, 0);
  const proof = T.line("i", T.nat, T.zero);
  syntax.check(proof, T.path("j", T.nat, T.zero, T.zero));
  assert.ok(k.stepBudget > 1n);
  const budget = k.stepBudget;
  assert.throws(() => syntax.check(proof, T.path("j", T.nat, T.zero, T.succ(T.zero))), /mismatch/);
  assert.ok(k.stepBudget >= budget);
  syntax.check(proof, T.path("j", T.nat, T.zero, T.zero));
});

test("browser dimension allocation reuses slots without capturing outer coordinates", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  let type = T.nat, point = T.zero;
  for (let i = 0; i < 100; i++) {
    const next = T.path(`constant${i}`, type, point, point);
    const reference = k.define(`level${i}`, syntax.encode(T.line(`constant${i}`, type, point)));
    point = syntax.decode(reference); type = next;
  }
  syntax.check(point, type);
  const p = T.variable("p"), P = T.path("i", T.nat, T.zero, T.succ(T.zero));
  const line = T.line("j", T.nat, T.at(p, I.variable("outside")));
  const checked = syntax.check(line, null, [["p", P]], new Map([["outside", 0]]));
  assert.throws(() => syntax.check(checked.term, null, [["p", P]]), /dimension/);
});
