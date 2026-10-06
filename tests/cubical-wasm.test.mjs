import "./fresh-build.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import { checkTestModule } from "./check-program.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel, KernelError } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { T } from "../web/translator/core.mjs";
import { interval as I, face as F } from "../web/translator/lattice.mjs";
import { identityEquivalence } from "../web/translator/equivalence.mjs";
import { Translator } from "../web/translator/translate.mjs";
import { Scope, SourceUnit } from "../web/translator/elaboration.mjs";
import { Goal, reflexivity } from "../web/translator/proof-goals.mjs";
import { abstractMotive } from "../web/translator/motives.mjs";
import { readFile } from "node:fs/promises";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { levelText, universeText } from "../web/cubical-levels.mjs";

const module = await createCubical();
const producerModule = module;
function session(t) {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  return kernel;
}
// Two points, the examples' small inductive type, and a function swapping them.
const two = T.sum(T.unit, T.unit), left = T.inl(two, T.point), right = T.inr(two, T.point);
const swap = x => T.sumrec(T.lam("_", two, two), T.lam("u", T.unit, right), T.lam("u", T.unit, left), x);
// The instruction kernel's check of a raw term, through the driver: the
// derived term and type, which normalize accepts.
function derive(k, raw, expected = 0, assumptions = [], mask = 0n) {
  const driver = new InstructionDriver(k), graph = driver.graph;
  const judgement = expected ? driver.check(raw, expected, assumptions, mask) : driver.infer(raw, assumptions, mask);
  const { term, type } = graph.judgement(judgement);
  (k.derivedHandles ??= new Set()).add(term).add(type);
  return { expression: term, type };
}
// The same for syntax with names and dimensions, as the elaborator checks it.
// Archive modules, each checked as a program's main module.
async function archive(t, ...names) {
  const program = new CubicalProgram(producerModule, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  for (const name of names) {
    const result = await program.check(await sourceReader()(name), name);
    assert.equal(result.complete, true, `${name}: ${JSON.stringify(result.gaps)}`);
  }
  return program;
}
const elaborate = (k, term, type = null, context = [], dimensions = new Map()) =>
  new NativeCubicalElaborator(k).checkSyntax(term, type, new Map(context), dimensions);

test("the kernel derives an application and leaves reduction explicit", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  const application = syntax.encode(T.app(T.lam("x", two, swap(T.variable("x"))), left));
  assert.throws(() => k.normalize(application), /an instruction derived/);
  const result = derive(k, application, syntax.encode(two));
  assert.equal(k.node(result.expression).kind, "App");
  assert.deepEqual(syntax.decode(k.normalize(result.expression)), right);
  assert.throws(() => derive(k, application, k.term("Unit")));
});

test("the kernel checks contexts and path endpoints instead of trusting annotations", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  const type = syntax.encode(two), l = syntax.encode(left), r = syntax.encode(right);
  const x = k.symbol("x"), variable = k.term("Var", x);
  assert.throws(() => derive(k, variable, type));
  assert.equal(k.node(derive(k, variable, type, [[x, type]]).type).kind, "Sum");
  assert.equal(k.node(variable).name, "x");
  assert.throws(() => derive(k, variable, type, [[x, l]]));
  const path = k.term("PLam", 0, type, l);
  const good = k.term("Path", 0, type, l, l), forged = k.term("Path", 0, type, l, r);
  assert.equal(k.node(derive(k, path, good).type).kind, "Path");
  assert.throws(() => derive(k, path, forged));
});

test("WASM retains both halves of dimension masks and the face/interval distinction", t => {
  const k = session(t), high = 1n << 63n, mixed = high | 1n;
  const interval = k.formula("interval", [[mixed, high]]);
  assert.deepEqual(k.inspectFormula(interval), { sort: "interval", clauses: [[mixed, high]] });
  const impossible = k.formula("face", [[mixed, high]]);
  assert.deepEqual(k.inspectFormula(impossible), { sort: "face", clauses: [] });
  assert.throws(() => k.formula("interval", [[1n << 64n, 0n]]), /64-bit/);
  const unit = k.term("Unit"), point = k.term("Point"), path = k.term("PLam", 0, unit, point);
  const atOne = k.term("PApp", k.formula("interval", [[0n, 0n]]), path);
  const checked = derive(k, atOne, unit);
  assert.equal(k.node(k.normalize(checked.expression)).kind, "Point");
  // A face given as a path's argument is refused, not read as the interval
  // formula with the same clauses (work plan I1.2c).
  assert.throws(() => derive(k, k.term("PApp", impossible, path), unit),
    /A path is applied at an interval point; found a face formula\./);
});

test("disposed WASM sessions cannot accidentally access a new session", t => {
  const old = session(t), token = old.handle;
  old.dispose();
  const next = session(t);
  assert.notEqual(next.handle, token);
  assert.equal(module._cb_term(token, 1, 0, 0, 0, 0, 0), 0);
  assert.throws(() => old.term("Unit"), /disposed/);
});

test("named syntax preserves path binders and sharing across checks", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  const pt = T.path("i", two, left, left), p = T.variable("p");
  const term = T.lam("p", pt, T.line("j", two, T.at(p, I.reverse(I.variable("j")))));
  const checked = elaborate(k, term);
  assert.equal(checked.type.tag, "Pi");
  assert.equal(checked.type.body.tag, "Path");
  assert.equal(syntax.encode(term), syntax.encode(term));
  const roundTrip = elaborate(k, checked.term, checked.type);
  assert.deepEqual(roundTrip.type, checked.type);
  assert.throws(() => { term.name = "changed"; }, TypeError);
});

test("the actual binary source checks entirely in cubical WASM", async t => {
  const { result } = await checkTestModule(t, "wasm_binary_literal", { module: producerModule });
  assert.equal(result.imports.filter(d=>d.sourceModule==="binary_naturals" && d.verified).length,6);
});

test("dependent pair induction checks its motive and both branch arguments natively", t => {
  const k = session(t), checker = new NativeCubicalElaborator(k);
  const translator = new Translator({ normalize: false, checker });
  const result = translator.translate(`
    def second(A : U0, B : A -> U0, p : (exists x : A. B(x))) :=
      pair_induction((fun (q : (exists x : A. B(x))) => B(unpack q as (a, b) return A { a; })),
        (fun (a : A) => fun (b : B(a)) => b), p);
    def wrong(p : Nat and Nat) := pair_induction(
      (fun (q : Nat and Nat) => Nat), (fun (a : Nat) => fun (b : Unit) => a), p);
  `);
  assert.equal(result.declarations[0].status, "checked-native-cubical", result.declarations[0].reason);
  assert.equal(result.declarations[1].status, "not-translated");
  assert.equal(k.definitions.has("wrong"), false);
});

test("a theory whose type of models fails is reported once, with no observer counting what is taken off", t => {
  const k = session(t), checker = new NativeCubicalElaborator(k);
  // Without hlevels, Pointed's sorts have no evidence: the rest of the
  // theory is not checked, and fails nothing more.
  const result = new Translator({ normalize: false, checker })
    .translate("theory Pointed(U < UU0) { M : set U; point : M; } def after := tt;");
  assert.deepEqual(result.declarations.map(d => [d.name, d.status]), [["Pointed", "not-translated"], ["after", "checked-native-cubical"]]);
  assert.match(result.declarations[0].reason, /need IsSet, from hlevels/);
});

test("the kernel computes transport through Glue without a univalence axiom", t => {
  const k = session(t), syntax = new CubicalSyntax(k), e = identityEquivalence(two);
  const ua = T.line("ua", T.universe(0), T.glueType(two, [
    { face: F.endpoint("ua", 0), type: two, equiv: e },
    { face: F.endpoint("ua", 1), type: two, equiv: e },
  ]));
  elaborate(k, ua, T.path("i", T.universe(0), two, two));
  const moved = T.comp("j", T.at(ua, I.variable("j")), [], right);
  const checked = elaborate(k, moved, two);
  assert.deepEqual(syntax.decode(k.normalize(checked.expression)), right);
  const forged = T.glueType(two, [{ face: F.top, type: two, equiv: T.lam("x", two, T.variable("x")) }]);
  assert.throws(() => elaborate(k, forged), /Type mismatch/);
});

test("native elaboration checks all manual factorial sources while retaining checked definitions", async t => {
  const program = await archive(t, "binary_arithmetic", "binary_induction", "radix_factorial");
  for(const name of ["binary_arithmetic__binary_factorial_ten", "radix_factorial__radix_factorial_ten_base_two", "radix_factorial__radix_factorial_ten_base_ten"]) {
    const view=program.inspect(name),checked=program.checker.checkView(view.expression,view.type);
    assert.ok(checked.arenaNodes<500000 && checked.arenaBytes<32*1024*1024);
  }
});

test("the existing Nat factorial theorem checks cubically without a million-successor expression",async t=>{
  const program = await archive(t, "binary_arithmetic_correct");
  const view=program.inspect("binary_arithmetic_correct__factorial_ten_from_binary"),checked=program.checker.checkView(view.expression,view.type);
  assert.ok(checked.arenaNodes<500000 && checked.arenaBytes<32*1024*1024);
});

test("open cubes check dependent contexts and preserve dimension names across decoding", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  const dimensions = new Map([["i", 63]]);
  const family = T.path("j", T.universe(0), two, two);
  const atI = T.at(T.variable("family"), I.variable("i"));
  const context = [["family", family], ["x", atI]];
  const checked = elaborate(k, T.variable("x"), atI, context, dimensions);
  assert.deepEqual(checked.type.arg, I.variable("i"));
  assert.equal(elaborate(k, checked.term, checked.type, context, dimensions).type.tag, "PApp");
  assert.throws(() => elaborate(k, T.variable("x"), atI, context), /Unbound cubical dimension/);
  const rawContext = context.map(([name, type]) => [k.symbol(name), syntax.encode(type, dimensions)]);
  // A judgement's context records each dimension it needs, whatever mask the driver was given.
  const driver = new InstructionDriver(k);
  const judgement = driver.graph.judgement(driver.check(syntax.encode(T.variable("x")), syntax.encode(atI, dimensions), rawContext, 1n));
  assert.ok(judgement.context.some(entry => driver.graph.entry(entry).dimension && driver.graph.entry(entry).symbol === 63));
  assert.throws(() => derive(k, syntax.encode(T.variable("x")), syntax.encode(atI, dimensions)));
  assert.throws(() => elaborate(k, left, null, [], new Map([["i", 0], ["j", 0]])), /distinct/);
  // A user name resembling the decoder's generated binder must not be captured.
  const collision = new Map([["d0", 63]]);
  const line = T.line("j", two, T.at(T.variable("p"), I.variable("d0")));
  const decoded = elaborate(k, line, null, [["p", T.path("k", two, left, left)]], collision).term;
  assert.notEqual(decoded.dim, "d0");
  assert.deepEqual(decoded.body.arg, I.variable("d0"));
  elaborate(k, decoded, null, [["p", T.path("k", two, left, left)]], collision);
});

// The refusals are wasm_invalid_paths.
test("Cubist expresses cubical paths, composition and pushout elimination with checked boundaries", async t => {
  const program=new CubicalProgram(producerModule,sourceReader());
  t.after(()=>program.dispose());
  const result=await program.check(await sourceReader()("cubical_paths"),"cubical_paths");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  assert.equal(result.outputs.length,15);
});

// The verdicts are wasm_moving_maps'; here, the transport's normal form,
// the corrected composition of 3.5, not a bare constructor.
test("the declared pushout's transported path constructor is a composition", async t => {
  const { program } = await checkTestModule(t, "wasm_moving_maps", { module: producerModule });
  assert.match(JSON.stringify(program.inspect("wasm_moving_maps__moved",{normalize:true}).expression),/"tag":"HComp"/);
});

// Its use is wasm_suspension_use.
test("source-defined suspension induction checks", async t => {
  const libraryProgram = new CubicalProgram(producerModule, sourceReader());
  t.after(() => libraryProgram.dispose());
  const library = await libraryProgram.check(await sourceReader()("suspension_types"), "suspension_types");
  assert.ok(library.complete, JSON.stringify(library.gaps));
  assert.ok(library.outputs.every(output => output.verified));
});

test("a query's growing budget stops at its declared limit and fails as the kernel's exhaustion", t => {
  const k = session(t), syntax = new CubicalSyntax(k);
  assert.equal(k.maxQuerySteps, 1280000000n);
  // A weak head that takes more than four steps, with a session budget of
  // one step and a limit of four: the query runs with 1, 2 and 4 steps, and
  // then fails as the kernel's exhaustion, not as a mismatch.
  const swapping = T.lam("n", two, swap(T.variable("n")));
  let term = left;
  for (let i = 0; i < 8; i++) term = T.app(swapping, term);
  const handle = syntax.encode(term);
  k.stepBudget = 1n; module._cb_step_budget(k.handle, 1, 0);
  k.maxQuerySteps = 4n;
  const before = k.work();
  assert.throws(() => k.head(handle), error => error.kind === "budget");
  const spent = k.work();
  assert.equal(spent.queries - before.queries, 3);
  assert.equal(spent.exhausted - before.exhausted, 3);
  assert.equal(spent.querySteps - before.querySteps, 1 + 2 + 4);
  assert.equal(k.stepBudget, 1n);
  // With room to grow, the same query answers.
  k.maxQuerySteps = 1280000000n;
  assert.ok(k.head(handle));
});

test("browser dimension allocation reuses slots without capturing outer coordinates", t => {
  const k = session(t), checker = new NativeCubicalElaborator(k);
  let type = T.unit, point = T.point;
  for (let i = 0; i < 100; i++) {
    const next = T.path(`constant${i}`, type, point, point);
    point = checker.define(`level${i}`, T.line(`constant${i}`, type, point), next); type = next;
  }
  elaborate(k, point, type);
  const p = T.variable("p"), P = T.path("i", two, left, right);
  const line = T.line("j", two, T.at(p, I.variable("outside")));
  const checked = elaborate(k, line, null, [["p", P]], new Map([["outside", 0]]));
  assert.throws(() => elaborate(k, checked.term, null, [["p", P]]), /dimension/);
});

test("kernel rejections are classified by kind, and speculative checks answer with values", t => {
  const k = session(t), checker = new NativeCubicalElaborator(k), syntax = new CubicalSyntax(k);
  assert.throws(() => derive(k, syntax.encode(left), k.term("Unit")), error => error instanceof KernelError && error.kind === "mismatch");
  assert.throws(() => elaborate(k, T.variable("free"), two), error => error instanceof KernelError && error.kind === "other");
  assert.equal(checker.attempt(left, two).ok, true);
  assert.equal(checker.attempt(left, T.unit).failure, "mismatch");
  assert.equal(checker.equal(left, right), false);
  // Set C's deadline directly so this exercises C, not the JS preflight guard.
  // The term is new: a judgement derived earlier is reused without work.
  module._cb_deadline_ms(k.handle, .01);
  let until = performance.now() + 2;
  while (performance.now() < until) { /* let the native deadline expire */ }
  const pairs = T.sigma("_", two, two);
  assert.equal(checker.attempt(T.pair(pairs, left, right), pairs).failure, "deadline");
  module._cb_deadline_ms(k.handle, 0);
  // Running out of time is no answer: equal() must not report inequality.
  k.setDeadline(0.001);
  until = performance.now() + 2;
  while (performance.now() < until) { /* let the JavaScript deadline expire */ }
  assert.equal(checker.attempt(left, two).failure, "deadline");
  assert.throws(() => checker.equal(left, left), error => error instanceof KernelError && error.kind === "deadline");
  k.setDeadline();
  assert.equal(checker.equal(left, left), true);
});

test("the native kernel checks an elimination through an abstracted motive", t => {
  const checker = new NativeCubicalElaborator(session(t)), v = T.variable;
  const sum = T.sum(v("A"), v("B")), same = value => T.path("i", sum, value, value);
  // s : A + B and h : s = s; the goal s = s is proved by cases on s.
  const scope = [["A", T.universe(0)], ["B", T.universe(0)], ["s", sum], ["h", same(v("s"))]]
    .reduce((scope, [name, type]) => scope.bind(name, type), new Scope(new SourceUnit({ checker })));
  const goal = new Goal(same(v("s")), scope), motive = abstractMotive(goal, [v("s")]);
  assert.deepEqual(motive.generalized.map(hypothesis => hypothesis.name), ["h"]);
  const branch = (side, domain) => {
    const name = scope.fresh(side), inner = scope.bind(name, domain), value = T[side](sum, v(name));
    const { transition } = motive.introduce(motive.instance([value], inner));
    return T.lam(name, domain, transition.rebuild(reflexivity(transition.next)));
  };
  const proof = motive.apply(T.sumrec(motive.term, branch("inl", v("A")), branch("inr", v("B")), v("s")));
  assert.doesNotThrow(() => scope.check(proof, goal.target));
  // A branch proof of the unrefined goal is rejected.
  const unrefined = T.lam("a", v("A"), T.lam("h2", same(v("s")), T.variable("h2")));
  assert.throws(() => scope.check(motive.apply(T.sumrec(motive.term, unrefined, branch("inr", v("B")), v("s"))),
    goal.target), error => error instanceof KernelError);
});

// A recursive match names its declaration's other parameters: the motive
// quantifies over them whatever their types mention, and each branch binds
// them again under their stems, the names a display shows.
test("the motive service generalizes a hypothesis it is given, and binds it again under its stem", t => {
  const checker = new NativeCubicalElaborator(session(t)), v = T.variable;
  const sum = T.sum(v("A"), v("B")), unit = new SourceUnit({ checker }), a = unit.names.fresh("a");
  const scope = [["A", T.universe(0)], ["B", T.universe(0)], ["s", sum], [a, v("A")]]
    .reduce((scope, [name, type]) => scope.bind(name, type), new Scope(unit));
  const goal = new Goal(v("A"), scope);
  assert.deepEqual(abstractMotive(goal, [v("s")]).generalized, []);
  const motive = abstractMotive(goal, [v("s")], { generalizing: [a] });
  assert.deepEqual(motive.generalized.map(hypothesis => hypothesis.name), [a]);
  const branch = (side, domain) => {
    const name = scope.fresh(side), inner = scope.bind(name, domain), value = T[side](sum, v(name));
    const { transition, renamed } = motive.introduce(motive.instance([value], inner));
    assert.match(renamed.get(a).name, /^a[0-9]+$/);
    return T.lam(name, domain, transition.rebuild(renamed.get(a)));
  };
  const proof = motive.apply(T.sumrec(motive.term, branch("inl", v("A")), branch("inr", v("B")), v("s")));
  assert.doesNotThrow(() => scope.check(proof, goal.target));
});

// A scope built apart from elaboration may bind names another supply gave:
// the motive's binders avoid them, so they capture nothing.
test("the motive service's binders avoid every name the scope binds", t => {
  const checker = new NativeCubicalElaborator(session(t)), v = T.variable;
  const scope = [["x1", two], ["x2", two]]
    .reduce((scope, [name, type]) => scope.bind(name, type), new Scope(new SourceUnit({ checker })));
  const goal = new Goal(T.path("i", two, v("x1"), v("x2")), scope);
  const motive = abstractMotive(goal, [v("x2")]);
  assert.equal(scope.context.has(motive.binders[0].name), false);
  assert.deepEqual(motive.instance([v("x2")]).target, goal.target);
});

test("G0: the module's ABI version is checked, and a universe carries its level as a child", t => {
  // A module built for another encoding is refused before any syntax is made.
  assert.throws(() => new CubicalKernel({ ...module, _cb_abi_version: () => 1 }), /ABI version 1, but this code expects version 3/);
  assert.throws(() => new CubicalKernel({ _cb_new: module._cb_new }), /ABI version 1/);
  const k = session(t), syntax = new CubicalSyntax(k);
  // Tier-0 levels stay numbers; other constants are objects.
  const u3 = syntax.encode({ tag: "U", level: 3 }), uu3 = { tag: "U", level: { tag: "LConst", tier: 1, value: 3 } };
  assert.equal(k.node(u3).payload, 0);
  assert.equal(k.node(k.node(u3).children[0]).kind, "LConst");
  assert.deepEqual(syntax.decode(u3), { tag: "U", level: 3 });
  assert.deepEqual(syntax.decode(syntax.encode(uu3)), uu3);
  assert.throws(() => k.term("U", 3), /payload must be zero/);
  // The instruction kernel takes a level to normal form: U(max(1, 0)) is U1.
  const g = new InstructionGraph(k), one = syntax.encodeLevel(1);
  const max = syntax.encodeLevel({ tag: "LMax", left: 1, right: 0 });
  const u1 = g.judgement(g.universe(one));
  assert.equal(g.judgement(g.universe(max)).term, u1.term);
  assert.deepEqual(syntax.decode(u1.type), { tag: "U", level: 2 });
  // Cumulativity crosses tiers: Unit : U0 ≤ UU0, but UU0 is not in U5.
  const uu0 = g.universe(syntax.encodeLevel({ tag: "LConst", tier: 1, value: 0 }));
  assert.deepEqual(syntax.decode(g.judgement(g.lift(g.unit(), uu0)).type), { tag: "U", level: { tag: "LConst", tier: 1, value: 0 } });
  assert.throws(() => g.lift(uu0, g.universe(syntax.encodeLevel(5))), /not included/);
  assert.throws(() => g.universe(syntax.encodeLevel(0xffff)), /exceeds the kernel's bound/);
  // Levels print in kernel and source notation.
  assert.deepEqual([levelText({ tag: "LConst", tier: 1, value: 2 }), levelText({ tag: "LConst", tier: 2, value: 0 }),
    levelText({ tag: "LMax", left: { tag: "Var", name: "x" }, right: 1 }), levelText({ tag: "LSucc", count: 1, level: { tag: "Var", name: "x" } })],
    ["ω + 2", "ω·2", "max(x, 1)", "x + 1"]);
  assert.deepEqual([universeText(3), universeText({ tag: "LConst", tier: 1, value: 3 }), universeText({ tag: "LConst", tier: 2, value: 0 })],
    ["U3", "UU3", "UUU0"]);
});

test("G0: level entries and level quantification through the instruction wrapper and the codec", t => {
  const k = session(t), syntax = new CubicalSyntax(k), g = new InstructionGraph(k);
  const x = g.level("x"), ux = g.universe(syntax.encodeLevel({ tag: "Var", name: "x" }));
  assert.throws(() => g.variable(x), /not a term/);
  // λ (x < ω). U(x) : Π (x < ω). U(x + 1), and its instance at 2 is U(2) : U(3).
  const family = g.levelLambda(x, ux);
  assert.deepEqual(syntax.decode(g.judgement(family).term),
    { tag: "LLam", name: "x", body: { tag: "U", level: { tag: "Var", name: "x" } } });
  const atTwo = g.judgement(g.levelApply(family, syntax.encodeLevel(2)));
  assert.deepEqual(syntax.decode(atTwo.type), { tag: "U", level: 3 });
  assert.throws(() => g.levelApply(family, syntax.encodeLevel({ tag: "LConst", tier: 1, value: 0 })), /finite/);
  // Π (x < ω). U(x) lives in UU0.
  const statement = g.judgement(g.levelPi(x, ux));
  assert.equal(statement.context.length, 0);
  assert.deepEqual(syntax.decode(statement.type), { tag: "U", level: { tag: "LConst", tier: 1, value: 0 } });
  const generic = { tag: "LPi", name: "y", body: { tag: "U", level: { tag: "LSucc", count: 1, level: { tag: "Var", name: "y" } } } };
  assert.deepEqual(syntax.decode(syntax.encode(generic)), generic);
});
