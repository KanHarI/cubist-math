import "./fresh-build.mjs";
import {naturalSort, numeral} from "../lib/cubical/numerals.mjs";
import { cubicalSourceFile } from "../web/cubical-sources.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { cubicalMathTree } from "../web/cubical-notation.mjs";
const module = await createCubical();

test("a universe-generic definition is checked once and instantiated at each level", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  await program.check(`def identity(U < UU0, A : U, x : A) := x;
    def first := identity(U0, Nat, 0); def second := identity(U0, Nat, 1);
    def higher := identity(U1, U0, Nat);
    def wrong : 0 = 1 { exact refl(identity(U0, Nat, 0)); }`, "generic");
  assert.equal(program.symbols.generic__identity.verified, true);
  assert.equal(program.inspect("generic__identity").type.tag, "LPi");
  assert.deepEqual([...program.kernel.definitions.keys()].filter(name => name.startsWith("generic__identity")), ["generic__identity"]);
  assert.equal(program.symbols.generic__second.verified, true);
  assert.equal(program.symbols.generic__higher.verified, true);
  assert.equal(program.symbols.generic__wrong.verified, false);
});

test("the browser program checks Euclid from source and exports a replayable native inspection", async t => {
  const readSource = name => readFile(new URL(`../archive/first-library/${cubicalSourceFile(name)}`, import.meta.url), "utf8");
  const program = new CubicalProgram(module, readSource); t.after(() => program.dispose());
  const result = await program.check(await readSource("euclid"), "euclid");
  assert.equal(result.complete, true);
  assert.equal(result.backend, "cubical");
  assert.ok(result.instructionCount > 0);
  assert.ok(result.links.some(x => x.name === "prime_divisor_exists"));
  assert.equal(program.inspect("euclid__euclid").type.name, "euclid__InfinitelyManyPrimes");
  const local = result.links.find(x => x.role === "local" && program.inspect(x.binding).context.length);
  assert.ok(local);
  assert.ok(program.inspect(local.binding).context.length);
  const payload = program.export("euclid__euclid", "type");
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).type, program.inspect(payload.binding).type);
});

test("module shadowing cannot retarget earlier checked native definitions", async t => {
  const sources = { first: "def value := 0; def remembered := value;", second: "def value := 1;" };
  const program = new CubicalProgram(module, async name => sources[name]); t.after(() => program.dispose());
  const result = await program.check("import first; import second; def preserved : remembered = 0 { exact refl(0); }", "example");
  assert.equal(result.complete, true);
  assert.equal(program.inspect("first__remembered").expression.name, "first__value");
  assert.equal(program.inspect("first__value", { normalize: true }).expression.tag, "Con");
  assert.equal(program.inspect("second__value", { normalize: true }).expression.tag, "App");
});

test("unsupported foundations and invalid proofs remain explicitly unverified", async t => {
  const program = new CubicalProgram(module, async () => { throw new Error("Source unavailable"); }); t.after(() => program.dispose());
  const result = await program.check("import missing; def wrong : 0 = 1 { exact refl(0); } def dependent := wrong; def fine := 0;", "example");
  assert.equal(result.complete, false);
  assert.deepEqual(result.outputs.map(d => d.verified), [false, false, true]);
  assert.ok(result.gaps.some(g => g.module === "missing"));
  assert.throws(() => program.inspect("example__wrong"));
  assert.equal(program.kernel.definitions.has("example__wrong"), false);
});

test("native notation preserves named references and dependent path families", () => {
  assert.deepEqual(cubicalMathTree({ tag: "DefRef", name: "m__F" }, { m__F: { name: "F" } }),
    { kind: "Name", name: "F", binding: "m__F" });
  const family = { tag: "PApp", path: { tag: "Var", name: "p" }, arg: [["i:1"]] };
  const tree = cubicalMathTree({ tag: "Path", dim: "i", family, left: { tag: "Var", name: "a" }, right: { tag: "Var", name: "b" } });
  assert.equal(tree.fn.name, "PathP");
});

test("native path interiors retain their interval context in the inspector and replay", async t => {
  const readSource = name => readFile(new URL(`../archive/first-library/${cubicalSourceFile(name)}`, import.meta.url), "utf8");
  const program = new CubicalProgram(module, readSource); t.after(() => program.dispose());
  const source = await readSource("cubical_paths");
  const result = await program.check(source, "cubical_paths");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const local = result.links.find(link => program.views.get(link.binding)?.dimensions.size);
  assert.ok(local);
  const view = program.inspect(local.binding);
  assert.equal(view.dimensions.length, 1);
  const payload = program.export(local.binding);
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).dimensions, view.dimensions);
});

test("logical assumptions remain explicit, minimal, and inspectable after native closure", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const result = await program.check(`
    def Mere(A : U1) := Truncate(U1, A);
    def introduction(A : U1, a : A) := TruncateIntro(U1, A, a);
    def innocent : 0 = 0 { exact refl(0); }
    def wrong : 0 = 1 { exact refl(0); }
  `, "assumptions");
  assert.deepEqual(result.outputs.map(d => d.verified), [true, true, true, false]);
  assert.equal(result.outputs[1].axioms.length, 2);
  assert.deepEqual(result.outputs[2].axioms, []);
  const view = program.inspect("assumptions__introduction");
  assert.equal(view.context.length, 2);
  assert.ok(view.context.some(entry => entry.label === "Truncate"));
  const assumption = program.inspect(view.axioms[0]);
  assert.equal(assumption.expression.tag, "Var");
  const payload = program.export("assumptions__introduction");
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).context, view.context);
});

test("source unfolding hints name checked definitions, remain scoped, and cannot prove false paths", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const source = `
    def id(n : Nat) := n;
    def hinted : id(0) = 0 { exact with unfolding [id] { refl(0) }; }
    def ordinary : 0 = 0 { exact refl(0); }
    def false_hint : id(0) = 1 { exact with unfolding [id] { refl(0) }; }
    def missing : 0 = 0 { exact with unfolding [unknown] { refl(0) }; }
  `;
  const result = await program.check(source, "hints");
  assert.deepEqual(result.outputs.map(d => d.verified), [true, true, true, false, false]);
  assert.deepEqual(result.outputs[1].unfoldingHints, []);
  assert.deepEqual(program.checker.definitionViews.get("hints__unfolding_1").unfoldingHints, ["hints__id"]);
  assert.deepEqual(result.outputs[2].unfoldingHints, []);
  assert.deepEqual(program.kernel.unfoldingHints, []);
  const view = program.inspect("hints__hinted");
  assert.deepEqual(view.unfoldingHints, []);
  assert.deepEqual(program.kernel.unfoldingHints, []);
  const payload = program.export("hints__hinted");
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).type, view.type);
});

test("native progress identifies the active declaration before it is checked", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const progress = [];
  await program.check("def first := 0; def second := 1;", "progress", event => progress.push(event));
  const checking = progress.filter(p => p.phase !== "loading");
  assert.ok(checking.every(p => p.total === 3));
  assert.deepEqual(checking.map(p => [p.current, p.phase, p.completed]), [
    ["nat.Nat", "checking", 0], ["nat.Nat", "checked", 1],
    ["progress.first", "checking", 1], ["progress.first", "checked", 2],
    ["progress.second", "checking", 2], ["progress.second", "checked", 3],
  ]);
});

test("unfolding scopes close local variables and interval coordinates without leaking hints", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const result = await program.check(`
    def id(n : Nat) := n;
    def local(n : Nat) : id(n) = n { exact with unfolding [id] { refl(n) }; }
    def scoped_path(n : Nat, p : n = n) := path(
      fun (i : Interval) => Nat,
      fun (i : Interval) => with unfolding [id] { at(p, i) }
    );
    def endpoint(n : Nat, p : n = n) : at(scoped_path(n, p), 0) = n { exact refl(n); }
  `, "scope");
  assert.deepEqual(result.outputs.map(d => [d.name, d.reason]).filter(([, reason]) => reason), []);
  assert.equal(result.complete, true);
  assert.deepEqual(program.kernel.unfoldingHints, []);
});

test("progress totals count a shared import once, including universe-generic definitions", async t => {
  const sources = {
    common: "def generic(U < UU0, A : U, a : A) := a; def shared := 0;",
    left: "import common; def fromLeft := shared;",
    right: "import common; def fromRight := shared;",
  };
  const reads = [];
  const program = new CubicalProgram(module, async name => { reads.push(name); return sources[name]; });
  t.after(() => program.dispose());
  const progress = [];
  const result = await program.check("import left; import right; def final := fromLeft;", "root", p => progress.push(p));
  assert.equal(result.declarationCount, 6);
  assert.equal(reads.filter(name => name === "common").length, 1);
  assert.ok(progress.filter(p => p.phase !== "loading").every(p => p.total === 6));
  assert.equal(progress.at(-1).completed, 6);
});

test("native optimization switches preserve path proofs and rejection independently", async () => {
  for (let flags = 0; flags < 8; flags++) {
    const optimizations = { shareSyntax: !!(flags & 1), reuseChecks: !!(flags & 2), compactPaths: !!(flags & 4) };
    const program = new CubicalProgram(module, async () => "", { optimizations });
    try {
      const result = await program.check(`
        def compose(x : Nat, y : Nat, z : Nat, p : x = y, q : y = z) : succ(x) = succ(z) {
          exact cong(succ, trans(p, q));
        }
        def reverse(x : Nat, y : Nat, p : x = y) : y = x { exact sym(p); }
        def wrong : 0 = 1 { exact trans(refl(0), refl(0)); }
        def disconnected : 0 = 1 { exact trans(refl(0), refl(1)); }
      `, "options");
      assert.deepEqual(result.outputs.map(d => d.verified), [true, true, false, false], JSON.stringify(optimizations));
      assert.deepEqual(program.kernel.optimizations, optimizations);
    } finally { program.dispose(); }
  }
});

test("calls of an imported generic definition link to the definition itself", async t => {
  const sources = { generic: "def identity(U < UU0, A : U, x : A) := x;" };
  for (const reuseChecks of [true, false]) {
    const program = new CubicalProgram(module, async name => sources[name], { optimizations: { reuseChecks } });
    t.after(() => program.dispose());
    const source = "import generic; def zero := identity(U0, Nat, 0); def identity1 := identity(U1);";
    const result = await program.check(source, "caller");
    assert.equal(result.complete, true, JSON.stringify(result.gaps));
    const references = result.links.filter(link => link.binding === "generic__identity");
    assert.equal(references.length, 2);
    for (const link of references) {
      assert.equal(source.slice(link.start, link.end), "identity");
      const view = program.inspect(link.binding);
      assert.equal(view.type.tag, "LPi");
      assert.equal(view.symbols[link.binding].sourceModule, "generic");
      assert.deepEqual(view.axioms, []);
    }
    for (const link of result.links)
      assert.equal(source.slice(link.start, link.end), link.name, "imported offsets must not leak into the caller");
    assert.deepEqual(program.inspect("caller__identity1").type.domain, { tag: "U", level: 1 });
  }
});

test("an unused generic definition is checked, and its locals inspect and replay under the universe binder", async t => {
  const source = `def identity(U < UU0, A : U, x : A) := x;
    def constant(U, V < UU0, A : U, B : V, x : A, y : B) := x;
    def invalid(U < UU0, A : U, x : A) : Void { exact x; }`;
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const result = await program.check(source, "generic");
  assert.deepEqual(result.outputs.map(d => d.verified), [true, true, false]);
  assert.match(result.outputs[2].reason, /Void/);
  const constant = program.inspect("generic__constant").type;
  assert.deepEqual([constant.tag, constant.body.tag], ["LPi", "LPi"]);
  const local = result.links.find(link => link.name === "x" && source.slice(link.end, link.end + 1) === ";");
  const view = program.inspect(local.binding);
  assert.equal(view.expression.tag, "Var");
  assert.deepEqual(view.context.map(entry => entry.label), ["U", "A", "x"]);
  assert.deepEqual(view.context[0].type, { tag: "LBound", tier: 1 });
  assert.deepEqual(view.context[1].type, { tag: "U", level: { tag: "Var", name: view.context[0].name } });
  const payload = program.export(view.name);
  const replay = new CubicalProgram(module, async () => ""); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  const restored = replay.inspect(payload.binding);
  assert.deepEqual(restored.expression, view.expression);
  assert.deepEqual(restored.type, view.type);
  assert.deepEqual(restored.context, view.context);
});

test("untyped lambdas in generic definitions report errors without aborting later declarations",async t=>{
  const program=new CubicalProgram(module,async()=>""); t.after(()=>program.dispose());
  const result=await program.check(`
    def generic(U < UU0) := fun x => x;
    def use := generic(U0);
    def good := 0;
    def ordinary := fun x => x;
    def after := 1;
  `,"untyped_generic");
  assert.deepEqual(result.outputs.map(item=>item.verified),[false,false,true,false,true]);
  assert.match(result.outputs[0].reason,/Untyped lambda requires an expected function type/);
  assert.match(result.outputs[1].reason,/Untranslated dependency: generic/);
  assert.match(result.outputs[3].reason,/Untyped lambda requires an expected function type/);
  assert.throws(()=>program.inspect("untyped_generic__generic"),
    /Untyped lambda requires an expected function type/);
});

test("every named reference in the generic group definitions is inspectable with source labels", async t => {
  const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
  const program = new CubicalProgram(module, readSource); t.after(() => program.dispose());
  const result = await program.check(await readSource("group_universes"), "group_universes");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const references = result.links.filter(link => link.role === "local");
  assert.ok(references.length > 300);
  for (const reference of references) {
    const view = program.inspect(reference.binding);
    assert.equal(view.symbols[view.name].name, reference.name);
  }
  const view = program.inspect("group_universes__GroupAssociativeAt");
  assert.equal(view.type.tag, "LPi");
  const notation = JSON.stringify(cubicalMathTree(view.expression, view.symbols));
  for (const name of ["U", "A", "multiply", "x", "y", "z"]) assert.ok(notation.includes(`"name":"${name}"`), name);
  assert.doesNotMatch(notation, /"name":"(?:U|A|multiply|x|y|z)_?[0-9]+"/);
});

test("a declaration that fails after a failed import names the import", async t => {
  const program = new CubicalProgram(await createCubical(), async name => {
    throw new Error(`Native source is not available for ${name}.`);
  }, { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check("import naturals;\ndef four := 2 + 2;\ndef five := 5;\ndef six : Nat {\n  exact 3 + 3;\n}\n", "imports_missing");
  const reason = name => result.outputs.find(output => output.name === name).reason;
  assert.equal(reason("four"),
    "Untranslated name: add (import naturals failed: Native source is not available for naturals.)");
  assert.match(reason("six"), /^Untranslated name: add \(import naturals failed: .*\)( at \d+:\d+)?$/);
  assert.equal(result.outputs.find(output => output.name === "five").verified, true);
});
