import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {cubistTestModules} from "../web/cubist/modules.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases, historicalCoverage, passingCoverage} from "./fixtures/frontend-generation.mjs";
import {accepted, complete, observeCase, recordCase, validateFixture} from "./frontend-generation-contracts.mjs";

const module = await createCubical();
const check = (t, source, fixtures = {}) => {
  const library = sourceReader();
  return checkProgram(t, source, {module, reader: (name, importer) => fixtures[name] ?? library(name, importer)});
};
// Keep group prefixes selectable by the downstream FG6 mutation gate.
for (const fixture of cases) test(`${fixture.group}: [${fixture.id}] ${fixture.contract}`, async t => {
  const observation = await observeCase(t, fixture, check);
  recordCase(t, fixture, observation, {strict: process.env.CUBIST_GENERATION_STRICT === "1"});
});

test("FG0 maps historical fixes and passing controls to existing executable tests", async () => {
  assert.equal(new Set(cases.map(fixture => fixture.id)).size, cases.length, "case IDs must be unique");
  for (const fixture of cases) validateFixture(fixture);
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  const documented = [...manifest.matchAll(/^\| `([^`]+)` \| G\d+ \|/gm)].map(match => match[1]);
  assert.deepEqual(documented.sort(), cases.map(fixture => fixture.id).sort(), "the coverage matrix must name every executable case once");
  for (const [file, name] of [...Object.values(historicalCoverage), ...passingCoverage]) {
    const source = await readFile(new URL(file, import.meta.url), "utf8");
    if (file.endsWith(".cubist")) {
      assert.ok(cubistTestModules.includes(file.split("/").at(-1).slice(0, -".cubist".length)),
        `${file} must run in the Cubist regression suite`);
      const declarations = new Set(parse(source).declarations.map(declaration => declaration.name?.text));
      for (const declaration of name) assert.ok(declarations.has(declaration), `${file}: ${declaration}`);
    } else {
      assert.ok(source.includes(`test(${JSON.stringify(name)},`), `${file}: ${name}`);
    }
  }
});

test("B1: opened fields precede later globals in ordinary and generated declarations across imports", async t => {
  const definitions = `import hlevels;
theory Point(U < UU0) { M : set U; point : M; }
def unit_set : IsSet(U0, Unit) { hlevel; }
def selected : Point(U0) := Point.make(Unit, unit_set, tt);
use selected;
inductive M : U0 { unrelated; }
inductive Box : U0 { box(x : M); }
theory T(U < UU0) { A : set U; op(x : M) : A; }
`;
  const client = `def boxed : Box := box(tt);
def input(S : T(U0)) : S.A := S.op(tt);
initial N : T(U0);
def generated : N := N.op(tt);
`;
  for (const imported of [false, true]) {
    const checked = await check(t, imported ? `import fixture;\n${client}` : definitions + client, {fixture: definitions});
    complete(checked); accepted(checked, ["boxed", "input", "generated"]);
  }
  const changed = await check(t, `${definitions}
def other : Point(U0) := Point.make(Nat, nat_is_set, zero);
use other;
inductive Later : U0 { later(x : M); }
def still_unit : Box := box(tt);
def now_nat : Later := later(zero);
`.replace("import hlevels;", "import hlevels; import nat;"));
  complete(changed); accepted(changed, ["still_unit", "now_nat"]);
});

test("FG0 controls: inherited, bare and partial helpers preserve independently stated law boundaries", async t => {
  const checked = await check(t, `import hlevels;
theory P(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  def kc(x, y : M) : M := op(x, c);
  def apply(f : M -> M, x : M) : M := f(x);
}
theory T(U < UU0) extends P {
  law inherited(c : M) : k(c) = op(c, c);
  law bare(c : M) : apply(k, c) = op(c, c);
  law partial(c : M) : apply(kc(c), c) = op(c, c);
}
def intended(S : T(U0), x : S.M) : S.op(x, S.c) = S.op(x, x) := S.inherited(x);
def bare(S : T(U0), x : S.M) : S.op(x, S.c) = S.op(x, x) := S.bare(x);
def partial(S : T(U0), x : S.M) : S.op(x, S.c) = S.op(x, x) := S.partial(x);
`);
  complete(checked); accepted(checked, ["intended", "bare", "partial"]);
});

test("FG0 controls: inherited recursive operations and initial-model clients compute", async t => {
  const checked = await check(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
}
theory Child(U < UU0) extends T {}
initial N : Child(U0);
def inherited(S : Child(U0)) : S.iter(zero) = S.c { rfl; }
def initial_computation : N.model.iter(zero) = N.c { rfl; }
`);
  complete(checked); accepted(checked, ["inherited", "initial_computation"]);
});

for (const {source, code, from, to} of [
  {source: "def g : forall x : Unit. Unit := fun (x : Unit) => tt;", code: "W705", from: "forall x : Unit. Unit", to: "Unit -> Unit"},
  {source: "def g : forall x, y : Unit. Unit := fun (x, y : Unit) => tt;", code: "W706", from: "forall x, y : Unit. Unit", to: "Unit -> Unit -> Unit"},
]) test(`FG0 controls: safe unused-binder advice remains available (${code})`, async t => {
  assert.ok(lint(source).some(w => w.code === code), `${code} safe unused-binder advice must remain available`);
  for (const candidate of [source, source.replace(from, to)]) {
    const checked = await check(t, candidate);
    complete(checked); accepted(checked, ["g"]);
  }
});

test("FG0 controls: explicit path bodies remain checked and recursive type unfolding remains refused", async t => {
  const explicit = await check(t, `import hlevels;
inductive H : set U0 { first; p(y : H) : y = y; }
def k(x : H) : Unit := match x { first => tt; p(y) @ i => k(y); };
def computation : k(first) = tt { rfl; }
`);
  complete(explicit); accepted(explicit, ["k", "computation"]);
  const refused = await check(t, cases.find(fixture => fixture.id === "G12-range").source);
  assert.equal(refused.result.gaps[0]?.code, "E845");
});
