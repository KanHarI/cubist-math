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
import {accepted, complete, observeCase, assertCase, validateFixture, validateCoverage} from "./frontend-generation-contracts.mjs";

const module = await createCubical();
const check = (t, source, fixtures = {}) => {
  const library = sourceReader();
  return checkProgram(t, source, {module, reader: (name, importer) => fixtures[name] ?? library(name, importer)});
};
// Keep group prefixes selectable by the downstream FG6 mutation gate.
for (const fixture of cases) test(`${fixture.group}: [${fixture.id}] ${fixture.contract}`, async t => {
  const observation = await observeCase(t, fixture, check);
  assertCase(fixture, observation);
});

test("FG0 maps historical fixes and passing controls to existing executable tests", async () => {
  assert.equal(new Set(cases.map(fixture => fixture.id)).size, cases.length, "case IDs must be unique");
  for (const fixture of cases) validateFixture(fixture);
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  validateCoverage(manifest, cases);
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
  const wrongPath = await check(t, `import hlevels;
inductive H : set U0 { first; p(y : H) : y = y; }
def bad(x : H) : Unit := match x { first => tt; p(y) @ i => tt; };`);
  assert.equal(wrongPath.result.gaps[0]?.code, "E606");
  assert.ok(!wrongPath.program.steps("main").some(step => step.declaration === "bad" && step.kind === "obligation"));
  const multiPath = await check(t, `import hlevels;
inductive H : set U0 { first; p(y : H) : y = y; }
inductive Bit : set U0 { off; yes; }
def bad(x : H, b : Bit) : Unit := match x, b { first, _ => tt; p(y) @ i, _ => tt; };`);
  assert.equal(multiPath.result.gaps[0]?.code, "E606");
  assert.ok(!multiPath.program.steps("main").some(step => step.declaration === "bad" && step.kind === "obligation"));
  const refused = await check(t, cases.find(fixture => fixture.id === "G12-range").source);
  assert.equal(refused.result.gaps[0]?.code, "E845");
});


test("FG0 controls: a local recursive name remains local in a field type", async t => {
  const checked = await check(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  law ok(iter : Nat -> M) : op(iter(zero)) = op(iter(zero));
}
def local(S : T(U0), f : Nat -> S.M) : S.op(f(zero)) = S.op(f(zero)) := S.ok(f);
`);
  complete(checked); accepted(checked, ["T.ok", "local"]);
});

test("FG0 controls: ordinary inherited, bare and partial helper clients remain supported", async t => {
  const checked = await check(t, `import hlevels;
theory P(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  def binary(x, y : M) : M := op(x, y);
  def apply(f : M -> M, x : M) : M := f(x);
}
theory T(U < UU0) extends P {
  law inherited(c : M) : k(c) = op(c, c);
  law bare(x : M) : apply(k, x) = op(x, c);
  law partial(c : M) : apply(binary(c), c) = op(c, c);
}
def intended(S : T(U0), x : S.M) : S.op(x, S.c) = S.op(x, x) := S.inherited(x);
def bare(S : T(U0), x : S.M) : S.op(x, S.c) = S.op(x, S.c) := S.bare(x);
def partial(S : T(U0), x : S.M) : S.op(x, x) = S.op(x, x) := S.partial(x);
`);
  complete(checked); accepted(checked, ["intended", "bare", "partial"]);
});

test("FG6: generated recursive calls retain a predecessor after a nested match destructs it", async t => {
  for (const predecessor of ["k", "T"]) {
    const checked = await check(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c;
    succ(${predecessor}) => match ${predecessor} {
      zero => op(iter(${predecessor})); succ(j) => op(iter(${predecessor}));
    };
  };
}
def computes(S : T(U0)) : S.iter(succ(succ(zero))) = S.op(S.op(S.c)) { rfl; }`);
    complete(checked); accepted(checked, ["T.iter", "computes"]);
  }
});

test("G8: nonrecursive wildcard refusal preserves its exact token without coherence search", async t => {
  const c = cases.find(c => c.id === "G8"), checked = await check(t, c.source);
  const actual = checked.result.gaps.find(g => g.name === "h");
  const start = c.source.lastIndexOf("t1");
  assert.equal(actual.start, start); assert.equal(actual.end, start + 2);
  assert.equal(checked.get("h").searchFuel.searches, 0, "a nonrecursive boundary must not start coherence search");
});
