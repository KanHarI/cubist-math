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
import {gaps, expectedFailures, historicalCoverage, passingCoverage, collisionVariants, matchVariants, lintVariants, captureVariants, captureSource} from "./fixtures/frontend-generation.mjs";

const module = await createCubical();
const check = (t, source, fixtures = {}) => {
  const library = sourceReader();
  return checkProgram(t, source, {module, reader: (name, importer) => fixtures[name] ?? library(name, importer)});
};
const accepted = (checked, names) => {
  for (const name of names) {
    const output = checked.get(name);
    assert.equal(output.verified, true, `${name}: ${output.reason}`);
    assert.deepEqual(output.axioms, [], `${name} must not introduce assumptions`);
  }
};
const complete = checked => assert.deepEqual(checked.result.gaps, []);
const gap = (checked, name) => {
  const found = checked.result.gaps.find(item => item.name === name);
  assert.ok(found, `missing refusal for ${name}`);
  return found;
};
const observationPositions = ({source, observations}) => {
  const start = source.indexOf(observations.scope);
  return [...observations.scope.matchAll(/\b\w+\b/g)]
    .filter(match => match[0] === observations.label).map(match => start + match.index);
};
const validateFixture = ({source, diagnostic, observations, rewrite}) => {
  const contains = (text, fragment, label) => {
    assert.ok(typeof fragment === "string" && fragment.length > 0, `${label} must be nonempty`);
    assert.ok(text.includes(fragment), `${label} must exist in its source`);
  };
  if (diagnostic && ("scope" in diagnostic || "token" in diagnostic)) {
    contains(source, diagnostic.scope, "diagnostic scope");
    contains(diagnostic.scope, diagnostic.token, "diagnostic token");
  }
  if (diagnostic && "conflict" in diagnostic) {
    contains(source, diagnostic.conflict, "diagnostic conflict");
    contains(diagnostic.conflict, "succ(c)", "conflicting binder");
    contains(diagnostic.conflict, "k(c)", "conflicting helper call");
  }
  if (observations) {
    contains(source, observations.scope, "observation scope");
    contains(observations.scope, observations.label, "observation label");
    assert.ok(Number.isInteger(observations.sites) && observations.sites > 0, "observation count must be positive");
    assert.equal(observationPositions({source, observations}).length, observations.sites, "observation sites must match the fixture");
  }
  if (rewrite) {
    contains(source, rewrite.from, "lint rewrite target");
    assert.ok(typeof rewrite.to === "string" && rewrite.to.length > 0, "lint replacement must be nonempty");
    assert.notEqual(rewrite.from, rewrite.to, "lint rewrite must change the source");
  }
};
const coversOriginalToken = (actual, {source, diagnostic}) => {
  const scope = source.indexOf(diagnostic.scope);
  const token = scope + diagnostic.scope.lastIndexOf(diagnostic.token);
  assert.ok(actual.end > actual.start, "diagnostic range must be nonempty");
  assert.ok(actual.start >= scope && actual.end <= scope + diagnostic.scope.length,
    "diagnostic range must stay within the original body or law");
  assert.ok(actual.start <= token && actual.end >= token + diagnostic.token.length,
    `diagnostic range must cover ${diagnostic.token}`);
};

const contracts = {
  G1(checked, t, fixture) {
    accepted(checked, fixture.clients);
    assert.equal(checked.get("N").type, fixture.originalType);
    assert.equal(checked.result.gaps.length, 1);
    assert.match(gap(checked, "N").reason, /already|duplicate/i);
  },
  G2(checked) { complete(checked); accepted(checked, gaps.G2.clients); },
  G3(checked) {
    accepted(checked, gaps.G3.clients);
    for (const prefix of gaps.G3.absentFamilies)
      assert.ok(!checked.result.outputs.some(o => o.name === prefix || o.name.startsWith(prefix + ".")), `${prefix} must not publish a partial family`);
    assert.ok(!checked.result.gaps.some(g => ["E606", "E340"].includes(g.code)), "unsupported transport must not cascade into type errors");
    // Query the refused family through an actual client, including the field,
    // binder and dependency in the diagnostic, without breaking the base T.
    const refusal = gap(checked, "unsupported");
    assert.equal(refusal.code, "E817");
    for (const name of ["op", "p", "l"]) assert.match(refusal.reason, new RegExp(`\\b${name}\\b`));
    assert.match(refusal.reason, /depend|transport|unsupported/i);
  },
  G4(checked, t, fixture) { complete(checked); accepted(checked, fixture.clients); },
  async G5(checked, t, fixture) {
    complete(checked); accepted(checked, fixture.clients);
    const advice = lint(fixture.source).filter(w => ["W705", "W706"].includes(w.code));
    if (advice.length) {
      // This is the rewrite the warning actually recommends. A standalone
      // function type remaining equivalent is insufficient: recheck clients.
      const rewritten = fixture.source.replace(fixture.rewrite.from, fixture.rewrite.to);
      const result = await check(t, rewritten);
      complete(result); accepted(result, fixture.clients);
    }
  },
  G6(checked) {
    accepted(checked, gaps.G6.clients);
    assert.equal(gap(checked, "P").code, "E343");
    assert.equal(gap(checked, "C").code, "E340");
    assert.equal(checked.result.gaps.length, 2);
    assert.match(gap(checked, "C").reason, /\bP\b/);
  },
  G8(checked) {
    const actual = gap(checked, "h"), expected = gaps.G8.diagnostic;
    assert.equal(actual.code, expected.code);
    assert.ok(actual.reason.includes(expected.found)); assert.ok(actual.reason.includes(expected.expected));
    coversOriginalToken(actual, gaps.G8);
  },
  G9(checked) {
    complete(checked); accepted(checked, gaps.G9.clients);
    const {observations} = gaps.G9;
    const positions = observationPositions(gaps.G9), binder = positions[0];
    for (const position of positions) {
      const links = checked.result.links.filter(link => link.start === position && link.end === position + observations.label.length);
      assert.ok(links.length, `missing link at ${position}`);
      for (const link of links) {
        assert.equal(link.name, observations.label);
        assert.equal(link.definitionStart, binder, `definition target at ${position}`);
      }
    }
  },
  G10(checked) {
    const actual = checked.result.gaps[0], {source, diagnostic} = gaps.G10;
    assert.equal(actual?.code, diagnostic.code);
    const conflict = source.indexOf(diagnostic.conflict);
    const binder = conflict + "succ(".length, call = conflict + diagnostic.conflict.indexOf("k(c)");
    assert.ok(actual.end > actual.start, "capture range must be nonempty");
    assert.ok(actual.start >= conflict && actual.end <= conflict + diagnostic.conflict.length);
    assert.ok([binder, call].some(site => actual.start <= site && actual.end > site), "range must cover the conflicting binder or helper call");
  },
  G11(checked) {
    accepted(checked, gaps.G11.clients);
    assert.equal(gap(checked, "captured").code, "E606");
    assert.equal(checked.result.gaps.length, 1);
  },
  G12(checked) { complete(checked); accepted(checked, gaps.G12.clients); },
  "G12-range"(checked) {
    assert.equal(checked.result.gaps.length, 1);
    const actual = gap(checked, "T");
    assert.equal(actual.code, gaps["G12-range"].diagnostic.code);
    coversOriginalToken(actual, gaps["G12-range"]);
  },
};

function contractTest(id, fixture, label = fixture.contract) { test(`${id}: ${label}`, async t => {
  // Fixture mistakes are setup failures, outside the expected-defect catch.
  validateFixture(fixture);
  const checked = await check(t, fixture.source);
  if (!expectedFailures.has(id) || process.env.CUBIST_GENERATION_STRICT === "1") return contracts[id](checked, t, fixture);
  let failure;
  try { await contracts[id](checked, t, fixture); } catch (error) {
    // Infrastructure errors are never an expected compiler defect.
    if (error.code !== "ERR_ASSERTION") throw error;
    failure = error;
  }
  assert.ok(failure, `${id} unexpectedly passed: remove it from expectedFailures and activate its regression`);
  t.todo(`${fixture.phase}: documented open contract; never counts as completion`);
  throw failure;
}); }
const fixtures = [
  ...Object.entries(gaps),
  ...collisionVariants.map(variant => ["G1", {...gaps.G1, ...variant}]),
  ...matchVariants.map(variant => ["G4", {...gaps.G4, ...variant}]),
  ...lintVariants.map(variant => ["G5", {...gaps.G5, ...variant}]),
  ...captureVariants.map(variant => ["G11", {...gaps.G11, source: captureSource(variant), contract: variant.name}]),
];
for (const [id, fixture] of fixtures) contractTest(id, fixture);

test("FG0 maps historical fixes and passing controls to existing executable tests", async () => {
  assert.deepEqual(Object.keys(contracts), Object.keys(gaps));
  for (const [, fixture] of fixtures) validateFixture(fixture);
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
  const refused = await check(t, gaps["G12-range"].source);
  assert.equal(refused.result.gaps[0]?.code, "E845");
});
