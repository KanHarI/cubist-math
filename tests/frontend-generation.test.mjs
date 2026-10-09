import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {checkProgram} from "./check-program.mjs";
import {gaps, expectedFailures, historicalCoverage, passingCoverage, captureVariants, captureSource} from "./fixtures/frontend-generation.mjs";

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

const contracts = {
  G1(checked) {
    accepted(checked, gaps.G1.clients);
    assert.equal(checked.get("N").type, "Unit");
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
  G4(checked) { complete(checked); accepted(checked, gaps.G4.clients); },
  async G5(checked, t) {
    complete(checked); accepted(checked, gaps.G5.clients);
    const advice = lint(gaps.G5.source).filter(w => ["W705", "W706"].includes(w.code));
    if (advice.length) {
      // This is the rewrite the warning actually recommends. A standalone
      // function type remaining equivalent is insufficient: recheck clients.
      const rewritten = gaps.G5.source.replace("forall x, y : M. M", "M -> M -> M");
      const result = await check(t, rewritten);
      complete(result); accepted(result, gaps.G5.clients);
    }
  },
  G6(checked) {
    accepted(checked, gaps.G6.clients);
    assert.equal(gap(checked, "P").code, "E343");
    assert.equal(gap(checked, "C").code, "E340");
    assert.equal(checked.result.gaps.length, 2);
    assert.match(gap(checked, "C").reason, /P/);
  },
  G8(checked) {
    const actual = gap(checked, "h"), expected = gaps.G8.diagnostic;
    assert.equal(actual.code, expected.code);
    assert.ok(actual.reason.includes(expected.found)); assert.ok(actual.reason.includes(expected.expected));
    const start = gaps.G8.source.lastIndexOf("t1");
    assert.equal(actual.start, start); assert.equal(actual.end, start + 2);
  },
  G9(checked) {
    complete(checked); accepted(checked, gaps.G9.clients);
    const {source, observations} = gaps.G9;
    const start = source.indexOf(observations.scope), binder = start + observations.scope.indexOf("c");
    const positions = [...observations.scope.matchAll(/\bc\b/g)].map(match => start + match.index);
    assert.equal(positions.length, observations.sites);
    for (const position of positions) {
      const links = checked.result.links.filter(link => link.start === position && link.end === position + 1);
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
};

function contractTest(id, fixture, label = fixture.contract) { test(`${id}: ${label}`, async t => {
  const checked = await check(t, fixture.source);
  if (!expectedFailures.has(id) || process.env.CUBIST_GENERATION_STRICT === "1") return contracts[id](checked, t);
  let failure;
  try { await contracts[id](checked, t); } catch (error) {
    // Infrastructure errors are never an expected compiler defect.
    if (error.code !== "ERR_ASSERTION") throw error;
    failure = error;
  }
  assert.ok(failure, `${id} unexpectedly passed: remove it from expectedFailures and activate its regression`);
  t.todo(`${fixture.phase}: documented open contract; never counts as completion`);
  throw failure;
}); }
for (const [id, fixture] of Object.entries(gaps)) contractTest(id, fixture);
for (const variant of captureVariants) contractTest("G11", {...gaps.G11, source: captureSource(variant)}, variant.name);

test("FG0 maps historical fixes and passing controls to existing executable tests", async () => {
  assert.deepEqual(Object.keys(contracts), Object.keys(gaps));
  for (const [file, name] of [...Object.values(historicalCoverage), ...passingCoverage]) {
    const source = await readFile(new URL(file, import.meta.url), "utf8");
    assert.ok(source.includes(`test(${JSON.stringify(name)},`), `${file}: ${name}`);
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

test("FG0 controls: explicit path bodies remain checked and recursive type unfolding remains refused", async t => {
  const explicit = await check(t, `import hlevels;
inductive H : set U0 { first; p(y : H) : y = y; }
def k(x : H) : Unit := match x { first => tt; p(y) @ i => k(y); };
def computation : k(first) = tt { rfl; }
`);
  complete(explicit); accepted(explicit, ["k", "computation"]);
  const refused = await check(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  law nope(n : Nat) : iter(n) = c;
}`);
  assert.equal(refused.result.gaps[0]?.code, "E845");
});
