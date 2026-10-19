import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { SEARCH_FUEL } from "../web/translator/fuel.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { checkProgram, testModule } from "./check-program.mjs";

// The hlevel tactic (work-plan L2.5b, the HoTT roadmap's D1): it proves
// h-level statements, and equalities in propositions, from the lemmas of
// library/hlevels.cubist, evidence in scope and hints, under counted fuel.
// Its cases and refusals are cubist-tests/hlevel_tactic.cubist and
// hlevel_without_import.cubist, whose comments state each refusal
// (tests/cubist-tests.test.mjs); here, what a verdict does not show.
const tactic = testModule("hlevel_tactic");
const check = (t, source, options = {}) => checkProgram(t, source, { options: { collectReferences: false, ...options } });
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);

// Every proof hlevel builds is made of computable lemmas and uses no
// assumption, so it may be marked computable.
test("hlevel's proofs use no assumption", async () => {
  const { result } = await tactic();
  const proved = result.outputs.filter(output => output.verified && /^(?:def|computable)/.test(output.kind ?? "def"));
  assert.ok(proved.length > 25);
  for (const output of proved) assert.deepEqual(output.axioms, [], output.name);
});

test("the search spends counted fuel, the same on every run, and stops when it runs out", async t => {
  const source = "import hlevels;\ndef deep : IsSet(U0, UNat -> (UNat and (UNat -> UNat))) { hlevel; }\n";
  const first = await check(t, source), second = await check(t, source);
  ok(first.get("deep"));
  assert.deepEqual(first.get("deep").searchFuel, second.get("deep").searchFuel, "the same fuel on every run");
  const starved = await check(t, source, { searchFuel: { ...SEARCH_FUEL, premises: 2 } });
  const stopped = starved.get("deep");
  assert.equal(stopped.verified, false);
  assert.equal(stopped.failure, "fuel");
  assert.match(stopped.reason, /hlevel ran out of search fuel: 2 premise searches\./);
});

test("the keyword links to the checked proof, and the formatter keeps hints", async t => {
  const source = "import hlevels;\n\ndef hinted(A : U0, h : Unit -> IsSet(U0, A)) : IsSet(U0, A and UNat) {\n  hlevel with [h(tt)];\n}\n";
  const { program, get } = await check(t, source, { collectReferences: true });
  ok(get("hinted"));
  const link = program.links.find(item => item.role === "h-level evidence");
  assert.ok(link, "a link from the hlevel keyword");
  assert.equal(source.slice(link.start, link.end), "hlevel");
  assert.match(link.description, /Checked h-level evidence with 1 hint\./);
  const statement = parse(source).declarations[0].body[0];
  assert.equal(statement.kind, "hlevel");
  assert.equal(statement.hints.length, 1);
  assert.equal(formatCubist(source), source);
});

// A setness field left out of T.make(…) is filled by the search plain hlevel
// runs, from evidence a local definition names too. The lint reads syntax
// only and does not see that use of h, so this case is here rather than in
// cubist-tests/hlevel_rules.cubist.
test("a setness field is filled from evidence a local definition names", async t => {
  const source = `import hlevels;
theory Pointed(U < UU0) { M : set U; point : M; }
def local_point(A : U0, a : A, evidence : Unit -> IsSet(U0, A)) : Pointed(U0) {
  let h := evidence(tt);
  exact Pointed.make(M := A, point := a);
}
`;
  const { get } = await check(t, source);
  ok(get("local_point"));
});

test("a constant quotient motive generates no dependent transports in its squash clause", async t => {
  const { program, get } = await check(t,`import quotients; import propositions;
def Same(a, b : Unit) : U0 := Unit;
computable def direct(x : Quotient(U0, Unit, Same)) : Prop(U0) :=
  match x return Prop(U0) { class(a) => (Unit, unit_is_prop); }
obligations { relate(a, b, r) @ i => typed(Prop(U0), (Unit, unit_is_prop)); };
`);
  ok(get("direct"));
  assert.deepEqual(get("direct").axioms,[]);
  // The old dependence test read the ignored argument of (λ_. Prop)(q),
  // even under another Path, and emitted four compositions. Normalizing
  // that checked definition exceeded the kernel's syntax-depth bound.
  const pending=[program.checker.definitionViews.get("main__direct").term],seen=new WeakSet();
  let eliminators=0;
  while(pending.length) {
    const term=pending.pop();
    if(!term||typeof term!=="object"||seen.has(term))continue;
    seen.add(term);
    if(term.tag==="Elim")eliminators++;
    assert.notEqual(term.tag,"Comp","a homogeneous squash clause needs no transport");
    pending.push(...Object.values(term));
  }
  assert.equal(eliminators,1,"inspect the generated eliminator, not a reference to it");
});

test("hlevel recognizes a beta-constant path family as a structural goal", async t => {
  const { program, get } = await check(t, `import hlevels;
computable def constant_level(p : tt = tt) :
  IsProp(U0, PathP(fun (i : Interval) => (fun (ignored : Unit) => Unit)(p @ i), tt, tt)) {
  hlevel;
}
`);
  ok(get("constant_level"));
  assert.deepEqual(get("constant_level").axioms, []);
  const pending = [program.checker.definitionViews.get("main__constant_level").term], seen = new WeakSet();
  while (pending.length) {
    const term = pending.pop();
    if (!term || typeof term !== "object" || seen.has(term)) continue;
    seen.add(term);
    assert.notEqual(term.tag, "Comp", "a constant-family h-level goal needs no transport");
    pending.push(...Object.values(term));
  }
});

test("reduced quotient motives retain checked path applications before head queries", async t => {
  for (const carrier of ["P @ 0", "(fun (R : Unit = Unit) => R @ 0)(P)"]) {
    const { get } = await check(t, `import quotients; import hlevels;
def Same(a, b : Unit) : U0 := Unit;
computable def direct(P : Unit = Unit, x : Quotient(U0, Unit, Same)) : ${carrier} :=
  match x return ${carrier} { class(u) => tt; }
obligations { relate(u, v, r) @ i => typed(${carrier}, tt); };
`);
    ok(get("direct"));
    assert.deepEqual(get("direct").axioms, []);
  }
});
