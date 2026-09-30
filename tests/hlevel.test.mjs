import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { SEARCH_FUEL } from "../lib/cubical/fuel.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// The hlevel tactic (work-plan L2.5b, the HoTT roadmap's D1): it proves
// h-level statements, and equalities in propositions, from the lemmas of
// library/hlevels.cubist, evidence in scope and hints, under counted fuel.
async function check(t, source, options = {}) {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false, ...options });
  t.after(() => program.dispose());
  const result = await program.check(source, "main");
  return { program, result, get: name => {
    const found = result.outputs.find(output => output.name === name);
    assert.ok(found, `no declaration ${name}`);
    return found;
  } };
}
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};

test("hlevel proves each kind of goal, from evidence, hints and the type's shape", async t => {
  const proved = {
    unit_contractible: "IsContr(U0, Unit)",
    void_proposition: "IsProp(U0, Void)",
    nat_set: "IsSet(U0, Nat)",
    nat_groupoid: "HasLevel(U0, 2, Nat)",
    functions_into_nat: "IsSet(U0, Nat -> Nat)",
    pairs_of_numbers: "IsSet(U0, Nat and Nat)",
    functions_into_unit: "IsContr(U0, Nat -> Unit)",
    paths_of_numbers: "IsProp(U0, 3 = 3)",
    level_statement: "IsProp(U0, IsSet(U0, Nat))",
    parallel_paths: "forall p, q : 0 = 0. p = q",
  };
  const { get } = await check(t, `import hlevels;
${Object.entries(proved).map(([name, type]) => `def ${name} : ${type} { ${type.startsWith("forall") ? "intro p, q; " : ""}hlevel; }`).join("\n")}
def lifted(A : U0, h : IsProp(U0, A)) : HasLevel(U0, 3, A) { hlevel; }
def from_contractible(A : U0, c : IsContr(U0, A)) : IsSet(U0, A -> A) { hlevel; }
def in_u1(A : U1, h : IsSet(U1, A)) : IsSet(U1, (A -> A) and A) { hlevel; }
def equal_in_prop(A : U0, h : IsProp(U0, A), x, y : A) : x = y { hlevel; }
def from_hint(A : U0, B : A -> U0, h : forall x : A. IsProp(U0, B(x)), a : A) : IsSet(U0, B(a) and Nat) {
  hlevel with [h(a)];
}
def after_intro : forall A : U0. IsSet(U0, A) -> IsSet(U0, A -> A) { intro A, h; hlevel; }
def after_universe_intro : forall U < UU0. IsSet(U, Nat) { intro U; hlevel; }
def after_universe_intros : forall U < UU0. forall A : U. IsSet(U, A) -> IsSet(U, A and (Unit -> A)) { intro U, A, h; hlevel; }
def from_have(A : U0, p : Unit -> IsProp(U0, A)) : IsProp(U0, A) { let h := p(tt); hlevel; }
def from_have_block(A : U0, p : Unit -> IsProp(U0, A)) : IsSet(U0, A and A) {
  let h : IsProp(U0, A) { exact p(tt); }
  hlevel;
}
def from_let(A : U0, p : Unit -> IsContr(U0, A)) : IsSet(U0, A) { let c := p(tt); hlevel; }
def from_obtain(A : U0, q : IsProp(U0, A) and Nat) : IsSet(U0, A) { obtain (h, n) := q; hlevel; }
def prop_at_any_level(n : Nat, A : U0, h : IsProp(U0, A)) : HasLevel(U0, n, A) { hlevel; }
def contractible_at_any_level(n : Nat, A : U0, c : IsContr(U0, A)) : HasLevel(U0, n, A) { hlevel; }
def statement_at_any_level(n : Nat, A : U0) : HasLevel(U0, n, IsSet(U0, A)) { hlevel; }
def same_variable_level(n : Nat, A : U0, h : HasLevel(U0, n, A)) : HasLevel(U0, n, A -> A) { hlevel with [h]; }
computable def computable_evidence : IsSet(U0, Nat -> (Nat and Unit)) { hlevel; }
def any_universe(U < UU0, A : U, h : IsSet(U, A)) : IsSet(U, (A -> A) and (Unit -> A)) { hlevel; }
def variable_statement(n : Nat, A : U0) : IsProp(U0, HasLevel(U0, n, A)) { hlevel; }
`);
  // Every proof is built from computable lemmas and uses no assumption, so
  // it may be marked computable.
  for (const name of [...Object.keys(proved), "lifted", "from_contractible", "in_u1", "equal_in_prop", "from_hint",
    "after_intro", "after_universe_intro", "after_universe_intros", "from_have", "from_have_block", "from_let", "from_obtain",
    "prop_at_any_level", "contractible_at_any_level", "statement_at_any_level", "computable_evidence", "any_universe",
    "variable_statement"]) {
    ok(get(name));
    assert.deepEqual(get(name).axioms, [], name);
  }
  // Structural rules need a numeral: a variable level is given only by
  // evidence at that level.
  refused(get("same_variable_level"), /^hlevel could not prove HasLevel\(U0, n, A -> A\); nothing in scope states that A -> A has level n\./);
});

// The HoTT roadmap's D completion: IsProp of an arbitrary type and 0 = 1
// stay unproved, the second with Nat a set.
test("hlevel checks dependent path h-levels using evidence at the line's start", async t => {
  const {get} = await check(t, `import hlevels;
def path_prop(A, B : U0, e : A = B, h : IsSet(U0, A), a : A, b : B) :
  IsProp(U0, PathP(fun (i : Interval) => e @ i, a, b)) { hlevel; }
def path_contr(A, B : U0, e : A = B, h : IsContr(U0, A), a : A, b : B) :
  IsContr(U0, PathP(fun (i : Interval) => e @ i, a, b)) { hlevel; }
def no_evidence(A, B : U0, e : A = B, a : A, b : B) :
  IsProp(U0, PathP(fun (i : Interval) => e @ i, a, b)) { hlevel; }
`);
  ok(get("path_prop")); ok(get("path_contr"));
  refused(get("no_evidence"), /hlevel could not prove.*no local evidence/);
});

test("hlevel refuses, naming the first obligation nothing discharges", async t => {
  const { get } = await check(t, `import hlevels;
def zero_is_one : 0 = 1 { hlevel; }
def nat_prop : IsProp(U0, Nat) { hlevel; }
def arbitrary(A : U0) : IsProp(U0, A) { hlevel; }
def nested(A, B : U0) : IsSet(U0, A -> (Nat and B)) { hlevel; }
def dependent(A : U0, B : A -> U0) : IsProp(U0, forall x : A. B(x)) { hlevel; }
def void_contractible : IsContr(U0, Void) { hlevel; }
def not_a_level : Nat { hlevel; }
def variable_level(n : Nat, A : U0) : HasLevel(U0, n, A) { hlevel; }
def unreachable : IsProp(U0, Unit) { hlevel; rfl; }
def other_universe(n : Nat, A : U0, h : HasLevel(U1, n, A)) : HasLevel(U0, n, A) { hlevel; }
def not_a_statement(A : U0, a : A) : IsProp(U0, Unit) { hlevel with [a]; }
def without_hint(A : U0, B : A -> U0, h : forall x : A. IsProp(U0, B(x)), a : A) : IsSet(U0, B(a) and Nat) { hlevel; }
def nested_names(A : U0, B : A -> U0) : IsProp(U0, forall x : A. Unit and B(x)) { hlevel; }
def quantified_hint(A : U0, B : A -> U0, h : forall x : A. IsProp(U0, B(x)), a : A) : IsProp(U0, B(a)) {
  hlevel with [h];
}
`);
  refused(get("zero_is_one"), /^hlevel could not prove 0 = 1; Nat is not a proposition: 0 and 1 differ\./);
  refused(get("nat_prop"), /^hlevel could not prove IsProp\(U0, Nat\); Nat is not a proposition/);
  refused(get("arbitrary"), /^hlevel could not prove IsProp\(U0, A\); no local evidence, hint or rule gives that\./);
  refused(get("nested"), /^hlevel could not prove IsSet\(U0, A -> Nat and B\): it needs Nat and B to be a set, which needs B to be a set; no local evidence, hint or rule gives that\./);
  refused(get("dependent"), /^hlevel could not prove IsProp\(U0, forall x : A\. B\(x\)\): it needs B\(x\) to be a proposition for every x : A;/);
  refused(get("void_contractible"), /Void is empty, so it is not contractible/);
  refused(get("not_a_level"), /^hlevel proves IsContr, IsProp, IsSet or HasLevel, or an equality in a proposition; the goal is Nat\./);
  refused(get("variable_level"), /nothing in scope states that A has level n/);
  refused(get("unreachable"), /Statements after hlevel are unreachable\./);
  // At a variable level HasLevel does not reduce, so evidence in another
  // universe states something else.
  refused(get("other_universe"), /nothing in scope states that A has level n\./);
  refused(get("not_a_statement"), /^The hint a has type A, which states no h-level\./);
  // A quantified hypothesis is no evidence until applied: from_hint's hint is needed.
  refused(get("without_hint"), /^hlevel could not prove IsSet\(U0, B\(a\) and Nat\): it needs B\(a\) to be a set; no local evidence, hint or rule gives that\./);
  // Each binder the search goes under keeps its name, however deep.
  refused(get("nested_names"), /^hlevel could not prove IsProp\(U0, forall x : A\. Unit and B\(x\)\): it needs Unit and B\(x\) to be a proposition for every x : A, which needs B\(x\) to be a proposition; no local evidence, hint or rule gives that\./);
  refused(get("quantified_hint"), /^hlevel does not use quantified hints yet: apply h to its arguments\./);
});

test("hlevel names the library module it needs", async t => {
  const { get } = await check(t, "def nat_equal(p, q : 0 = 0) : p = q { hlevel; }\n");
  refused(get("nat_equal"), /^hlevel uses the library module hlevels: add import hlevels;/);
});

test("the search spends counted fuel, the same on every run, and stops when it runs out", async t => {
  const source = "import hlevels;\ndef deep : IsSet(U0, Nat -> (Nat and (Nat -> Nat))) { hlevel; }\n";
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
  const source = "import hlevels;\n\ndef hinted(A : U0, h : Unit -> IsSet(U0, A)) : IsSet(U0, A and Nat) {\n  hlevel with [h(tt)];\n}\n";
  const { program, get } = await check(t, source, { collectReferences: true });
  ok(get("hinted"));
  const link = program.links.find(item => item.role === "h-level evidence");
  assert.ok(link, "a link from the hlevel keyword");
  assert.equal(source.slice(link.start, link.end), "hlevel");
  assert.match(link.description, /Checked h-level evidence with 1 hint\./);
  const statement = parse(source).declarations[0].body[0];
  assert.equal(statement.kind, "hlevel");
  assert.equal(statement.hints.length, 1);
  assert.equal(formatMathScript(source), source);
});
