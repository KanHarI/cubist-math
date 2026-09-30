import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { validateLedger } from "../tools/migration-ledger.mjs";
import { execFileSync } from "node:child_process";

const module = await createCubical();
async function check(t,source) {
  const program=new CubicalProgram(module,sourceReader(),{experimental:["h1"]});
  t.after(()=>program.dispose());
  const result=await program.check(source,"migration_cases");
  const get=name=>[...result.outputs,...result.imports].find(output=>output.name===name);
  const assumptions=output=>output.axioms.map(name=>result.assumptionLabels[name] ?? name).sort();
  return {program,result,get,assumptions};
}

test("G2: small_mere_eliminate uses the declared eliminator into U1 without assumptions",async t=>{
  const {result,get,assumptions}=await check(t,`import h1_truncation;
computable def replay(A : U0, P : U1, prop : IsProp(U1, P), f : A -> P, h : Trunc(U0, A)) : P :=
  small_mere_eliminate(A, P, prop, f, h);
computable def computes : small_mere_eliminate(Unit, Unit, unit_is_prop, fun (x : Unit) => tt, point(tt)) = tt { rfl; }
`);
  assert.ok(result.complete,JSON.stringify(result.gaps));
  assert.deepEqual(assumptions(get("replay")),[]);
  assert.deepEqual(get("replay").extensions,["H1"]);
});

test("G5: the rebuilt CauchySame relation and EventualClose stay in U0 without assumptions",async t=>{
  const {result,get,assumptions}=await check(t,`import cauchy_quotient;
computable def relation(Q : U0, zero : Q, addQ : Q -> Q -> Q, ltQ : Q -> Q -> U0,
    x, y : CauchySequence(Q, zero, addQ, ltQ)) : U0 := CauchySame(Q, zero, addQ, ltQ, x, y);
`);
  assert.ok(result.complete,JSON.stringify(result.gaps));
  for(const name of ["EventualClose","CauchySame","relation"]) {
    assert.ok(get(name)?.verified,name); assert.deepEqual(assumptions(get(name)),[],name);
  }
});

test("G6: resizing a proposition uses only LEM; a StrictlyAbove witness cannot use set evidence",async t=>{
  const {get,assumptions}=await check(t,`import h1_zorn_step;
def resized(P : U1, prop : IsProp(U1, P)) : PropResize(P) := resize_prop(P, prop);
def rejected(A : U1, le : OrderRelation(A), laws : PartialOrderLaws(A, le), x : A) :=
  resize_prop(StrictlyAbove(A, le, x), strict_above_is_set(A, le, laws, x));
`);
  assert.ok(get("resized")?.verified,get("resized")?.reason);
  assert.deepEqual(assumptions(get("resized")),["LEM"]);
  assert.equal(get("rejected").verified,false);
  assert.match(get("rejected").reason,/mismatch/i);
});

test("G7: no_maximal_strict_successor applies double negation at U1 and retains LEM",async t=>{
  const {get,assumptions}=await check(t,`import h1_zorn_step;
def replay(A : U1, le : OrderRelation(A), laws : PartialOrderLaws(A, le),
    none : Trunc(U1, exists x : A. OrderMaximal(A, le, x)) -> Void, x : A) : Trunc(U1, StrictlyAbove(A, le, x)) :=
  no_maximal_strict_successor(A, le, laws, none, x);
`);
  assert.ok(get("replay")?.verified,get("replay")?.reason);
  assert.deepEqual(assumptions(get("replay")),["LEM"]);
});

test("G4: the checked migration ledger has exact pins and defers the H2 tower declarations",async()=>{
  const ledger=JSON.parse(await readFile(new URL("../docs/roadmaps/h1-truncation-ledger.json",import.meta.url),"utf8"));
  assert.equal(validateLedger(ledger).size,17);
  assert.deepEqual(ledger.deferred,["tower_induction_large","tower_relative_induction"]);
});

test("G4: the CLI uses a pinned library baseline and refuses a new module without a baseline",()=>{
  const args=["tools/verify-proof-migration.mjs","--base","HEAD","--experimental","h1","--no-dependents",
    "--edited-file","library/h1_classical.cubist"];
  const report=execFileSync(process.execPath,[...args,"--declarations",
    "ExcludedMiddle,AxiomOfChoice,excluded_middle_assumed,axiom_of_choice_assumed",
    "--ledger","docs/roadmaps/h1-truncation-ledger.json","classical_axioms"],{encoding:"utf8"});
  assert.match(report,/4 exact ledger changes/); assert.match(report,/0 failures/);
  assert.throws(()=>execFileSync(process.execPath,[...args,"migration_no_baseline_fixture"],{stdio:"pipe"}),
    error=>error.status===1 && /No baseline for compared module migration_no_baseline_fixture/.test(String(error.stderr)));
});

test("rebuilt classical assumptions coexist with legacy signatures and reject a false truncation former",async t=>{
  const {get,assumptions}=await check(t,`import h1_classical;
def old(P : U1, h : (P -> Void) -> Void) := LEM(U1, P, h);
def rebuilt(P : U1, h : (P -> Void) -> Void) : Trunc(U1, P) := LEM(Trunc, U1, P, h);
inductive Empty(U < UU0, A : U) : prop U {}
def rejected(P : U1, h : (P -> Void) -> Void) := LEM(Empty, U1, P, h);
`);
  assert.ok(get("old").verified); assert.ok(get("rebuilt").verified);
  assert.deepEqual(assumptions(get("old")),["LEM","Truncate"]);
  assert.deepEqual(assumptions(get("rebuilt")),["LEM"]);
  assert.equal(get("rejected").verified,false);
  assert.match(get("rejected").reason,/admitted proposition truncation/);
});
