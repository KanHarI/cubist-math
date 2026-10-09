import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const module = await createCubical();
const check = (t,source,fixtures={}) => {
  const library = sourceReader();
  return checkProgram(t,source,{module,reader:(name,importer)=>fixtures[name]??library(name,importer)});
};

test("FG2: helper capture preserves named calls through a grouped dependent telescope", async t => {
  const {result,get} = await check(t,`import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x,c);
  def kk(c, d : M, p : c = c) : M := k(c);
}
def intended(S : T(U0), x : S.M) : T.kk(S, c := x, d := x, p := refl(x)) = S.op(x,S.c) { rfl; }
def captured(S : T(U0), x : S.M) : T.kk(S, c := x, d := x, p := refl(x)) = S.op(x,x) { rfl; }`);
  assert.equal(get("intended").verified,true,get("intended").reason);
  assert.deepEqual(get("intended").axioms,[]);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["captured","E606"]]);
});

test("FG2: imported and renamed inheritance transforms helper telescopes without capturing a parameter", async t => {
  const {result,get} = await check(t,`import fixture;
theory Child(U < UU0) extends P(c := d) {}
def intended(S : Child(U0), x : S.M) : Child.k(S, d := x) = S.op(x,S.d) { rfl; }
def captured(S : Child(U0), x : S.M) : Child.k(S, d := x) = S.op(x,x) { rfl; }
initial N : Child(U0);
def computation(x : N) : Child.k(N.model, d := x) = N.op(x,N.d) { rfl; }`,{
    fixture:`import hlevels;
theory P(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(d : M) : M := op(d,c);
}`});
  for(const name of ["intended","computation"]) {
    assert.equal(get(name).verified,true,get(name).reason);
    assert.deepEqual(get(name).axioms,[]);
  }
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["captured","E606"]]);
});

test("FG2: earlier recursive value calls compute through import, inheritance and a generated model", async t => {
  const {result,get} = await check(t,`import fixture;
theory Child(U < UU0) extends P {}
initial N : Child(U0);
def inherited(S : Child(U0)) : S.twice(zero) = S.op(S.c) { rfl; }
def generated : N.model.twice(succ(zero)) = N.op(N.op(N.c)) { rfl; }`,{
    fixture:`import hlevels; import nat;
theory P(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def twice(n : Nat) : M := op(iter(n));
}`});
  assert.deepEqual(result.gaps,[]);
  for(const name of ["inherited","generated"])assert.deepEqual(get(name).axioms,[]);
});

test("FG2: a recursive call in a later derived parameter type still receives the type-unfolding refusal", async t => {
  const source = `import hlevels; import nat;
theory P(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def with_proof(n : Nat, p : iter(n) = c) : M := c;
}`;
  const {result} = await check(t,source);
  assert.equal(result.gaps.length,1);
  assert.equal(result.gaps[0].code,"E845");
  assert.equal(source.slice(result.gaps[0].start,result.gaps[0].end),"iter(n)");
});
