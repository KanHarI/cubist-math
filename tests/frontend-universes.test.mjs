import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const module=await createCubical();
const check=(t,source,fixtures={})=>{
  const library=sourceReader();
  return checkProgram(t,source,{module,reader:(name,importer)=>fixtures[name]??library(name,importer)});
};
const checked=(get,names)=>{
  for(const name of names) {
    assert.equal(get(name).verified,true,`${name}: ${get(name).reason}`);
    assert.deepEqual(get(name).axioms,[],name);
    assert.doesNotMatch(get(name).type,/\u0000|__theory/);
  }
};

test("FG3: fixed U0/U1 domains and dependent proofs determine the least generated universe",async t=>{
  for(const level of [0,1])for(const inherited of [false,true]) {
    const parent=`import hlevels;
theory P(U < UU0) { M : set U; op(A : U${level}, x : A, p : x = x) : M; }`;
    const source=`${inherited?"import fixture; theory T(U < UU0) extends P {}":parent.replace("theory P(","theory T(")}
def model_level : U${level+1} := T(U0);
def hom_level(S : T(U0)) : U${level+1} := T.Hom(S,S);
def iso_level(S : T(U0)) : U${level+1} := T.Iso(S,S);
def identity(S : T(U0)) : T.Hom(S,S) := T.Hom.id(S);
def preservation(S : T(U0), h : T.Hom(S,S), A : U${level}, x : A, p : x = x) :
  h.map(S.op(A,x,p)) = S.op(A,x,p) := h.map_op(A,x,p);
def composition(S : T(U0), x : S.M) : T.Hom.compose(identity(S),identity(S)).map(x) = x { rfl; }
def inverse_computation(S : T(U0), x : S.M) : T.Iso.inverse(T.Iso.id(S)).to.map(x) = x { rfl; }
def too_low(S : T(U0)) : U${level} := T.Hom(S,S);
def iso_too_low(S : T(U0)) : U${level} := T.Iso(S,S);`;
    const {result,get}=await check(t,source,{fixture:parent});
    assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["too_low","E606"],["iso_too_low","E606"]]);
    checked(get,["T","T.Hom","T.Iso","model_level","hom_level","iso_level","identity","preservation","composition","inverse_computation"]);
    for(const gap of result.gaps) {
      assert.match(gap.reason,new RegExp(`U${level+1}`));
    }
  }
});

test("FG3: generic fixed domains retain shared universes and their successor contribution",async t=>{
  const {result,get}=await check(t,`import hlevels;
theory T(U < UU0) { M : set U; op(A : U, x : A) : M; }
def hom_level(U < UU0, S : T(U)) : next(U) := T.Hom(S,S);
def iso_level(U < UU0, S : T(U)) : next(U) := T.Iso(S,S);
def identity(U < UU0, S : T(U)) : T.Hom(S,S) := T.Hom.id(S);
def composition(U < UU0, S : T(U), x : S.M) : T.Hom.compose(identity(U,S),identity(U,S)).map(x) = x { rfl; }
def too_low(U < UU0, S : T(U)) : U := T.Hom(S,S);
def incompatible(U, V < UU0, S : T(U), R : T(V)) := T.Hom(S,R);`);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["too_low","E606"],["incompatible","E606"]]);
  checked(get,["hom_level","iso_level","identity","composition"]);
});

test("FG3: multiple header universes use the full telescope rather than a blanket successor",async t=>{
  const {result,get}=await check(t,`import hlevels;
theory T(U, V < UU0) { M : set U; op(A : V, x : A) : M; }
def model_level(U, V < UU0) : max(next(U),next(V)) := T(U,V);
def hom_level(U, V < UU0, S : T(U,V)) : max(U,next(V)) := T.Hom(S,S);
def iso_level(U, V < UU0, S : T(U,V)) : max(U,next(V)) := T.Iso(S,S);
def identity(U, V < UU0, S : T(U,V)) : T.Hom(S,S) := T.Hom.id(S);
def composite(U, V < UU0, S : T(U,V), x : S.M) : T.Hom.compose(identity(U,V,S),identity(U,V,S)).map(x) = x { rfl; }
def too_low(S : T(U0,U1)) : U1 := T.Hom(S,S);`);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["too_low","E606"]]);
  checked(get,["model_level","hom_level","iso_level","identity","composite"]);
});

test("FG3: dependent fixed family indices contribute to Hom and Iso universes",async t=>{
  const {result,get}=await check(t,`import hlevels;
theory T(U < UU0) { F(A : U1, a : A) : set U; point(A : U1, a : A) : F(A,a); }
def hom_level(S : T(U0)) : U2 := T.Hom(S,S);
def iso_level(S : T(U0)) : U2 := T.Iso(S,S);
def identity(S : T(U0)) : T.Hom(S,S) := T.Hom.id(S);
def composite(S : T(U0), A : U1, a : A, x : S.F(A,a)) : T.Hom.compose(identity(S),identity(S)).map(A,a,x) = x { rfl; }
def inverse_computation(S : T(U0), A : U1, a : A, x : S.F(A,a)) : T.Iso.inverse(T.Iso.id(S)).to.map(A,a,x) = x { rfl; }
def too_low(S : T(U0)) : U1 := T.Hom(S,S);`);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["too_low","E606"]]);
  checked(get,["hom_level","iso_level","identity","composite","inverse_computation"]);
});
