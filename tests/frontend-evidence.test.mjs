import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {Scope,SourceUnit} from "../web/translator/elaboration.mjs";
import {T} from "../web/translator/core.mjs";
import {BindingAdapter} from "../web/cubist/bindings.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";
import {interval as I} from "../web/translator/lattice.mjs";

const module=await createCubical();
const check=(t,source,fixtures={},options={})=>{
  const library=sourceReader();
  return checkProgram(t,source,{module,reader:(name,importer)=>fixtures[name]??library(name,importer),options});
};
const accepts=(result,get,names)=>{
  assert.deepEqual(result.gaps,[]);
  for(const name of names) {
    assert.equal(get(name).verified,true,get(name).reason);
    assert.deepEqual(get(name).axioms,[]);
  }
};

test("CB3: evidence ignores dimension, constructor and lazy operand aliases",async t=>{
  const body=`
inductive Circle { base; loop : base = base; }
inductive Bit { off; yes; }
def coordinate(x : Circle, b : Bit) : Circle := match x, b {
  base, off => base; base, yes => base;
  loop @ i, off => loop @ i; loop @ j, yes => loop @ j;
};
def coordinate_value : coordinate(base, yes) = base { rfl; }
def coordinate_loop : base = base := path k => coordinate(loop @ k, yes);
def coordinate_path : coordinate_loop = loop { rfl; }
def wrong_path : coordinate_loop = refl(base) { rfl; }
def constructor(b : Bit) : Nat := match zero, b { n, off => n; n, yes => succ(n); };
def constructor_value : constructor(yes) = succ(zero) { rfl; }
def wrong_constructor : constructor(yes) = zero { rfl; }
notation pick { x + y := match x, y { zero, m => m; succ(n), m => succ(m); }; }
def operand : Nat := pick.(succ(zero) + succ(zero));
def operand_value : operand = succ(succ(zero)) { rfl; }
def wrong_operand : operand = succ(zero) { rfl; }`;
  for(const context of ["", "theory T(U < UU0) { M : set U; }", "import algebra;"]) {
    const {result,get}=await check(t,`import nat; import hlevels; ${context}\n${body}`);
    assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),
      [["wrong_path","E606"],["wrong_constructor","E606"],["wrong_operand","E606"]],JSON.stringify(result.gaps));
    for(const name of ["coordinate_value","coordinate_path","constructor_value","operand_value"])
      assert.equal(get(name).verified,true,get(name).reason);
  }
});

test("CB3: dependent motives rebuild evidence for generalized model parameters",async t=>{
  const {result,get}=await check(t,`import hlevels; import nat;
inductive Bit : set U0 { off; yes; }
theory T(U < UU0, n : Nat) { M : set U; c : M; }
def unit_set : IsSet(U0,Unit) { hlevel; }
def value(n : Nat, S : T(U0,n), b : Bit) : S.M {
  match n {
    zero => { exact S.c; }
    succ(k) => {
      let unused := value(k,T.make(k,Unit,unit_set,tt),b);
      exact match b { off => S.c; yes => S.c; };
    }
  }
}
def computation(S : T(U0,succ(zero))) : value(succ(zero),S,yes) = S.c { rfl; }`);
  accepts(result,get,["value","computation"]);
});

test("CB3: nested matches specialize checked evidence for a dependent carrier family",async t=>{
  const {result,get}=await check(t,`import hlevels;
inductive Bit : set U0 { off; yes; }
inductive Bits : set U0 { nil; cons(b : Bit, rest : Bits); }
theory Indexed(U < UU0, A : U0) { F(a : A) : set U; point(a : A) : F(a);
  def value(a : A, b : Bits) : F(a) := match b { nil => point(a); cons(off,rest) => point(a); cons(yes,rest) => point(a); };
}
def computation(A : U0, S : Indexed(U0,A), a : A) : S.value(a,cons(yes,nil)) = S.point(a) { rfl; }`);
  accepts(result,get,["Indexed.value","computation"]);
});

test("CB3: checked evidence for one model cannot justify elimination into another model",async t=>{
  const {result,get}=await check(t,`import hlevels;
inductive Bit : set U0 { off; yes; }
theory Good(U < UU0) { M : set U; c : M; }
theory Raw(U < UU0) { M : U; c : M; }
def unsupported(good : Good(U0), raw : Raw(U0), b : Bit) : raw.M := match b { off => raw.c; yes => raw.c; };
def available(good : Good(U0)) : IsSet(U0,good.M) { hlevel; }`);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["unsupported","E546"]]);
  assert.equal(get("available").verified,true,get("available").reason);
  assert.deepEqual(get("available").axioms,[]);
});

test("CB3: contextual model evidence remains checked after refinement and dimension restriction",async t=>{
  const {program,result,get}=await check(t,`import hlevels;
theory T(U < UU0) { M : set U; c : M; }`);
  assert.deepEqual(result.gaps,[]);
  const record=[...program.checker.theories.values()].find(record=>record.name==="T");
  const field=record.fields.find(field=>field.kind==="evidence");
  const adapter=new BindingAdapter(program.compilationBindings.table);
  const env=new Map([[adapter.key(field.projectionId),{tag:"DefRef",name:get("T.M_is_set").binding}]]);
  const modelType=T.levelApply({tag:"DefRef",name:get("T").binding},0);
  const unit=new SourceUnit({checker:program.checker});
  for(const value of [undefined,{tag:"Untranslated",reason:"refused"}]) {
    const unavailable=new Map([[field.projection,env.get(adapter.key(field.projectionId))]]);
    if(value)unavailable.set(adapter.key(field.projectionId),value);
    assert.equal(new Scope(unit,new Map(),unavailable).bind("S",modelType).evidence.length,0,
      "the exact checked projection is required; a public spelling grants nothing");
  }
  const scope=new Scope(unit,new Map(),env).bind("S",modelType).bind("R",modelType)
    .bind("p",T.path("j",modelType,T.variable("S"),T.variable("R"))).bindDimension("i");
  const lexical=scope.sourceBinding("local",scope.evidence[0].term,null,{name:"local"}).enterLexicalBody();
  const refined=lexical.refineEvidence(new Map([["S",T.variable("R")]]));
  assert.ok(scope.equal(scope.evidence[0].model,T.variable("S")));
  assert.ok(refined.equal(refined.evidence[0].model,T.variable("R")));
  refined.check(refined.evidence[0].term,refined.evidence[1].type);
  refined.check(refined.inheritedDefinitions[0],refined.evidence[1].type);
  const along=scope.modelEvidence(T.at(T.variable("p"),I.variable("i")),modelType)
    .sourceBinding("local",T.at(T.variable("p"),I.variable("i")),null,{name:"local"}).enterLexicalBody();
  for(const [endpoint,model] of [[0,"S"],[1,"R"]]) {
    const face=along.onFace([[`i:${endpoint}`]]),witness=face.evidence.at(-1);
    assert.ok(face.equal(witness.model,T.variable(model)));
    const original=scope.evidence.find(e=>e.model.name===model);
    face.check(witness.term,original.type);
    face.check(face.inheritedDefinitions[0],modelType);
    assert.ok(face.equal(face.inheritedDefinitions[0],T.variable(model)));
    assert.deepEqual(witness.dependencies,[record.modelId,field.projectionId]);
  }
});

test("CB3: isolated query replay carries checked model evidence across scratch entries",async t=>{
  const source=`import hlevels;
theory T(U < UU0) { M : set U; c : M; }
def f(S : T(U0)) : Unit := tt;`;
  const {program,result}=await check(t,source,{}, {collectScopes:true});
  assert.deepEqual(result.gaps,[]);
  const points=[...program.scopePoints.values()].filter(p=>p.origin.module==="main"&&p.phase==="expression"
    &&p.origin.start===source.lastIndexOf("tt;"));
  assert.equal(points.length,1);
  assert.ok(points[0].available,points[0].reason);
  assert.equal(points[0].state.evidence.nodes.length>0,true);
  const session=new ContextualSession(program,points[0].id);
  for(const [entry,kind] of [["let evidence_ : IsSet(U0, S.M) { hlevel; }","defined"],
    ["let saved := evidence_","defined"],["typed(Unit, evidence_)","error"],["typeof saved","type"]]) {
    const [response]=await session.run(entry);
    assert.equal(response.kind,kind,JSON.stringify(response));
  }
  assert.equal(program.modules.get("main").has("evidence_"),false);
});

test("CB3: failed recursive wildcard coherence preserves the primary mismatch and body site",async t=>{
  const source=`import hlevels;
inductive L : set U0 { nil; cons(x : L); step(x : L) : cons(x) = x; }
def bad(x : L) : L := match x { nil => nil; _ => cons(nil); };`;
  const {program,result,get}=await check(t,source);
  assert.equal(result.gaps.length,1);
  const error=result.gaps[0];
  assert.equal(error.code,"E606");
  assert.equal(source.slice(error.start,error.end),"cons(nil)");
  assert.match(error.reason,/found L -> L -> cons\(nil\) = cons\(nil\), expected L -> \(forall (\w+) : L\. cons\(nil\) = \1\)/);
  assert.ok(get("bad").searchFuel.searches>0);
  assert.ok(get("bad").searchFuel.queries>=get("bad").searchFuel.most.queries);
  assert.ok(!program.steps("main").some(step=>step.declaration==="bad"&&step.kind==="obligation"));
  const limited=await check(t,source,{}, {searchFuel:{queries:1}});
  assert.equal(limited.get("bad").failure,"fuel");
  assert.match(limited.get("bad").reason,/ran out of search fuel/);
});

test("CB3: successful recursive wildcard coherence publishes its checked inspection witness",async t=>{
  const {program,result,get}=await check(t,`import hlevels;
inductive H : set U0 { first; second; p(y : H) : y = y; }
def collapse(x : H) : Unit := match x { first => tt; _ => tt; };
def computes : collapse(second) = tt { rfl; }`);
  accepts(result,get,["collapse","computes"]);
  const witness=result.links.find(link=>link.role==="coherence obligation"&&link.name==="p");
  assert.ok(witness);
  assert.equal(witness.description,"Checked clause for p from h-level evidence.");
  assert.ok(program.steps("main").some(step=>step.declaration==="collapse"&&step.kind==="obligation"));
  assert.ok(get("collapse").searchFuel.searches>0);
});
