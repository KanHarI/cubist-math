import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {bindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
import {parse,reservedReferences} from "../web/cubist/parser.mjs";
import {bindingResolution,sourceOrigin} from "../web/cubist/bindings.mjs";
import {resolveBindingSyntax,bindingUses} from "../web/cubist/binding-syntax.mjs";
import {retainTheorySource} from "../web/cubist/retained-theories.mjs";
import {retainedTheoryArtifacts,retainedMorphismArtifacts} from "../web/cubist/retained-theory-artifacts.mjs";
import {retainedInitialDeclarations} from "../web/translator/retained-initial-models.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const wasm=await create();
const failures=result=>result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]);
const queue=built=>built.artifacts.map(({binding,syntax,...annotations})=>bindingDeclaration(binding,syntax,annotations));
async function setup(t,theory) {
  const program=new CubicalProgram(wasm,sourceReader());t.after(()=>program.dispose());
  assert.deepEqual((await program.check("import hlevels; inductive Two : set U0 { left_; right_; }","base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,env=program.modules.get("base"),values=new Map();
  for(const [label,value] of env)if(/^[A-Za-z_][A-Za-z0-9_]*$/.test(label)) {
    const binding=registry.ofValue(value);if(binding)values.set(binding.id,value);
  }
  const inputs=bindingInputs(table,values,{reserved:reservedReferences("U0 UU0 Unit tt refl")});
  const source={revision:"retained-initial",module:"source"};
  const retained=retainTheorySource(parse(theory).declarations[0],{table,source,owner:["T"],context:inputs.context,
    constructors:inputs.constructors});
  const built=retainedTheoryArtifacts(retained,{table,owner:["T","base"]});
  const morphisms=retainedMorphismArtifacts(built.record,{table,owner:["T","morphisms"],bindings:built.bindings});
  const record=morphisms.record;
  built.artifacts.push(...morphisms.artifacts);built.artifacts[0].theory=record;
  const check=(declarations,text="",imports=env)=>{
    const checker=Object.create(program.checker);checker.bindingName=label=>`pilot__${label}`;
    checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
    const translator=new Translator({checker,normalize:false,moduleName:"pilot",compilationBindings:registry});
    const result=translator.translateSyntax({declarations:[...declarations,...parse(text).declarations]},text,imports);
    const scope=new Scope(translator.unit(),new Map(),result.env);
    return {result,translator,equal:(actual,expected)=>scope.equal(translator.term(parse(actual,true),scope),translator.term(parse(expected,true),scope))};
  };
  const checked=check(queue(built));assert.deepEqual(failures(checked.result),[]);
  let serial=0;
  const prepare=(text,{free=false}={})=>{
    const d=parse(text).declarations[0],owner=["initial",String(serial++)];
    const binding=table.allocate([...owner,"declaration"],{role:"declaration",label:d.name.text,
      origin:sourceOrigin({...source,start:d.name.start,end:d.name.end})});
    const header=resolveBindingSyntax({...d,value:d.value??d.body?.[0]?.value,body:undefined},
      {table,source,owner:[...owner,"header"],context:inputs.context.bind(record.name,bindingResolution(record.modelId)),
        constructors:inputs.constructors});
    const original=JSON.stringify(record),result=retainedInitialDeclarations(checked.translator,checked.translator.unit({source:text}),
      {record,binding,header,free},checked.result.env,{owner});
    assert.equal(JSON.stringify(record),original);
    assert.equal(result.plan.status,"conditional",JSON.stringify(result.plan));
    assert.doesNotThrow(()=>snapshotSyntax(queue(result)));
    for(const artifact of result.artifacts) {
      assert.ok(!bindingUses(artifact.syntax).some(use=>record.fields.some(f=>f.id===use.id)),"every field is explicitly instantiated");
    }
    return result;
  };
  return {program,record,prepare,check,env:checked.result.env};
}

test("retained initial and free artifacts compute folds through exact theory and constructor identities",async t=>{
  const {prepare,check,env}=await setup(t,`theory T(U < UU0, A : U0) {
    M : set U; point(a : A) : M; step(x : M) : M; law neutral(x : M) : step(x) = x;
  }`);
  const initial=prepare("def N : T(U0, Two) := tt;");
  const free=prepare("def W(A : U0) : T(U0, Two) := A;",{free:true});
  const {result,equal}=check([...parse("def Two : U0 := Unit;").declarations,...queue(initial),...queue(free)],`
    def target : T(U0, base.Two) := T.make(A := base.Two, M := base.Two, point := fun (a : base.Two) => a,
      step := fun (x : base.Two) => x, neutral := fun (x : base.Two) => refl(x));
    def ni : base.Two := N.fold(target).map(N.step(N.point(left_)));
    def wf : base.Two := W.fold(Unit, target, fun (a : Unit) => right_).map(W.step(W.gen(tt)));
    def wp : base.Two := W.fold(Unit, target, fun (a : Unit) => right_).map(W.point(left_));
    def wrong : ni = right_ := refl(right_);
  `,new Map([...env,["base.Two",env.get("Two")]]));
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  assert.equal(equal("ni","left_"),true);assert.equal(equal("ni","right_"),false);
  assert.equal(equal("wf","right_"),true);assert.equal(equal("wf","left_"),false);
  assert.equal(equal("wp","left_"),true);assert.equal(equal("wp","right_"),false);
});

test("retained constructor domains preserve dependent grouped arguments and caller header bindings",async t=>{
  const {prepare,check,env}=await setup(t,`theory T(U < UU0, A : U0) {
    M : set U; point(Two, x : Two, p : Two = x, a : A) : M;
  }`);
  const free=prepare("def W(Two : U0) : T(U0, Two) := Two;",{free:true});
  const {result,equal}=check(queue(free),`
    def target : T(U0, Unit) := T.make(A := Unit, M := Two,
      point := fun (Two, x : Two) => fun (p : Two = x) => fun (a : Unit) => x);
    def value : Two := W.fold(Unit, target, fun (a : Unit) => right_).map(W.point(left_, left_, refl(left_), tt));
    def generator : Two := W.fold(Unit, target, fun (a : Unit) => right_).map(W.gen(tt));
    def wrong : W(Unit) := W.point(tt, tt, refl(tt), tt);
  `,env);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  assert.equal(equal("value","left_"),true);assert.equal(equal("value","right_"),false);
  assert.equal(equal("generator","right_"),true);
});

test("retained initial arguments solve named universe holes once under the caller telescope",async t=>{
  const {prepare,check,env}=await setup(t,`theory T(U < UU0, A : U) {
    M : set U; point(a : A) : M;
  }`);
  const initial=prepare("def N : T(A := Two, U := _) := tt;");
  const free=prepare("def W(V < UU0, A : V) : T(_, A) := A;",{free:true});
  const {result,equal}=check([...queue(initial),...queue(free)],`
    def target : T(U0, Two) := T.make(A := Two, M := Two, point := fun (a : Two) => a);
    def ni : Two := N.fold(target).map(N.point(left_));
    def wf : Two := W.fold(U0, Two, target, fun (a : Two) => a).map(W.gen(right_));
  `,env);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("ni","left_"),true);assert.equal(equal("ni","right_"),false);
  assert.equal(equal("wf","right_"),true);assert.equal(equal("wf","left_"),false);
  assert.throws(()=>prepare("def Bad : T(U0, tt) := tt;"),/Type mismatch/);
});

test("anonymous law, operation and request positions survive initial and free folds",async t=>{
  const {prepare,check,env}=await setup(t,`theory T(U < UU0) {
    M : set U; point(_ : Two) : M; step(x : M) : M;
    law fixed(_ : Two, x : M) : step(x) = x;
  }`);
  const initial=prepare("def N : T(U0) := tt;");
  const free=prepare("def W(_, _ : Two, A : U0) : T(U0) := A;",{free:true});
  const {result,equal}=check([...queue(initial),...queue(free)],`
    def target : T(U0) := T.make(M := Two, point := fun (x : Two) => x,
      step := fun (x : Two) => x, fixed := fun (_ : Two, x : Two) => refl(x));
    def ni : Two := N.fold(target).map(N.step(N.point(right_)));
    def wf : Two := W.fold(left_, right_, Unit, target, fun (a : Unit) => left_).map(W.point(right_));
    def wg : Two := W.fold(left_, right_, Unit, target, fun (a : Unit) => left_).map(W.gen(tt));
  `,env);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  for(const name of ["ni","wf"]) {
    assert.equal(equal(name,"right_"),true);assert.equal(equal(name,"left_"),false);
  }
  assert.equal(equal("wg","left_"),true);assert.equal(equal("wg","right_"),false);
});

test("anonymous theory header arguments are forwarded positionally through Hom and initial models",async t=>{
  const {prepare,check,env}=await setup(t,`theory T(U < UU0, _, _ : Two) {
    M : set U; point(_ : Two) : M;
  }`);
  const initial=prepare("def N : T(U0, left_, right_) := tt;");
  const {result,equal}=check(queue(initial),`
    def target : T(U0, left_, right_) := T.make(left_, right_, M := Two, point := fun (x : Two) => x);
    def ni : Two := N.fold(target).map(N.point(right_));
    def identity_ : Two := T.Hom.id(target).map(right_);
  `,env);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  for(const name of ["ni","identity_"]) {
    assert.equal(equal(name,"right_"),true);assert.equal(equal(name,"left_"),false);
  }
});
