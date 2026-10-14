import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {bindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {RetainedInterfaces} from "../web/cubist/retained-interfaces.mjs";
import {retainedTheoryArtifacts,retainedMorphismArtifacts} from "../web/cubist/retained-theory-artifacts.mjs";
import {bindingUses} from "../web/cubist/binding-syntax.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";

const module=await create();
async function setup(t,header="def T(U < UU0) : Unit := tt;") {
  const program=new CubicalProgram(module,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check(`inductive Two { left_; right_; } inductive Nat { zero; succ(n : Nat); }
    def Index : U0 := Two; def IsSet(U < UU0, A : U) : U := forall x, y : A. forall p, q : x = y. p = q;`,"base")).gaps,[]);
  const registry=program.compilationBindings,table=registry.table,env=program.modules.get("base"),values=new Map();
  for(const [label,value] of env)if(/^[A-Za-z_][A-Za-z0-9_]*$/.test(label)) {
    const binding=registry.ofValue(value);if(binding)values.set(binding.id,value);
  }
  const inputs=bindingInputs(table,values,{reserved:["U0","UU0","Unit","tt","refl"]});
  const source={revision:"source",module:"source"};
  const retained=new RetainedInterfaces({table,source,owner:["T"],context:inputs.context,constructors:inputs.constructors});
  const d=parse(header).declarations[0];retained.parameters(d.name,d.params);
  const add=(source,kind="operation",options={})=>retained.retain(parse(source).declarations[0],{kind,...options});
  const metadata=new Map();
  const build=({morphisms=false}={})=>{
    const record={name:"T",bindingSyntax:retained.header,fields:retained.entries.filter(e=>e.kind!=="derived").map(e=>({...e,...metadata.get(e.id)})),
      derived:retained.entries.filter(e=>e.kind==="derived"),parents:[]};
    const built=retainedTheoryArtifacts(record,{table,owner:["T","generated"]});
    if(morphisms) {
      const generated=retainedMorphismArtifacts(built.record,{table,owner:["T","morphisms"],bindings:built.bindings});
      built.plan=generated.plan;built.artifacts.push(...generated.artifacts);
    }
    return {...built,declarations:built.artifacts.map(({binding,syntax,generated,theory})=>bindingDeclaration(binding,syntax,{generated,...(theory?{theory}:{})}))};
  };
  const check=(built,source="",before="")=>{
    const checker=Object.create(program.checker);
    checker.bindingName=label=>`pilot__${label}`;
    checker.define=(label,...args)=>program.checker.define(checker.bindingName(label),...args);
    const translator=new Translator({checker,normalize:false,moduleName:"pilot",compilationBindings:registry});
    const result=translator.translateSyntax({declarations:[...parse(before).declarations,...built.declarations,...parse(source).declarations]},source,env);
    const scope=new Scope(translator.unit(),new Map(),result.env);
    const equal=(label,expected)=>scope.equal(result.env.get(label),translator.term(parse(expected,true),scope));
    return {result,equal};
  };
  return {program,table,retained,add,build,check,metadata,inputs,source};
}
const failures=result=>result.declarations.filter(d=>d.status!=="checked-native-cubical").map(d=>[d.name,d.reason]);

test("retained base artifacts and derived telescopes preserve source IDs through the real declaration queue",async t=>{
  const {retained,add,build,check}=await setup(t);
  add("def M : U := Unit;","sort");
  const point=add("def c : M := tt;");
  add("def get(x : Two) : M := c;","derived");
  add("def op(c, x : Two, p : c = x) : M := tt;");
  add("def same(c : Two) : get(c) = get(c) := tt;","law");
  const original=JSON.stringify(retained.entries),built=build();
  assert.doesNotThrow(()=>snapshotSyntax(built.declarations));
  for(const artifact of built.artifacts)assert.ok(!bindingUses(artifact.syntax).some(use=>use.id===point.id));
  assert.equal(JSON.stringify(retained.entries),original,"generation leaves canonical source interfaces intact");
  const {result,equal}=check(built,`
    def instance_ : T(U0) := T.make(M := Two, c := left_, op := fun (c, x : Two) => fun (p : c = x) => c,
      same := fun (c : Two) => refl(left_));
    def value : Two := T.get(instance_, x := right_);
    def member_value : Two := instance_.get(right_);
    def applied : Two := T.op(instance_, right_, right_, refl(right_));
    def good : value = left_ := refl(left_);
    def wrong : value = right_ := refl(right_);
  `,"def c : Two := right_;");
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  assert.equal(equal("value","left_"),true);assert.equal(equal("value","right_"),false);
  assert.equal(equal("member_value","left_"),true);assert.equal(equal("member_value","right_"),false);
  assert.equal(equal("applied","right_"),true);
  const locals=built.artifacts.map(({syntax})=>new Set(syntax.owned));
  for(let i=0;i<locals.length;i++)for(let j=0;j<i;j++)assert.ok(![...locals[i]].some(id=>locals[j].has(id)));
});

test("family domains expand retained helpers without destination names and keep their argument checks",async t=>{
  const {add,build,check}=await setup(t);
  add("def Index(x : Unit) : U0 := Two;","derived");
  add("def M(x : Index(tt)) : U := Unit;","sort");
  add("def c(x : Two) : M(x) := tt;");
  const {result,equal}=check(build(),`
    def instance_ : T(U0) := T.make(M := fun (x : Two) => Two, c := fun (x : Two) => x);
    def value : Two := T.c(instance_, left_);
  `,"def Index : U0 := Unit;");
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("value","left_"),true);assert.equal(equal("value","right_"),false);
});

test("helper normalization cannot erase an ill-typed unused argument or result annotation",async t=>{
  for(const invalid of ["Index(left_)","Bad(tt)"]) {
    const {add,build,check}=await setup(t);
    add("def Index(x : Unit) : U0 := Two;","derived");
    add("def Bad(x : Unit) : U0 := tt;","derived");
    add(`def M(x : ${invalid}) : U := Unit;`,"sort");
    const built=build(),last=retainedLast(built),views=built.views.get(last.id);
    assert.ok(views.obligations.some(o=>o.kind==="interface-check"&&o.entry===last.id));
    assert.notDeepEqual(views.checking.tree,views.analysis.tree);
    const {result}=check(built);
    assert.ok(failures(result).some(([name])=>name==="T"),invalid);
  }
});

const retainedLast=built=>built.record.fields.at(-1);

test("generated structural self calls keep the fixed model and explicit parameter interface",async t=>{
  const {add,build,check}=await setup(t);
  add("def M : U := Unit;","sort");add("def c : M := tt;");
  add("def count(n : Nat, x : M) : M := match n { zero => x; succ(k) => count(k, x); };","derived",{self:true});
  const {result,equal}=check(build(),`
    def instance_ : T(U0) := T.make(M := Two, c := left_);
    def value : Two := T.count(instance_, n := succ(zero), x := right_);
  `);
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("value","right_"),true);assert.equal(equal("value","left_"),false);
});

test("Hom and Iso templates splice retained helper types and dependent locals by identity",async t=>{
  const {add,build,check,metadata}=await setup(t);
  const carrier=add("def M : U := Unit;","sort");
  const evidence=add("def M_is_set : IsSet(U, M) := tt;","evidence");
  metadata.set(evidence.id,{of:carrier.id,evidence:"IsSet"});
  add("def c : M := tt;");
  add("def Equal(A : Two) : U0 := A = A;","derived");
  add("def op(A : Two, p : Equal(A)) : M := tt;");
  const built=build({morphisms:true});
  assert.equal(built.plan.support.status,"conditional",built.plan.missing);
  assert.equal(built.plan.isoSupport.status,"conditional",built.plan.missingIso);
  assert.doesNotThrow(()=>snapshotSyntax(built.declarations));
  const {result,equal}=check(built,`
    def instance_(h : IsSet(U0, Two)) : T(U0) := T.make(Two, h, left_, fun (A : Two) => fun (p : A = A) => left_);
    def image(h : IsSet(U0, Two)) : Two := (T.Hom.id(instance_(h))).map(right_);
    def composed(h : IsSet(U0, Two)) : Two := (T.Hom.compose(T.Hom.id(instance_(h)), T.Hom.id(instance_(h)))).map(right_);
    def roundtrip(h : IsSet(U0, Two)) : Two := (T.Iso.inverse(T.Iso.id(instance_(h)))).to.map(right_);
  `,"def Equal : U0 := Unit;");
  assert.deepEqual(failures(result),[]);
  for(const label of ["image","composed","roundtrip"]) {
    assert.equal(equal(label,"fun (h : IsSet(U0, Two)) => right_"),true,label);
    assert.equal(equal(label,"fun (h : IsSet(U0, Two)) => left_"),false,label);
  }
});

test("parent projection artifacts use the complete identity correspondence after public renaming",async t=>{
  const {add,build,check,table,retained,inputs,source}=await setup(t,"def T(U < UU0, n : Two) : Unit := tt;");
  const carrier=add("def M : U := Unit;","sort"),point=add("def c : M := tt;");
  add("def get(x : Two) : M := c;","derived");
  const parent=build(),child=new RetainedInterfaces({table,source,owner:["child"],context:inputs.context,constructors:inputs.constructors});
  const header=parse("def Child(V < UU0, n : Two) : Unit := tt;").declarations[0];child.parameters(header.name,header.params);
  const correspondence=new Map(retained.header.tree.params.map((parameter,k)=>[parameter.name.bindingId,child.header.tree.params[k].name.bindingId]));
  const renamed=new Map([[carrier.id,"N"],[point.id,"point"]]);
  for(const entry of retained.entries)child.inherit(entry,correspondence,{label:renamed.get(entry.id)??entry.label,site:retained.header.tree.name.origin});
  const built=retainedTheoryArtifacts({name:"Child",bindingSyntax:child.header,
    fields:child.entries.filter(e=>e.kind!=="derived"),derived:child.entries.filter(e=>e.kind==="derived"),parents:[{
      label:"parent",theory:"T",modelId:parent.record.modelId,makeId:parent.record.makeId,
      universeIds:parent.record.universeIds.map(id=>correspondence.get(id)),
      parameterIds:parent.record.params.map(parameter=>correspondence.get(parameter.id)),
      fieldIds:parent.record.fields.map(field=>correspondence.get(field.id)),
    }]},{table,owner:["child","artifacts"]});
  const declarations=built.artifacts.map(({binding,syntax,generated,theory})=>bindingDeclaration(binding,syntax,{generated,...(theory?{theory}:{})}));
  const {result,equal}=check({declarations:[...parent.declarations,...declarations]},`
    def instance_ : Child(U0, right_) := Child.make(n := right_, N := Two, point := left_);
    def inherited : Two := instance_.get(right_);
    def forgotten : Two := instance_.parent.get(right_);
  `);
  assert.deepEqual(failures(result),[]);
  for(const label of ["inherited","forgotten"]) {
    assert.equal(equal(label,"left_"),true);assert.equal(equal(label,"right_"),false);
  }
});

test("opening a retained model preserves usable fields beside an unavailable optional helper",async t=>{
  const {add,build,check}=await setup(t);
  add("def M : U := Unit;","sort");add("def c : M := tt;");
  add("def bad : Unit := Two;","derived");
  const {result,equal}=check(build(),`
    def instance_ : T(U0) := T.make(Two, left_);
    use instance_;
    def healthy : Two := c;
    def broken : Unit := bad;
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["T.bad","broken"]);
  assert.equal(result.env.get("broken").blockedBy,"pilot__T.bad");
  assert.equal(equal("healthy","left_"),true);assert.equal(equal("healthy","right_"),false);
});
