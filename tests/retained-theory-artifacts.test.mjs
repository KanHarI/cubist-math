import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {Scope} from "../web/translator/elaboration.mjs";
import {bindingInputs,bindingDeclaration} from "../web/translator/binding-module.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {RetainedInterfaces} from "../web/cubist/retained-interfaces.mjs";
import {retainedTheoryArtifacts,retainedMorphismArtifacts} from "../web/cubist/retained-theory-artifacts.mjs";
import {retainTheorySource} from "../web/cubist/retained-theories.mjs";
import {bindingUses} from "../web/cubist/binding-syntax.mjs";
import {snapshotSyntax} from "../web/translator/syntax-graph.mjs";
import {LexicalContext,bindingResolution} from "../web/cubist/bindings.mjs";

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
  const construct=(record,{morphisms=false}={})=>{
    const built=retainedTheoryArtifacts(record,{table,owner:["T","generated"]});
    if(morphisms) {
      const generated=retainedMorphismArtifacts(built.record,{table,owner:["T","morphisms"],bindings:built.bindings});
      built.plan=generated.plan;built.artifacts.push(...generated.artifacts);
      built.record=generated.record;built.artifacts[0].theory=built.record;
    }
    return {...built,declarations:built.artifacts.map(({binding,syntax,generated,theory})=>bindingDeclaration(binding,syntax,{generated,...(theory?{theory}:{})}))};
  };
  const build=options=>construct({name:"T",bindingSyntax:retained.header,
    fields:retained.entries.filter(e=>e.kind!=="derived").map(e=>({...e,...metadata.get(e.id)})),
    derived:retained.entries.filter(e=>e.kind==="derived"),parents:[]},options);
  const records=new Map();
  const retain=(text,{context=inputs.context}={})=>retainTheorySource(parse(text).declarations[0],{table,source,owner:["source","T"],
    context,constructors:inputs.constructors},{lookup:name=>records.get(name)});
  const buildSource=(text,options)=>{
    const built=construct(retain(text),options);records.set(built.record.name,built.record);return built;
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
  return {program,table,retained,add,build,check,metadata,inputs,source,retain,buildSource,construct};
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

test("the source entry retains header and helper meanings through generation and law classification",async t=>{
  const {buildSource,check}=await setup(t);
  const built=buildSource(`theory T(U < UU0, n : Two) {
    M : set U;
    c : M;
    op(p : n = n) : M;
    def get(x : Two) : M := c;
    def n : Two := right_;
    law same(c : Two) : get(c) = get(c);
  }`,{morphisms:true});
  const header=built.record.bindingSyntax.tree.params[1].name.bindingId;
  const op=built.record.fields.find(field=>field.name==="op"),helper=built.record.derived.find(field=>field.name==="n");
  assert.equal(op.type.domain.left.resolution.id,header);
  assert.notEqual(header,helper.id);
  assert.equal(built.plan.support.status,"conditional",built.plan.missing);
  const {result,equal}=check(built,`
    def instance_(h : IsSet(U0, Two)) : T(U0, left_) := T.make(n := left_, M := Two, M_is_set := h, c := left_,
      op := fun (p : left_ = left_) => left_, same := fun (c : Two) => refl(left_));
    def got(h : IsSet(U0, Two)) : Two := instance_(h).get(right_);
    def image(h : IsSet(U0, Two)) : Two := (T.Hom.id(instance_(h))).map(right_);
  `);
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("got","fun (h : IsSet(U0, Two)) => left_"),true);
  assert.equal(equal("got","fun (h : IsSet(U0, Two)) => right_"),false);
  assert.equal(equal("image","fun (h : IsSet(U0, Two)) => right_"),true);
});

test("the source entry connects leveled family arguments to their exact evidence binders",async t=>{
  const {buildSource,check}=await setup(t);
  const built=buildSource(`theory T(U < UU0) {
    F(A : set U) : set U;
    get(A : set U, x : F(A)) : F(A);
    def again(A : set U, x : F(A)) : F(A) := get(A, x);
  }`);
  const operation=built.record.fields.find(field=>field.name==="get"),parameters=operation.syntax.tree.params;
  const witness=parameters[1].name.bindingId;
  assert.equal(parameters[2].type.args[1].resolution.id,witness);
  assert.equal(operation.syntax.tree.type.args[1].resolution.id,witness);
  const {result,equal}=check(built,`
    def instance_ : T(U0) := T.make(
      F := fun (A : U0) => fun (h : IsSet(U0, A)) => A,
      F_is_set := fun (A : U0) => fun (h : IsSet(U0, A)) => h,
      get := fun (A : U0) => fun (h : IsSet(U0, A)) => fun (x : A) => x);
    def got(h : IsSet(U0, Two)) : Two := instance_.get(Two, h, right_);
    def repeated(h : IsSet(U0, Two)) : Two := instance_.again(Two, h, right_);
  `);
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("got","fun (h : IsSet(U0, Two)) => right_"),true);
  assert.equal(equal("got","fun (h : IsSet(U0, Two)) => left_"),false);
  assert.equal(equal("repeated","fun (h : IsSet(U0, Two)) => right_"),true);
});

test("the retained law predicate rejects data and recursive helper dependencies by identity",async t=>{
  const {retain}=await setup(t);
  assert.throws(()=>retain("theory T(U < UU0) { M : set U; law invalid : M; }"),/elements are data/);
  assert.throws(()=>retain("theory T(U < UU0) { M : U; c : M; law invalid : c = c; }"),/has no h-level/);
  for(const reference of ["recurse_","recurse_(zero)"])
    assert.throws(()=>retain(`theory T(U < UU0) { M : set U;
      def recurse_(n : Nat) : M := match n { zero => recurse_(zero); succ(k) => recurse_(k); };
      law invalid : ${reference} = ${reference}; }`),/recursive, and a field's type cannot unfold it/);
});

test("source diamonds share ancestor identities and preserve every parent projection",async t=>{
  const {buildSource,check}=await setup(t);
  const root=buildSource("theory Root(U < UU0) { M : set U; c : M; def get(x : Two) : M := c; }",{morphisms:true});
  const left=buildSource("theory Left(U < UU0) extends base_ : Root { }",{morphisms:true});
  const right=buildSource("theory Right(U < UU0) extends base_ : Root { }",{morphisms:true});
  const child=buildSource("theory Child(V < UU0) extends l : Left, r : Right { def chosen : M := l.c; }",{morphisms:true});
  assert.deepEqual(child.record.fields.map(field=>field.name),["M","M_is_set","c"]);
  assert.equal(child.record.derived.filter(entry=>entry.name==="get").length,1);
  assert.equal(child.record.fields[2].binding.original,root.record.fields[2].id);
  const {result,equal}=check({declarations:[...root.declarations,...left.declarations,...right.declarations,...child.declarations]},`
    def instance_(h : IsSet(U0, Two)) : Child(U0) := Child.make(Two, h, left_);
    def direct(h : IsSet(U0, Two)) : Two := instance_(h).chosen;
    def through_left(h : IsSet(U0, Two)) : Two := instance_(h).l.base_.get(right_);
    def through_right(h : IsSet(U0, Two)) : Two := instance_(h).r.base_.get(right_);
    def hom_parent(h : IsSet(U0, Two)) : Two := (Child.Hom.id(instance_(h))).l.base_.map(right_);
  `);
  assert.deepEqual(failures(result),[]);
  for(const label of ["direct","through_left","through_right"]) {
    assert.equal(equal(label,"fun (h : IsSet(U0, Two)) => left_"),true,label);
    assert.equal(equal(label,"fun (h : IsSet(U0, Two)) => right_"),false,label);
  }
  assert.equal(equal("hom_parent","fun (h : IsSet(U0, Two)) => right_"),true);
  assert.equal(equal("hom_parent","fun (h : IsSet(U0, Two)) => left_"),false);
});

test("independent parent families share alpha-equivalent telescopes and retain distinct operations",async t=>{
  const {buildSource,retain,check}=await setup(t);
  const p=buildSource("theory P(U < UU0) { F(x : Unit) : set U; point(x : Unit) : F(x); }");
  const q=buildSource("theory Q(U < UU0) { F(y : Unit) : set U; point(y : Unit) : F(y); }");
  const c=buildSource("theory C(U < UU0) extends p : P, q : Q { def get(x : Unit) : F(x) := p.point(x); }");
  assert.deepEqual(c.record.fields.map(field=>field.name),["F","F_is_set","p_point","q_point"]);
  assert.throws(()=>retain("theory Ambiguous(U < UU0) extends p : P, q : Q { def get(x : Unit) : F(x) := point(x); }"),/point is ambiguous/);
  const {result,equal}=check({declarations:[...p.declarations,...q.declarations,...c.declarations]},`
    def instance_(h : IsSet(U0, Two)) : C(U0) := C.make(fun (x : Unit) => Two,
      fun (x : Unit) => h, fun (x : Unit) => left_, fun (x : Unit) => right_);
    def left_value(h : IsSet(U0, Two)) : Two := instance_(h).get(tt);
    def right_value(h : IsSet(U0, Two)) : Two := instance_(h).q.point(tt);
  `);
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("left_value","fun (h : IsSet(U0, Two)) => left_"),true);
  assert.equal(equal("left_value","fun (h : IsSet(U0, Two)) => right_"),false);
  assert.equal(equal("right_value","fun (h : IsSet(U0, Two)) => right_"),true);
  buildSource("theory Different(U < UU0) { F(y : Two) : set U; }");
  assert.throws(()=>retain("theory Conflict(U < UU0) extends p : P, d : Different { }"),/different kinds or indices/);
});

test("carrier evidence retains its source predicate even when a field shadows its public name",async t=>{
  const {buildSource,check}=await setup(t);
  const built=buildSource("theory T(U < UU0) { IsSet : Unit; M : set U; c : M; }");
  const shadow=built.record.fields[0],evidence=built.record.fields.find(field=>field.kind==="evidence");
  assert.notEqual(evidence.syntax.tree.type.fn.resolution.id,shadow.id);
  const {result,equal}=check(built,`
    def instance_(h : IsSet(U0, Two)) : T(U0) := T.make(tt, Two, h, left_);
    def got(h : IsSet(U0, Two)) : Two := instance_(h).c;
  `);
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("got","fun (h : IsSet(U0, Two)) => left_"),true);
  assert.equal(equal("got","fun (h : IsSet(U0, Two)) => right_"),false);
});

test("independent parent field orders merge according to dependencies",async t=>{
  const {buildSource,check}=await setup(t);
  const p=buildSource("theory P(U < UU0) { M : set U; N : set U; m : M; }");
  const q=buildSource("theory Q(U < UU0) { N : set U; M : set U; n : N; }");
  const child=buildSource("theory C(U < UU0) extends p : P, q : Q { }");
  const {result,equal}=check({declarations:[...p.declarations,...q.declarations,...child.declarations]},`
    def instance_(h : IsSet(U0, Two)) : C(U0) := C.make(M := Two, M_is_set := h, N := Two, N_is_set := h, m := left_, n := right_);
    def first_(h : IsSet(U0, Two)) : Two := instance_(h).p.m;
    def second_(h : IsSet(U0, Two)) : Two := instance_(h).q.n;
  `);
  assert.deepEqual(failures(result),[]);
  assert.equal(equal("first_","fun (h : IsSet(U0, Two)) => left_"),true);
  assert.equal(equal("second_","fun (h : IsSet(U0, Two)) => right_"),true);
});

test("grouped evidence uses the corpus Monad's interleaved public interface through Hom and Iso",async t=>{
  const {buildSource,check}=await setup(t);
  const source=await readFile(new URL("../cubist-tests/theory_families.cubist",import.meta.url),"utf8");
  const declarations=parse(source).declarations;
  const part=name=>{const d=declarations.find(d=>d.name?.text===name);return source.slice(d.start,d.end);};
  const built=buildSource(part("Monad"),{morphisms:true});
  const {result,equal}=check(built,`${part("identity")}
    def value(h : IsSet(U0, Two)) : Two := identity.bind(Two, h, Two, h, left_, fun (x : Two) => x);
    def twice(h : IsSet(U0, Two)) : Two := Monad.Hom.compose(Monad.Hom.id(identity), Monad.Hom.id(identity)).map(Two, h, left_);
    def iso : Monad.Iso(identity, identity) := Monad.Iso.compose(Monad.Iso.id(identity), Monad.Iso.id(identity));
    def wrong(h : IsSet(U0, Two)) : value(h) = right_ := refl(right_);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  for(const name of ["value","twice"]) {
    assert.equal(equal(name,"fun (h : IsSet(U0, Two)) => left_"),true);
    assert.equal(equal(name,"fun (h : IsSet(U0, Two)) => right_"),false);
  }
});

test("fixed universe positions survive family parameters, helpers and absent generated source lexemes",async t=>{
  const {buildSource,retain,construct,inputs,check}=await setup(t);
  const family=buildSource("theory TG(U < UU0) { F(U : U0) : U; }");
  const helpers=buildSource("theory TH(U < UU0) { def U : U0 := Two; M : set U; c : M; }");
  const context=new LexicalContext(inputs.context.snapshot().filter(([label])=>label!=="UU0"));
  const headerless=construct(retain("theory Bare { k : Two; }",{context}));
  const {result,equal}=check({declarations:[...family.declarations,...helpers.declarations,...headerless.declarations]},`
    def family_instance : TG(U0) := TG.make(fun (A : U0) => A);
    def wrong_element : TG(U0) := TG.make(fun (A : U0) => tt);
    def helper_instance(h : IsSet(U0, Two)) : TH(U0) := TH.make(M := Two, M_is_set := h, c := left_);
    def bare : Bare(U0) := Bare.make(left_);
    def value : Two := Bare.k(bare);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong_element"],JSON.stringify(failures(result)));
  assert.equal(equal("value","left_"),true);assert.equal(equal("value","right_"),false);
});

test("resolved parent namespaces close unknown members before unrelated module lookup",async t=>{
  const {buildSource,retain,inputs}=await setup(t);
  buildSource("theory P(U < UU0) { M : U; }");
  const global=buildSource("theory p(U < UU0) { x : Two; }");
  const context=inputs.context.bind("p",bindingResolution(global.record.modelId))
    .bind("p.x",bindingResolution(global.record.fields[0].projectionId));
  assert.throws(()=>retain("theory C(U < UU0) extends p : P { op(q : p(U), e : p.x(q) = left_) : M; }",{context}),
    /P, C's parent p, has no field x/);
  const local=retain("theory Local(U < UU0, p : U0) extends p : P { op(q : p) : M; }",{context});
  assert.equal(local.fields.find(f=>f.name==="op").syntax.tree.params[0].type.resolution.id,
    local.bindingSyntax.tree.params.find(p=>p.name.text==="p").name.bindingId);
});

test("parent Hom support is a planning dependency and leaves the child's base usable",async t=>{
  const {buildSource,retain,construct,check}=await setup(t);
  const parent=buildSource("theory P(U < UU0) { k : Two; }",{morphisms:true});
  const child=buildSource("theory C(U < UU0) extends p : P { M : set U; c : M; }",{morphisms:true});
  assert.equal(child.record.homSupport.status,"unsupported");
  assert.equal(child.record.homSupport.cause,parent.record.homSupport);
  const {result,equal}=check({declarations:[...parent.declarations,...child.declarations]},`
    def instance_(h : IsSet(U0, Two)) : C(U0) := C.make(k := left_, M := Two, M_is_set := h, c := right_);
    def value(h : IsSet(U0, Two)) : Two := C.k(instance_(h));
    def unavailable(a : C(U0)) : U0 := C.Hom(a, a);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["unavailable"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/parent P has no homomorphisms/);
  assert.equal(equal("value","fun (h : IsSet(U0, Two)) => left_"),true);
  const source=retain("theory Pending(U < UU0) extends p : P { M : set U; c : M; }");
  const pending=construct({...source,parents:source.parents.map(p=>({...p,homSupport:{status:"pending",obligations:[{kind:"interface-check"}]}}))},
    {morphisms:true});
  assert.equal(pending.record.homSupport.status,"pending");
  assert.ok(pending.artifacts.every(a=>!a.binding.label.includes(".Hom")));
});

test("anonymous helper arguments normalize for support while their complete checking obligations remain",async t=>{
  const {buildSource,check}=await setup(t);
  const good=buildSource("theory T(U < UU0) { M : set U; def K(_ : Two) : U := M; op(x : K(left_)) : M; }",{morphisms:true});
  assert.equal(good.record.homSupport.status,"conditional");
  const {result,equal}=check(good,`
    def instance_(h : IsSet(U0, Two)) : T(U0) := T.make(M := Two, M_is_set := h, op := fun (x : Two) => x);
    def value(h : IsSet(U0, Two)) : Two := T.Hom.id(instance_(h)).map(left_);
  `);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("value","fun (h : IsSet(U0, Two)) => left_"),true);
  assert.equal(equal("value","fun (h : IsSet(U0, Two)) => right_"),false);
  const bad=buildSource("theory Bad(U < UU0) { M : set U; def K(_ : Two) : U := M; op(x : K(tt)) : M; }",{morphisms:true});
  assert.ok(failures(check(bad).result).some(([name,reason])=>name==="Bad"&&/Type mismatch/.test(reason)));
});
