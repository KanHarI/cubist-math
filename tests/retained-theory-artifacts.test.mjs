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
async function setup(t,header="def T(U < UU0) : Unit := tt;",base="") {
  const program=new CubicalProgram(module,async()=>"");t.after(()=>program.dispose());
  assert.deepEqual((await program.check(`inductive Two { left_; right_; } inductive Nat { zero; succ(n : Nat); }
    def Index : U0 := Two; def IsSet(U < UU0, A : U) : U := forall x, y : A. forall p, q : x = y. p = q;
    ${base}`,"base")).gaps,[]);
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

test("theory retention preserves grouped and separate universe domains through Hom and Iso",async t=>{
  for(const [header,groups] of [["U, V < UU0",[0,0]],["U < UU0, V < UU0",[0,1]]]) {
    const {retain,construct,check}=await setup(t);
    const record=retain(`theory T(${header}) { M : set U; N : set V; op(x : M) : N; }`);
    const params=record.bindingSyntax.tree.params;
    assert.deepEqual(params.map(p=>p.group),groups);
    if(groups[0]===groups[1])assert.equal(params[0].bound,params[1].bound);
    else assert.notEqual(params[0].bound,params[1].bound);
    const built=construct(record,{morphisms:true});
    const {result,equal}=check(built,`
      def instance_(h : IsSet(U0, Two)) : T(U0, U0) := T.make(Two, h, Two, h, fun (x : Two) => x);
      def value(h : IsSet(U0, Two)) : Two := T.Hom.id(instance_(h)).map_N(right_);
      def inverse_(h : IsSet(U0, Two)) : Two := T.Iso.inverse(T.Iso.id(instance_(h))).to.map_M(left_);
    `);
    assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
    assert.equal(equal("value","fun (h : IsSet(U0, Two)) => right_"),true);
    assert.equal(equal("value","fun (h : IsSet(U0, Two)) => left_"),false);
    assert.equal(equal("inverse_","fun (h : IsSet(U0, Two)) => left_"),true);
  }
});

test("anonymous operation and family positions remain usable through generated Hom applications",async t=>{
  const {buildSource,check}=await setup(t);
  const built=buildSource(`theory T(U < UU0) { M : set U; F(_ : Two) : set U;
    op(_, _ : Two) : M; point : F(left_); pick(_ : set U, x : M) : M; }`,{morphisms:true});
  assert.equal(built.record.homSupport.status,"conditional");
  const {result,equal}=check(built,`
    def instance_(h : IsSet(U0, Two)) : T(U0) := T.make(M := Two, M_is_set := h,
      F := fun (x : Two) => Two, F_is_set := fun (x : Two) => h,
      op := fun (x, y : Two) => x, point := right_,
      pick := fun (A : U0) => fun (e : IsSet(U0, A), x : Two) => x);
    def value(h : IsSet(U0, Two)) : Two := T.Hom.id(instance_(h)).map_M(T.op(instance_(h), right_, left_));
    def family(h : IsSet(U0, Two)) : Two := T.Hom.id(instance_(h)).map_F(left_, right_);
    def evidence_(h : IsSet(U0, Two)) : Two := T.pick(instance_(h), Two, h, right_);
  `);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  for(const name of ["value","family","evidence_"]) {
    assert.equal(equal(name,"fun (h : IsSet(U0, Two)) => right_"),true,name);
    assert.equal(equal(name,"fun (h : IsSet(U0, Two)) => left_"),false,name);
  }
});

test("anonymous parent header positions retain distinct child correspondences",async t=>{
  const {buildSource,check}=await setup(t);
  const parent=buildSource("theory P(U < UU0, _, _ : Two) { M : set U; c : M; }",{morphisms:true});
  const child=buildSource("theory C(U < UU0, _, _ : Two) extends p : P {}",{morphisms:true});
  assert.equal(new Set(child.record.parents[0].parameterIds).size,2);
  assert.deepEqual(child.record.parents[0].parameterIds,child.record.params.map(p=>p.id));
  const {result,equal}=check({declarations:[...parent.declarations,...child.declarations]},`
    def instance_(h : IsSet(U0, Two)) : C(U0, left_, right_) := C.make(left_, right_, Two, h, right_);
    def value(h : IsSet(U0, Two)) : Two := instance_(h).p.c;
    def mapped(h : IsSet(U0, Two)) : Two := C.Hom.id(instance_(h)).p.map(right_);
  `);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  for(const name of ["value","mapped"])assert.equal(equal(name,"fun (h : IsSet(U0, Two)) => right_"),true);
});

test("anonymous universe positions introduce no name in fixed universe syntax",async t=>{
  const {retain}=await setup(t);
  for(const source of [
    "theory T(_ < UU0) { M : set _; c : M; }",
    "theory T(_, _ < UU0) { M : set _; c : M; }",
    "theory T(_ < UU0) { P : prop _; }",
    "theory T(_ < UU0) { def f(A : set _) : Two := left_; }",
    "theory T(_, _ < UU0) { op(A : set _) : Two; }",
  ]) {
    const position=source.indexOf("_",source.includes("set _")?source.indexOf("set _"):source.indexOf("prop _"));
    assert.throws(()=>retain(source),error=>{
      assert.match(error.message,/anonymous universe has no name/,source);
      assert.equal(error.offset,position);assert.equal(error.sourceEnd,position+1);
      return true;
    },source);
  }
});

test("universe and term header correspondence preserve anonymous positions independently",async t=>{
  const {buildSource,retain,check}=await setup(t);
  const parent=buildSource("theory P(_, _, U < UU0, _, _ : Two) { M : set U; c : M; }");
  const child=buildSource("theory C(_, _, V, U < UU0, _, _ : Two) extends p : P {}");
  const header=child.record.bindingSyntax.tree.params;
  const universes=header.filter(p=>p.bound),parameters=header.filter(p=>!p.bound);
  assert.deepEqual(child.record.parents[0].universeIds,[0,1,3].map(i=>universes[i].name.bindingId));
  assert.deepEqual(child.record.parents[0].parameterIds,parameters.map(p=>p.name.bindingId));
  assert.equal(new Set(child.record.parents[0].universeIds).size,3);
  const one=buildSource("theory One(_ < UU0) { k : Two; }");
  const more=buildSource("theory More(_, _ < UU0) extends base_ : One {}");
  assert.deepEqual(more.record.parents[0].universeIds,[more.record.bindingSyntax.tree.params[0].name.bindingId]);
  assert.throws(()=>retain("theory Named(U < UU0) extends base_ : One {}"),/header binds the universe _/);
  assert.throws(()=>retain("theory Shifted(U, _, _ < UU0, _, _ : Two) extends p : P {}"),/header binds the universe _/);
  buildSource("theory NamedParent(U < UU0) { M : U; }");
  assert.throws(()=>retain("theory AnonymousChild(_ < UU0) extends base_ : NamedParent {}"),/header binds the universe U/);
  const {result,equal}=check({declarations:[...parent.declarations,...child.declarations,...one.declarations,...more.declarations]},`
    def instance_(h : IsSet(U0, Two)) : C(U0, U1, U1, U0, left_, right_) :=
      C.make(left_, right_, Two, h, right_);
    def parent_(h : IsSet(U0, Two)) : P(U0, U1, U0, left_, right_) := instance_(h).p;
    def value(h : IsSet(U0, Two)) : Two := parent_(h).c;
    def small : More(U0, U1) := More.make(left_);
    def first_ : One(U0) := small.base_;
  `);
  assert.deepEqual(failures(result),[],JSON.stringify(failures(result)));
  assert.equal(equal("value","fun (h : IsSet(U0, Two)) => right_"),true);
  assert.equal(equal("value","fun (h : IsSet(U0, Two)) => left_"),false);
});

const operandModels=`
  theory Numerals(U < UU0) {
    M : U; one : Nat; ghost : Nat; read(n : Nat) : M;
    def numeral_(n : Nat) : M := read(n) notation numeral;
  }
  def recipe : Numerals(U0) := Numerals.make(Nat, succ(zero), succ(zero), fun (n : Nat) => n);
  def shifted : Numerals(U0) := Numerals.make(Nat, succ(zero), succ(zero), fun (n : Nat) => succ(n));
  def original : Numerals(U0) := recipe;
`;

test("retained operand recipes keep declaration receivers and caller operand bindings",async t=>{
  const {buildSource,check}=await setup(t,undefined,operandModels);
  const built=buildSource(`theory Power(U < UU0) {
    M : U; pow(x : M, n : Nat) : M notation x ^ recipe.(n);
  }`);
  const snapshot=JSON.stringify(built.record);
  assert.doesNotThrow(()=>snapshotSyntax(built.declarations));
  const {result,equal}=check(built,`
    def chosen : Power(U0) := Power.make(Nat, fun (x, n : Nat) => n);
    def value(recipe : Numerals(U0)) : Nat := chosen.(zero ^ 0);
    def local_operand(one : Nat) : Nat := chosen.(zero ^ one);
    def intended : value(shifted) = zero := refl(zero);
    def wrong : value(shifted) = succ(zero) := refl(succ(zero));
    def unbound : Nat := chosen.(zero ^ ghost);
  `,"def recipe : Numerals(U0) := shifted;");
  assert.deepEqual(failures(result).map(([name])=>name),["wrong","unbound"],JSON.stringify(failures(result)));
  assert.equal(equal("value","fun (recipe : Numerals(U0)) => zero"),true);
  assert.equal(equal("local_operand","fun (one : Nat) => one"),true);
  assert.equal(JSON.stringify(built.record),snapshot,"opening instantiates recipes without changing their canonical source");
});

test("retained operand recipes instantiate the selected model's header and field identities",async t=>{
  for(const location of ["header","field"] )await t.test(location,async t=>{
    const {buildSource,check}=await setup(t,undefined,operandModels);
    const header=location==="header"?", recipe : Numerals(U0)":"";
    const field=location==="field"?"recipe : Numerals(U0);":"";
    const built=buildSource(`theory Power(U < UU0${header}) {
      ${field} M : U; pow(recipe : M, n : Nat) : M notation recipe ^ recipe.(n);
    }`);
    const model=arg=>location==="header"?`Power(U0, ${arg})`:"Power(U0)";
    const {result,equal}=check(built,`
      def plain : ${model("original")} := Power.make(original, Nat, fun (x, n : Nat) => n);
      def raised : ${model("shifted")} := Power.make(shifted, Nat, fun (x, n : Nat) => n);
      def plain_value(recipe : Numerals(U0)) : Nat := plain.(zero ^ 0);
      def raised_value(recipe : Numerals(U0)) : Nat := raised.(zero ^ 0);
      def intended : plain_value(shifted) = zero := refl(zero);
      def shifted_value : raised_value(original) = succ(zero) := refl(succ(zero));
      def wrong : raised_value(original) = zero := refl(zero);
    `);
    assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
    assert.equal(equal("plain_value","fun (recipe : Numerals(U0)) => zero"),true);
    assert.equal(equal("raised_value","fun (recipe : Numerals(U0)) => succ(zero)"),true);
  });
});

test("parent namespace selections distinguish header scope from field-local binders",async t=>{
  const {buildSource,check}=await setup(t);
  const built=[
    "theory P(U < UU0) { M : U; }",
    "theory Header(U < UU0, M : U0) extends p : P(M := N) { f(a : p.(M)) : N; }",
    "theory Universe(U, M < UU0) extends p : P(M := N) { f(a : p.(M)) : N; }",
    "theory Local(U < UU0, M : U0) extends p : P(M := N) { f(M : U0, a : p.(M)) : M; }",
  ].map(text=>buildSource(text));
  const {result}=check({declarations:built.flatMap(b=>b.declarations)},`
    def intended : Header(U0, Unit) := Header.make(Unit, Two, fun (a : Two) => a);
    def wrong_header : Header(U0, Unit) := Header.make(Unit, Two, fun (a : Unit) => left_);
    def universe_intended : Universe(U0, U0) := Universe.make(Two, fun (a : Two) => a);
    def wrong_universe : Universe(U0, U0) := Universe.make(Two, fun (a : U0) => left_);
    def local_intended : Local(U0, Unit) := Local.make(Unit, Two, fun (M : U0) => fun (a : M) => a);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong_header","wrong_universe"],JSON.stringify(failures(result)));
});

test("inherited ambiguity is an ordered resolution that explicit namespaces and locals can shadow",async t=>{
  const {buildSource,check}=await setup(t);
  const built=[
    "theory P(U < UU0) { M : U; x : M; }",
    "theory Q(U < UU0) { M : U; x : M; }",
    "theory C(U < UU0) extends p : P, q : Q { f(a : M, e : a = p.(x)) : M; def local(x : M) : M := x; }",
  ].map(text=>buildSource(text));
  assert.throws(()=>buildSource("theory Bad(U < UU0) extends p : P, q : Q { def bad : M := x; }"),/x is ambiguous in Bad/);
  const {result}=check({declarations:built.flatMap(b=>b.declarations)},`
    def intended : C(U0) := C.make(Two, left_, right_, fun (a : Two, e : a = left_) => a);
    def wrong : C(U0) := C.make(Two, left_, right_, fun (a : Two, e : a = right_) => a);
    def local_value : intended.local(right_) = right_ := refl(right_);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
});

test("deferred namespaces retain only the member candidates used by their bodies",async t=>{
  const {buildSource,check}=await setup(t,undefined,`
    theory Leaf(U < UU0) { w : Two; } def leaf : Leaf(U0) := Leaf.make(left_);
  `);
  const built=[
    "theory G(U < UU0) { x : Two; y : Two; }",
    "theory A(U < UU0) extends g : G { def pick(m : Leaf(U0)) : Two := m.(g.(x)); }",
    "theory B(U < UU0) extends a : A(y := z) {}",
    "theory C(U < UU0) extends a : A {}",
    "theory D(U < UU0) extends b : B, c : C {}",
  ].map(text=>buildSource(text));
  assert.equal(built.at(-1).record.derived.filter(d=>d.label==="pick").length,1);
  const source=built[1].record,unused=source.fields.find(f=>f.label==="y").id;
  assert.ok(bindingUses(source.derived[0].syntax,{conditional:true}).every(use=>use.id!==unused));
  const {result,equal}=check({declarations:built.flatMap(b=>b.declarations)},`
    def d : D(U0) := D.make(x := right_, z := left_, y := left_);
    def picked : Two := D.pick(d, leaf);
    def wrong : picked = left_ := refl(left_);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  assert.equal(equal("picked","right_"),true);
});

test("deferred namespace failures keep the same source diagnostic as immediate lookup",async t=>{
  const {buildSource,check}=await setup(t,undefined,"theory Leaf(U < UU0) { w : Two; }");
  const parent=buildSource("theory Parent(U < UU0) { x : Two; }");
  const immediate="theory Static(U < UU0) extends left_ : Parent { def bad : Two := left_.unknown; }";
  assert.throws(()=>buildSource(immediate),error=>{
    assert.equal(error.message,"Parent, Static's parent left_, has no field unknown.");
    assert.equal(error.offset,immediate.indexOf("left_.unknown"));
    return true;
  });
  const text=`theory C(U < UU0) extends left_ : Parent {
    def pick(b : Two) : Two := match b { left_ => left_.unknown; right_ => right_; };
    def opened(m : Leaf(U0)) : Two := m.(left_.unknown);
  }`;
  const child=buildSource(text),{result}=check({declarations:[...parent.declarations,...child.declarations]});
  const errors=result.declarations.filter(d=>d.status!=="checked-native-cubical");
  assert.deepEqual(errors.map(e=>e.name),["C.pick","C.opened"]);
  for(const [index,error] of errors.entries()) {
    assert.equal(error.reason,"Parent, C's parent left_, has no field unknown.");
    const offset=index===0?text.indexOf("left_.unknown"):text.lastIndexOf("left_.unknown");
    assert.equal(error.errorStart,offset);
    assert.equal(error.errorEnd,offset+"left_.unknown".length);
  }
});

test("inherited notation substitutes receiver fields through renaming and shared diamonds",async t=>{
  const {buildSource,check}=await setup(t,undefined,operandModels);
  const parent=buildSource(`theory Power(U < UU0) {
    recipe : Numerals(U0); M : U; pow(x : M, n : Nat) : M notation x ^ recipe.(n);
  }`),snapshot=JSON.stringify(parent.record);
  const built=[parent,...[
    "theory L(U < UU0) extends p : Power(recipe := reader, M := Carrier, pow := power) {}",
    "theory R(U < UU0) extends p : Power(recipe := reader, M := Carrier, pow := power) {}",
    "theory D(U < UU0) extends l : L, r : R {}",
  ].map(text=>buildSource(text))];
  const record=built.at(-1).record;
  assert.equal(record.notationBindings["^"].field,record.fields.find(field=>field.label==="power").id);
  assert.equal(record.notationBindings["^"].recipe.right.tree.resolution.id,record.fields.find(field=>field.label==="reader").id);
  assert.deepEqual(record.ambiguousNotations,{});
  assert.equal(JSON.stringify(parent.record),snapshot);
  assert.doesNotThrow(()=>snapshotSyntax(record));
  const {result}=check({declarations:built.flatMap(b=>b.declarations)},`
    def plain : D(U0) := D.make(reader := original, Carrier := Nat, power := fun (x, n : Nat) => n);
    def raised : D(U0) := D.make(reader := shifted, Carrier := Nat, power := fun (x, n : Nat) => n);
    def value : Nat := plain.(zero ^ 0);
    def intended : value = zero := refl(zero);
    def raised_intended : raised.(zero ^ 0) = succ(zero) := refl(succ(zero));
    def parent_intended : raised.l.p.(zero ^ 0) = succ(zero) := refl(succ(zero));
    def wrong : value = succ(zero) := refl(succ(zero));
  `,"def recipe : Numerals(U0) := shifted;");
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
});

test("one shared operation with different inherited operand receivers stays ambiguous",async t=>{
  const {buildSource,check}=await setup(t,undefined,operandModels);
  const built=[
    "theory Power(U < UU0) { recipe : Numerals(U0); M : U; pow(x : M, n : Nat) : M notation x ^ recipe.(n); }",
    "theory L(U < UU0) extends p : Power(recipe := a) {}",
    "theory R(U < UU0) extends p : Power(recipe := b) {}",
    "theory Both(U < UU0) extends l : L, r : R {}",
    "theory Further(U < UU0) extends both : Both {}",
  ].map(text=>buildSource(text));
  const record=built.at(-1).record;
  assert.equal(record.fields.filter(field=>field.label==="pow").length,1);
  assert.equal(record.notationBindings["^"],undefined);
  assert.equal(record.ambiguousNotationBindings["^"].length,2);
  assert.deepEqual(record.ambiguousNotations["^"].map(rule=>rule.label),["both.l","both.r"]);
  assert.throws(()=>buildSource(`theory Collision(U < UU0) extends base : Both {
    other(x : M, n : Nat) : M notation x ^ recipe.(n);
  }`),/parents bind it to/);
  const {result}=check({declarations:built.flatMap(b=>b.declarations)},`
    def chosen : Further(U0) := Further.make(a := original, b := shifted, M := Nat, pow := fun (x, n : Nat) => n);
    def ambiguous : Nat := chosen.(zero ^ 0);
    def left_value : Nat := chosen.both.l.(zero ^ 0);
    def right_value : Nat := chosen.both.r.(zero ^ 0);
    def left_intended : left_value = zero := refl(zero);
    def right_intended : right_value = succ(zero) := refl(succ(zero));
    def wrong : right_value = zero := refl(zero);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["ambiguous","wrong"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/\^ is ambiguous/);
});

test("operand receivers select parent namespaces instead of ambient same-named models",async t=>{
  const {buildSource,check}=await setup(t,undefined,operandModels+"def num : Numerals(U0) := shifted;");
  const parent=buildSource(`theory Num(U, V < UU0) {
    M : U; read(n : Nat) : M; def numeral_(n : Nat) : M := read(n) notation numeral;
  }`);
  const child=buildSource(`theory Power(U, V < UU0) extends num : Num {
    pow(num : M, n : Nat) : M notation num ^ num.(n);
  }`);
  const renamed=buildSource("theory Renamed(U, V < UU0) extends p : Power(M := Carrier, read := convert) {}");
  const snapshot=JSON.stringify(child.record.notationBindings);
  assert.ok(bindingUses(child.record.notationBindings["^"].recipe.right).some(use=>use.id===parent.record.makeId));
  const {result}=check({declarations:[...parent.declarations,...child.declarations,...renamed.declarations]},`
    def chosen : Renamed(U0, U1) := Renamed.make(Carrier := Nat, convert := fun (n : Nat) => n, pow := fun (x, n : Nat) => n);
    def value(num : Numerals(U0)) : Nat := chosen.(zero ^ 0);
    def intended : value(shifted) = zero := refl(zero);
    def wrong : value(shifted) = succ(zero) := refl(succ(zero));
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
  assert.equal(JSON.stringify(child.record.notationBindings),snapshot);
});

test("extends notation replacements capture the renamed child interface and leave parent recipes intact",async t=>{
  const {buildSource,check}=await setup(t,undefined,operandModels);
  const built=[
    "theory Power(U < UU0) { decoder : Numerals(U0); M : U; pow(x : M, n : Nat) : M notation x ^ recipe.(n); }",
    "theory Child(U < UU0) extends p : Power(decoder := recipe, pow := sum notation x + recipe.(n)) {}",
    "theory Further(U < UU0) extends c : Child(recipe := reader) {}",
  ].map(text=>buildSource(text));
  const record=built.at(-1).record;
  assert.equal(record.notationBindings["^"],undefined);
  assert.equal(record.notationBindings["+"].recipe.right.tree.resolution.id,record.fields.find(field=>field.label==="reader").id);
  const {result}=check({declarations:built.flatMap(b=>b.declarations)},`
    def chosen : Further(U0) := Further.make(reader := shifted, M := Nat, sum := fun (x, n : Nat) => n);
    def value(recipe : Numerals(U0)) : Nat := chosen.(zero + 0);
    def intended : value(original) = succ(zero) := refl(succ(zero));
    def parent_intended : chosen.c.p.(zero ^ 0) = zero := refl(zero);
    def removed : Nat := chosen.(zero ^ 0);
    def wrong : value(original) = zero := refl(zero);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["removed","wrong"],JSON.stringify(failures(result)));
});

test("renoting one ambiguous inherited field removes only that field's previous notation",async t=>{
  const {buildSource,check}=await setup(t,undefined,operandModels);
  const built=[
    "theory Power(U < UU0) { M : U; pow(x : M, n : Nat) : M notation x ^ recipe.(n); }",
    "theory Both(U < UU0) extends l : Power(pow := left_power notation x + recipe.(n)), r : Power(pow := right_power notation x + recipe.(n)) {}",
    "theory Fixed(U < UU0) extends b : Both(left_power := product notation x * recipe.(n)) {}",
  ].map(text=>buildSource(text));
  assert.equal(built[1].record.ambiguousNotationBindings["+"].length,2);
  const fixed=built[2].record;
  assert.deepEqual(fixed.ambiguousNotations,{});
  assert.equal(fixed.notationBindings["+"].field,fixed.fields.find(field=>field.label==="right_power").id);
  assert.equal(fixed.notationBindings["*"].field,fixed.fields.find(field=>field.label==="product").id);
  const {result}=check({declarations:built.flatMap(b=>b.declarations)},`
    def both : Both(U0) := Both.make(M := Nat, left_power := fun (x, n : Nat) => n, right_power := fun (x, n : Nat) => succ(n));
    def ambiguous : Nat := both.(zero + 0);
    def left_call : both.l.pow(zero, zero) = zero := refl(zero);
    def right_call : both.r.pow(zero, zero) = succ(zero) := refl(succ(zero));
    def fixed : Fixed(U0) := Fixed.make(M := Nat, product := fun (x, n : Nat) => n, right_power := fun (x, n : Nat) => succ(n));
    def left_intended : fixed.(zero * 0) = zero := refl(zero);
    def right_intended : fixed.(zero + 0) = succ(zero) := refl(succ(zero));
    def wrong : fixed.(zero + 0) = zero := refl(zero);
  `);
  assert.deepEqual(failures(result).map(([name])=>name),["ambiguous","wrong"],JSON.stringify(failures(result)));
  assert.match(failures(result)[0][1],/Write both\.l\.pow\(x, y\) or both\.r\.pow\(x, y\)/);
});

test("notation carrier classification uses retained helper analysis while preserving argument checks",async t=>{
  for(const argument of ["tt","left_"])await t.test(argument,async t=>{
    const {buildSource,check}=await setup(t);
    const built=buildSource(`theory Alias(U < UU0) {
      M : U; def Carrier(a : Unit) : U := M;
      add(x, y : Carrier(${argument})) : Carrier(${argument}) notation x + y;
    }`);
    const {result}=check(built,argument==="tt"?`
      def chosen : Alias(U0) := Alias.make(Two, fun (x, y : Two) => x);
      def value : Two := chosen.(left_ + right_);
      def intended : value = left_ := refl(left_);
      def wrong : value = right_ := refl(right_);
    `:"");
    if(argument==="tt")assert.deepEqual(failures(result).map(([name])=>name),["wrong"],JSON.stringify(failures(result)));
    else assert.ok(failures(result).some(([name])=>name==="Alias"),"normalization cannot discard the helper's invalid argument");
  });
});
