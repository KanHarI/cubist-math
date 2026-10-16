import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";
import {LexicalContext} from "../web/cubist/bindings.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const module=await create();
const naturals="inductive Nat { zero; succ(n : Nat); }\n";
const theory="theory T(U < UU0) { M : U; c : M; def get(x : M) : M := x; }\n";
const model="def instance_ : T(U0) := T.make(Nat, zero);\n";
const setup=(t,source,options={})=>checkProgram(t,source,{module,...options,
  options:{collectScopes:true,...options.options}});
function select(t,program,source,marker,{name="main",declaration="f",phase="expression",length=marker.length}={}) {
  assert.equal(source.split(marker).length,2,"unique authored occurrence");
  const start=source.indexOf(marker);
  const points=[...program.scopePoints.values()].filter(point=>point.origin.module===name
    &&point.origin.start===start&&point.origin.end===start+length&&point.declaration===declaration&&point.phase===phase);
  assert.equal(points.length,1,JSON.stringify(points));
  const [point]=points;
  assert.ok(point.available,point.reason);
  const session=new ContextualSession(program,point.id);
  t.after(()=>session.dispose());
  return session;
}
async function query(session,source,kind,text) {
  const [result]=await session.run(source);
  assert.equal(result.kind,kind,JSON.stringify(result));
  if(text!==undefined)assert.equal(result.text,text);
  return result;
}

test("inductive context labels preserve the header's ordinary missing-name diagnostic",async t=>{
  for(const collectScopes of [false,true]) {
    const {result}=await checkProgram(t,"inductive Foo(A : Foo) { mk; }",{module,options:{collectScopes}});
    assert.equal(result.gaps.length,1);
    assert.match(result.gaps[0].reason,/Untranslated name: Foo/);
  }
});

test("model openings preserve their checked receiver in expression, statement and file contexts",async t=>{
  const cases=[
    {name:"expression",body:"def f : Nat := instance_.(c);",marker:"c);",length:1},
    {name:"statement",body:"def f : Nat { use instance_; exact c; }",marker:"exact c;",phase:"before"},
    {name:"file",body:"use instance_; def f : Nat := c;",marker:"c;",length:1},
  ];
  for(const c of cases)await t.test(c.name,async t=>{
    const source=naturals+theory+model+"def c : Nat := succ(zero);\n"+c.body+
      "\ndef checked : f = zero := refl(zero);";
    const {program,result}=await setup(t,source);
    assert.deepEqual(result.gaps,[]);
    const session=select(t,program,source,c.marker,{phase:c.phase,length:c.length});
    await query(session,"typed(c = zero, refl(c))","value");
    await query(session,"typed(c = succ(zero), refl(c))","error");
    await query(session,"let saved := c","defined");
    await query(session,"let c := succ(zero)","defined");
    await query(session,"typed(saved = zero, refl(saved))","value");
    await query(session,"typed(c = succ(zero), refl(c))","value");
  });
});

test("a local opening shadows an earlier binder and a later let shadows the opening",async t=>{
  const source=naturals+theory+model+`def f(c : Nat) : Nat {
    use instance_;
    let saved := c;
    let c := succ(saved);
    exact c;
  }
  def checked : f(succ(zero)) = succ(zero) := refl(succ(zero));`;
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  const opened=select(t,program,source,"c;\n    let c",{length:1});
  await query(opened,"typed(c = zero, refl(c))","value");
  await query(opened,"typed(c = succ(zero), refl(c))","error");
  const after=select(t,program,source,"exact c;",{phase:"before"});
  await query(after,"typed(c = succ(zero), refl(c))","value");
  await query(after,"typed(saved = zero, refl(saved))","value");
  await query(after,"typed(c = zero, refl(c))","error");
  const earlier=new LexicalContext(opened.point.lexical).snapshot().filter(([label])=>label==="c");
  const later=new LexicalContext(after.point.lexical).lookup("c");
  assert.ok(earlier.length);
  assert.ok(earlier.every(([,resolution])=>resolution.id!==later.id));
});

test("selected standalone and attached notation retain their exact checked rules",async t=>{
  for(const attached of [false,true])await t.test(attached?"attached":"standalone",async t=>{
    const source=naturals+(attached?theory+model:"")+`notation ${attached?"instance_":"keep"} {
        ${attached?"numeral(n : Nat) := succ(n);":"x + y := x;"}
      }
      def f(k : Nat) : Nat := ${attached?"instance_":"keep"}.(${attached?"k":"k + zero"});`;
    const {program,result}=await setup(t,source);
    assert.deepEqual(result.gaps,[]);
    const session=select(t,program,source,attached?"k);":"k + zero",{length:attached?1:8});
    const expression=attached?"1":"zero + succ(zero)",expected=attached?"succ(succ(zero))":"zero";
    await query(session,`typed((${expression}) = ${expected}, refl(${expected}))`,"value");
    await query(session,`typed((${expression}) = succ(zero), refl(${expected}))`,"error");
    await query(session,`let saved := ${expression}`,"defined");
    await query(session,`typed(saved = ${expected}, refl(saved))`,"value");
  });
});

test("generated and inherited helpers select distinct instances of the authored body",async t=>{
  const fixture=theory,source="import fixture; theory Child(U < UU0) extends T {}";
  const read=sourceReader();
  const {program,result}=await setup(t,source,{reader:(name,...args)=>name==="fixture"?fixture:read(name,...args)});
  assert.deepEqual(result.gaps,[]);
  const sessions=["T.get","Child.get"].map(declaration=>select(t,program,fixture,"x;",
    {name:"fixture",declaration,length:1}));
  assert.notEqual(sessions[0].point.id,sessions[1].point.id);
  for(const session of sessions) {
    await query(session,"x","value","x");
    await query(session,"typed(x = x, refl(x))","value");
    await query(session,"let x := tt","defined");
    await query(session,"x","value","tt");
  }
});

test("collecting model and notation scopes preserves source results and kernel work",async t=>{
  const source=naturals+theory+model+`notation keep { x + y := x; }
    def f(c : Nat) : Nat { use instance_; let c := succ(c); exact keep.(c + zero); }
    def checked : f(zero) = succ(zero) := refl(succ(zero));`;
  const off=await setup(t,source,{options:{collectScopes:false}}),on=await setup(t,source);
  assert.deepEqual(off.result.gaps,[]);
  assert.deepEqual(on.result.gaps,[]);
  assert.deepEqual(on.result.outputs,off.result.outputs);
  assert.deepEqual(on.result.links,off.result.links);
  assert.deepEqual(on.program.kernel.work(),off.program.kernel.work());
  assert.equal(off.program.scopePoints.size,0);
  assert.ok(on.program.scopePoints.size>0);
});

test("section contexts apply earlier definitions and refresh cached model openings",async t=>{
  const source=theory+`section (S : T(U0), x : S.M) {
    def first_ : M := x;
    def second_ : M := first_;
    def third_ : M := c;
  }`;
  const off=await setup(t,source,{options:{collectScopes:false}}),on=await setup(t,source);
  assert.deepEqual(off.result.gaps,[]);
  assert.deepEqual(on.result.gaps,[]);
  assert.deepEqual(on.result.outputs,off.result.outputs);
  assert.deepEqual(on.result.links,off.result.links);
  assert.deepEqual(on.program.kernel.work(),off.program.kernel.work());
  const second=select(t,on.program,source,"first_;",{declaration:"second_",length:6});
  await query(second,"typed(first_ = x, refl(x))","value");
  await query(second,"typed(c = S.c, refl(c))","value");
  const third=select(t,on.program,source,"c;\n  }",{declaration:"third_",length:1});
  await query(third,"typed(second_ = x, refl(x))","value");
  await query(third,"typed(c = S.c, refl(c))","value");
  await query(third,"typed(c = x, refl(x))","error");
});

test("cached section notation uses the current declaration's model parameter",async t=>{
  const source=`theory R(U < UU0) { M : U; op(x, y : M) : M notation x + y; }
    section (S : R(U0), x : S.M) {
      def first_ : M := x + x;
      def second_ : M := first_;
      def third_ : M := second_;
    }`;
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  const session=select(t,program,source,"second_;",{declaration:"third_",length:7});
  await query(session,"typed((x + x) = S.op(x, x), refl(S.op(x, x)))","value");
  await query(session,"typed(second_ = S.op(x, x), refl(second_))","value");
  await query(session,"typed((x + x) = x, refl(x))","error");
});

test("inductive constructor contexts keep provisional self and earlier constructors local",async t=>{
  const source="inductive List(U < UU0, A : U) { nil; cons(head : A, tail : List(U, A)); }";
  const off=await setup(t,source,{options:{collectScopes:false}}),on=await setup(t,source);
  assert.deepEqual(on.result.gaps,[]);
  assert.deepEqual(on.result.outputs,off.result.outputs);
  assert.deepEqual(on.result.links,off.result.links);
  assert.deepEqual(on.program.kernel.work(),off.program.kernel.work());
  const session=select(t,on.program,source,"List(U, A)",{declaration:"List"});
  const before=on.program.kernel.work();
  await query(session,"typeof List(U, A)","type","UU0");
  await query(session,"typed(List(U, A), nil)","value");
  await query(session,"typeof head","type","A");
  for(const input of ["cons","tail","List(U0, A)"])await query(session,input,"error");
  await query(session,"let saved := nil","defined");
  await query(session,"typed(saved = nil, refl(saved))","value");
  assert.deepEqual(on.program.kernel.work(),before);
  const invalid=await setup(t,source.replace("List(U, A)","List(U0, A)"));
  assert.equal(invalid.result.gaps.length,1);
  assert.match(invalid.result.gaps[0].reason,/applied to its own parameters/);
});

test("a later rejected inductive signature leaves its earlier provisional context queryable",async t=>{
  const source="inductive Bad { zero; step(n : Bad); invalid : Unit; }";
  const {program,result}=await setup(t,source);
  assert.equal(result.gaps.length,1);
  const session=select(t,program,source,"Bad);",{declaration:"Bad",length:3});
  await query(session,"typed(Bad, zero)","value");
  await query(session,"step","error");
  await query(session,"invalid","error");
  await query(session,"typeof Bad","type","UU0");
});

test("generated initial and free constructor scopes use their own provisional identities",async t=>{
  const source=`import hlevels;
    theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M; }
    initial N : T(U0); free F(A : U0) : T(U0) on A;`;
  const {program,result}=await setup(t,source,{options:{collectGeneration:true}});
  assert.deepEqual(result.gaps,[]);
  const declarations=program.generation.get("main").flatMap(group=>group.declarations);
  const points=[...program.scopePoints.values()];
  assert.ok(points.every(point=>point.available),JSON.stringify(points.filter(point=>!point.available)));
  for(const name of ["N","F"]) {
    const declaration=declarations.find(d=>d.kind==="inductive"&&d.name.text===name);
    const candidates=points.filter(point=>point.declarationId===declaration.name.bindingId&&point.phase==="expression"
      &&point.origin.expansion.some(frame=>frame.kind==="substitution"&&frame.site.module==="main"
        &&frame.site.start===source.indexOf("M) :")));
    assert.equal(candidates.length,1,JSON.stringify(candidates));
    const session=new ContextualSession(program,candidates[0].id);t.after(()=>session.dispose());
    await query(session,`typed(${name==="N"?"N":"F(A)"}, ${name}.c)`,"value");
    await query(session,`${name}.op`,"error");
    if(name==="F")await query(session,"F(Unit)","error");
  }
});

test("observing historical name-based notation cannot change source checking",async t=>{
  const source=theory+"section (S : T(U0)) { def f : M := c; def g : M := c; }";
  const reader=sourceReader();reader.nameBased=()=>true;
  const off=await setup(t,source,{reader,options:{collectScopes:false}}),on=await setup(t,source,{reader});
  assert.deepEqual(off.result.gaps,[]);
  assert.deepEqual(on.result.gaps,[]);
  assert.deepEqual(on.result.outputs,off.result.outputs);
  assert.deepEqual(on.result.links,off.result.links);
  assert.deepEqual(on.program.kernel.work(),off.program.kernel.work());
  const contexts=[...on.program.scopePoints.values()].filter(point=>["f","g"].includes(point.declaration)
    &&source.slice(point.origin.start,point.origin.end)==="c");
  assert.equal(contexts.length,2);
  for(const point of contexts) {
    assert.equal(point.available,false);
    assert.match(point.reason,/Historical name-based notation/);
    const session=new ContextualSession(on.program,point.id);
    t.after(()=>session.dispose());
    await query(session,"c","unavailable");
  }
});
