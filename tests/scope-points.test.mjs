import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {contextualScenarios} from "./fixtures/contextual-sessions.mjs";
import {ElaborationStop} from "../web/translator/control.mjs";
import {ScopePoints} from "../web/translator/scope-points.mjs";
import {Scope,SourceUnit} from "../web/translator/elaboration.mjs";
import {T} from "../web/translator/core.mjs";

const module=await create();
const scenario=id=>contextualScenarios.find(entry=>entry.id===id);
const points=(program,name="main")=>[...program.scopePoints.values()].filter(point=>point.origin.module===name);
const at=(program,source,marker,phase="expression")=>points(program).filter(point=>
  point.origin.start===source.indexOf(marker)&&point.phase===phase
    &&(phase!=="expression"||point.origin.end===source.indexOf(marker)+marker.length));
const binding=(point,label)=>point.lexical.find(([key])=>key===label)?.[1].id;
const setup=(t,source,options={})=>checkProgram(t,source,{module,options:{collectScopes:true,...options}});

test("nested function scope descriptions preserve identity, visibility, origins and parent instances",async t=>{
  const fixture=scenario("nested-function"),{program,result}=await setup(t,fixture.source);
  assert.deepEqual(result.gaps,[]);
  const selected=at(program,fixture.source,fixture.marker);
  assert.equal(selected.length,1);
  const [point]=selected;
  assert.equal(point.available,true,point.reason);
  for(const label of fixture.visible) {
    const record=program.scopeRecorder.table.get(binding(point,label));
    assert.equal(record.label,label);
    assert.equal(record.origin.module,"main");
    assert.equal(fixture.source.slice(record.origin.start,record.origin.end),label);
  }
  assert.equal(binding(point,"f"),undefined);
  assert.equal(program.scopeRecorder.table.get(binding(point,"Nat")).origin.module,"nat");
  for(const entry of points(program))if(entry.parent)assert.ok(program.scopePoints.has(entry.parent),entry.id);
  assert.deepEqual(JSON.parse(JSON.stringify(point)),point);
  assert.ok(Object.isFrozen(point.state.context.nodes));
  const callee=points(program).find(entry=>entry.origin.start===point.origin.start&&entry.origin.end===point.origin.start+3
    &&entry.phase==="expression");
  assert.equal(callee.state.bindings,point.state.bindings,"same lexical frame shares inert binding data");
  assert.equal(callee.state.context,point.state.context,"same telescope shares inert type data");
  const serialized=JSON.stringify(point);
  program.dispose();
  assert.equal(JSON.stringify(point),serialized,"no native handle is needed to read a stored description");
});

test("a shadowing let has separate initializer and after-statement contexts",async t=>{
  const fixture=scenario("let-before-after"),{program,result}=await setup(t,fixture.source);
  assert.deepEqual(result.gaps,[]);
  const [initializer]=at(program,fixture.source,"succ(next_)"),[after]=at(program,fixture.source,fixture.marker,"after");
  assert.ok(initializer?.available,initializer?.reason);
  assert.ok(after?.available,after?.reason);
  assert.notEqual(binding(initializer,"next_"),binding(after,"next_"));
  assert.equal(binding(initializer,"saved"),binding(after,"saved"));
  const [before]=at(program,fixture.source,fixture.marker,"before");
  assert.equal(binding(initializer,"next_"),binding(before,"next_"));
  const [conclusion]=at(program,fixture.source,"exact next_","before");
  assert.equal(binding(conclusion,"next_"),binding(after,"next_"));
});

test("shared lexical descriptions retain each point's mutable recursion permissions",()=>{
  const descriptions=[],recorder=new ScopePoints("permissions",{onPoint:point=>descriptions.push(point)});
  recorder.declaration("main",{name:{text:"f",start:4,end:5}},"main__f");
  const unit=new SourceUnit({checker:{},moduleName:"main",declaring:"f",scopePoints:recorder}).declaration();
  const recursive={tag:"Recursive",source:"f",state:"pending",bindings:new Map([["n",T.point]])};
  const scope=new Scope(unit,new Map(),new Map([["f",recursive],["\u0000recursive",recursive]]));
  const node={kind:"name",name:"f",start:20,end:21};
  recorder.around(null,node,scope,{},()=>{});
  const saved=JSON.stringify(descriptions[0]);
  recursive.state="selected";
  recursive.bindings.set("n",T.unit);
  recorder.around(null,node,scope,{},()=>{});
  assert.ok(descriptions.every(point=>point.available));
  assert.equal(descriptions[0].state.bindings,descriptions[1].state.bindings);
  assert.notDeepEqual(descriptions[0].state.recursion,descriptions[1].state.recursion);
  assert.equal(JSON.stringify(descriptions[0]),saved);
});

test("a declaration's later failure keeps selected prefix descriptions after native rollback",async t=>{
  const fixture=scenario("selected-failing-prefix"),{program,result}=await setup(t,fixture.source);
  assert.deepEqual(result.gaps.map(gap=>[gap.name,gap.code]),fixture.gaps);
  const [point]=at(program,fixture.source,fixture.marker,"before");
  assert.ok(point?.available,point?.reason);
  for(const label of fixture.visible)assert.ok(binding(point,label),label);
  assert.equal(binding(point,"broken"),undefined);
  assert.equal(program.kernel.definitions.has("main__broken"),false);
  assert.equal(program.kernel.definitions.has("main__independent"),true);
});

test("discarded written implicit-path bodies publish no selectable instance",async t=>{
  const fixture=scenario("discarded-path-body"),{program,result}=await setup(t,fixture.source);
  assert.deepEqual(result.gaps.map(gap=>[gap.name,gap.code]),fixture.gaps);
  const start=fixture.source.indexOf(fixture.marker)+fixture.marker.indexOf("right_");
  assert.deepEqual(points(program).filter(point=>point.origin.start===start),[]);
  assert.ok(points(program).some(point=>fixture.source.slice(point.origin.start,point.origin.end)==="left_"));
});

test("reference collection cannot change scope identities or declaration fuel",async t=>{
  const fixture=scenario("nested-function");
  const withReferences=await setup(t,fixture.source,{scopeRevision:"same-input",collectReferences:true});
  const withoutReferences=await setup(t,fixture.source,{scopeRevision:"same-input",collectReferences:false});
  assert.deepEqual([...withReferences.program.scopePoints],[...withoutReferences.program.scopePoints]);
  assert.deepEqual(withReferences.result.outputs.map(output=>output.searchFuel),withoutReferences.result.outputs.map(output=>output.searchFuel));
  const unobserved=await checkProgram(t,fixture.source,{module});
  assert.deepEqual(withReferences.result.outputs.map(output=>output.searchFuel),unobserved.result.outputs.map(output=>output.searchFuel));
  assert.deepEqual(withReferences.program.kernel.work(),unobserved.program.kernel.work());
});

test("source rechecks rebuild imported scopes and invalidate the previous registry",async t=>{
  const source="import dep; def f(x : Unit) : Unit := x;";
  let dependency="def imported : Unit := tt;";
  const {program}=await checkProgram(t,source,{module,reader:async()=>dependency,options:{collectScopes:true}});
  const oldRecorder=program.scopeRecorder,oldRevision=program.scopeRevision,oldPoints=program.scopePoints;
  dependency="def replacement : Unit := tt;";
  const result=await program.check(source,"main");
  assert.deepEqual(result.gaps,[]);
  assert.notEqual(program.scopeRecorder,oldRecorder);
  assert.notEqual(program.scopeRevision,oldRevision);
  assert.ok(points(program,"dep").length);
  assert.ok([...oldPoints.keys()].every(id=>!program.scopePoints.has(id)));
  assert.equal(program.scopeSources.dep,dependency);
  assert.equal(program.kernel.definitions.has("dep__imported"),false);
});

test("the module REPL keeps its cached imports without replacing the source scope registry",async t=>{
  const {program}=await setup(t,"def base : Unit := tt;");
  const recorder=program.scopeRecorder,registry=program.scopePoints;
  const result=await program.checkEntry("import main; def saved := base;","entry");
  assert.deepEqual(result.gaps,[]);
  assert.equal(result.declarations.length,1);
  assert.equal(result.declarations[0].verified,true);
  assert.equal(program.scopeRecorder,recorder);
  assert.equal(program.scopePoints,registry);
  assert.equal(points(program,"entry").length,0);
});

test("a rejected duplicate cannot reassign a retained declaration's source origin",async t=>{
  const source="def saved : Unit := tt; def saved : Unit := tt; def client : Unit := saved;";
  const {program,result}=await setup(t,source);
  assert.equal(result.gaps.length,1);
  const use=points(program).find(entry=>entry.origin.start===source.lastIndexOf("saved")&&entry.phase==="expression");
  assert.ok(use?.available,use?.reason);
  const record=program.scopeRecorder.table.get(binding(use,"saved"));
  assert.equal(record.origin.start,source.indexOf("saved"));
});

test("private replay interception occurs before buffered observation publication and unwinds cleanly",async t=>{
  const source="import nat; def f(n, m : Nat) : Nat := match n { zero => m; succ(k) => f(k, m); };";
  const initial=await setup(t,source,{scopeRevision:"attempt-replay"});
  const [selected]=at(initial.program,source,"f(k, m)");
  assert.ok(selected?.attempt.length,selected?.id);
  const stop=new ElaborationStop({kind:"value",text:"detached result"});
  let visits=0,probes=0;
  // Use the real callback in a fresh program; no patch to Translator.term.
  const {CubicalProgram}=await import("../web/cubical-program.mjs");
  const replay=new CubicalProgram(module,initial.program.readSource,{collectScopes:true,scopeRevision:"attempt-replay",scopeTarget:selected.id,
    scopeProbe(point,live) {
      probes++;
      if(point.id!==selected.id)return;
      visits++;
      assert.deepEqual(point,selected);
      assert.equal(replay.scopePoints.has(point.id),false);
      assert.ok(live.scope);
      throw stop;
    }});
  t.after(()=>replay.dispose());
  await assert.rejects(replay.check(source,"main"),value=>value===stop);
  assert.equal(visits,1);
  assert.equal(probes,1,"full prefix replay materializes only the requested scope");
  assert.equal(replay.scopePoints.size,0,"the stop precedes publication of the requested point");
  assert.equal(replay.kernel.definitions.has("main__f"),false);
});
