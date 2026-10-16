import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {contextualScenarios} from "./fixtures/contextual-sessions.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";
import {CubicalKernel,KernelError} from "../web/cubical-kernel.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {replayPolicyCallbacks,kernelReplayPolicy} from "../web/cubical-replay-inputs.mjs";

const module=await create();
const scenario=id=>contextualScenarios.find(entry=>entry.id===id);
const at=(program,source,marker,phase="expression")=>{
  const selected=[...program.scopePoints.values()].filter(point=>point.origin.module==="main"
    &&point.origin.start===source.indexOf(marker)&&point.phase===phase
    &&(phase!=="expression"||point.origin.end===source.indexOf(marker)+marker.replace(/;$/,"").length));
  assert.equal(selected.length,1,`${phase}: ${marker}`);
  return new ContextualSession(program,selected[0].id);
};
const setup=(t,source,options={})=>checkProgram(t,source,{module,...options,
  options:{collectScopes:true,...options.options}});
const query=async(session,source,kind,text)=>{
  const [result]=await session.run(source);
  assert.equal(result.kind,kind,JSON.stringify(result));
  if(text!==undefined)assert.equal(result.text,text);
  return result;
};

test("CB1 contextual session: nested-function",async t=>{
  const fixture=scenario("nested-function"),{program}=await setup(t,fixture.source);
  const session=at(program,fixture.source,fixture.marker);
  const before={work:program.kernel.work(),definitions:[...program.kernel.definitions],
    symbols:JSON.stringify(program.symbols),scopes:program.scopePoints.size};
  const handles=new Set(),disposed=[],oldInfer=Translator.prototype.term,dispose=CubicalKernel.prototype.dispose;
  CubicalKernel.prototype.dispose=function() {disposed.push(this.handle);return dispose.call(this);};
  Translator.prototype.term=function(node,scope,expected) {
    if(scope.unit.moduleName.startsWith("contextual-session/"))handles.add(scope.checker.kernel.handle);
    return oldInfer.call(this,node,scope,expected);
  };
  const results=[];
  try {
    for(const entry of fixture.sessions) {
      const expected=entry.accepts===false?"error":entry.entry.startsWith("let ")?"defined":entry.type?"type":"value";
      results.push(await query(session,entry.entry,expected,entry.value??entry.type));
    }
  } finally {Translator.prototype.term=oldInfer;CubicalKernel.prototype.dispose=dispose;}
  assert.equal(session.accepted.length,1);
  assert.ok(!handles.has(program.kernel.handle));
  assert.equal(disposed.length,fixture.sessions.length);
  assert.ok(disposed.every(handle=>handle!==program.kernel.handle));
  // Handles may be reused after disposal; each request's work starts afresh.
  for(const result of results)for(const phase of ["prefix","validation","history","query"]) {
    assert.ok(result.costs[phase].elapsedMs>=0,phase);
    assert.ok(result.costs[phase].work.instructions>=0,phase);
  }
  assert.ok(results[2].costs.history.work.instructions>0);
  assert.ok(results[0].conditional);
  assert.deepEqual({work:program.kernel.work(),definitions:[...program.kernel.definitions],
    symbols:JSON.stringify(program.symbols),scopes:program.scopePoints.size},before);
  assert.deepEqual(JSON.parse(JSON.stringify(results)),results);
  assert.equal(Object.isFrozen(session.accepted[0]),true);
});

test("replayed recursive calls keep structural permissions and cannot change a selected motive",async t=>{
  const source="import nat; def f(n, m : Nat) : Nat := match n { zero => m; succ(k) => f(k, m); };";
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  const session=at(program,source,"f(k, m)");
  await query(session,"typeof f(k, m)","type","Nat");
  await query(session,"f(n, m)","error");
  await query(session,"f(k, zero)","error");
  await query(session,"typeof f(k, m)","type","Nat");
});

test("universe parameters and interval coordinates remain available by identity",async t=>{
  const source="def poly{{U < UU0}}(A : U, x : A) : A := x; def line(p : tt = tt) : tt = tt := path i => p @ i;";
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  const universe=at(program,source,"x;"),dimension=at(program,source,"p @ i");
  await query(universe,"typed(A, x)","value","x");
  await query(universe,"let identity := fun (y : A) => y","defined");
  await query(universe,"identity(x)","value","x");
  await query(universe,"let reflexive : x = x { rfl; }","defined");
  await query(universe,"typed(x = x, reflexive)","value");
  await query(dimension,"p @ i","value");
  await query(dimension,"p @ j","error");
});

test("contextual model queries share the replay compilation's exact projection identities",async t=>{
  const source=`import hlevels;
    inductive Two : set U0 { left_; right_; }
    theory Leaf(U < UU0) { M : set U; x : M; }
    def chosen : Leaf(U0) := Leaf.make(Two, _, left_);
    def f(m : Leaf(U0), y : Two) : Two := y;`;
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  const session=at(program,source,"y;");
  await query(session,"typeof m.x","type");
  await query(session,"typeof Leaf.x(m)","type");
  await query(session,"chosen.x","value","left_");
  await query(session,"chosen.(x)","value","left_");
  await query(session,"let saved := chosen.x","defined");
  await query(session,"saved","value","left_");
  await query(session,"let chosen := tt","defined");
  await query(session,"chosen.x","error");
  await query(session,"saved","value","left_");
  await query(session,"typeof m.x","type");
});

test("contextual selections preserve the source named-notation namespace across scratch bindings",async t=>{
  for(const attached of [false,true])await t.test(attached?"model-attached rules":"standalone notation",async t=>{
    const model=`def recipe : Numerals(U0) := Numerals.make(Nat, fun (n : Nat) => n);`;
    const notation=`notation recipe { numeral(n : Nat) := succ(n); }`;
    const source=`inductive Nat { zero; succ(n : Nat); }
      theory Numerals(U < UU0) { M : U; read(n : Nat) : M; }
      def read(n : Nat) : Nat := succ(n);
      ${attached?model+notation:notation+model}
      def source_value : Nat := recipe.(read(zero));
      def intended : source_value = ${attached?"zero":"succ(zero)"} := refl(${attached?"zero":"succ(zero)"});
      def f(k : Nat) : Nat := k;`;
    const {program,result}=await setup(t,source);
    assert.deepEqual(result.gaps,[]);
    const session=at(program,source,"k;");
    await query(session,"evaluate recipe.(read(zero))","value",attached?"zero":"succ(zero)");
    await query(session,"evaluate read(zero)","value","succ(zero)");
    await query(session,"evaluate source_value","value",attached?"zero":"succ(zero)");
    await query(session,"let saved := source_value","defined");
    await query(session,"evaluate recipe.(read(zero))","value",attached?"zero":"succ(zero)");
    await query(session,"let recipe := tt","defined");
    if(attached)assert.match((await query(session,"recipe.(read(zero))","error")).text,/use selects a model/);
    else await query(session,"evaluate recipe.(read(zero))","value","succ(zero)");
    await query(session,"evaluate saved","value",attached?"zero":"succ(zero)");
  });
});

test("CB1 contextual session: let-before-after",async t=>{
  const fixture=scenario("let-before-after"),{program}=await setup(t,fixture.source);
  const initializer=at(program,fixture.source,"succ(next_)"),after=at(program,fixture.source,fixture.marker,"after");
  await query(initializer,fixture.sessions[0].entry,"value");
  await query(after,fixture.sessions[1].entry,"error");
  await query(after,fixture.sessions[2].entry,"value");
});

test("scratch proof blocks share source set identities through history and local shadowing",async t=>{
  const source=`import nat;
simp_set rules := [nat_add_zero];
def focus(n : Nat) : Nat := n;
simp_set later := [nat_add_zero];`;
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  const session=at(program,source,"n;");
  const before={work:program.kernel.work(),definitions:[...program.kernel.definitions]};
  await query(session,"let h : add(n, zero) = n { simp only [rules]; }","defined");
  await query(session,"let rules := tt","defined");
  await query(session,"let copied : n = n { simp only [h] at h as h2; exact h2; }","defined");
  await query(session,"let supplied : n = n { simpa only [rules] using h; }","defined");
  assert.match((await query(session,"let bad : add(n, zero) = n { simp only [later]; }","error")).text,/Untranslated name: later/);
  await query(session,"with unfolding [nat_add_zero] { n }","value","n");
  await query(session,"typeof supplied","type","n = n");
  assert.equal(session.accepted.length,4);
  assert.deepEqual({work:program.kernel.work(),definitions:[...program.kernel.definitions]},before);
});

test("CB1 contextual session: selected-failing-prefix",async t=>{
  const fixture=scenario("selected-failing-prefix"),{program}=await setup(t,fixture.source);
  const session=at(program,fixture.source,fixture.marker,"before");
  await query(session,fixture.sessions[0].entry,"value");
  await query(session,"let saved := next_","defined","saved : Nat");
  await query(session,"typed(Unit, saved)","error");
  await query(session,"evaluate saved","value","succ(k)");
  await query(session,"broken(k)","error");
  await query(session,"independent","error");
  assert.equal(program.kernel.definitions.has("main__broken"),false);
  assert.equal(session.accepted.length,1);
});

test("replay pins imported text, full declaration order, and the import reader's legacy mode",async t=>{
  const source="import dep; def selected(x : Unit) : Unit := kept; def later : Unit := tt;";
  let reads=0;
  const reader=async()=>{reads++;return "def unrelated : Unit := tt; def kept : Unit := tt;";};
  reader.nameBased=()=>false;
  const {program}=await setup(t,source,{reader});
  const session=at(program,source,"kept");
  const checked=[],translate=Translator.prototype.translate;
  Translator.prototype.translate=function(text,env) {
    checked.push([this.moduleName,text,this.nameBased]);
    return translate.call(this,text,env);
  };
  reader.nameBased=()=>true;
  program.readSource=async()=>{throw Error("The live reader must not run during replay.");};
  try {await query(session,"kept","value","tt");}
  finally {Translator.prototype.translate=translate;}
  assert.equal(reads,1);
  assert.deepEqual(checked.map(([name])=>name),["dep","main"]);
  assert.ok(checked[0][1].includes("unrelated"));
  assert.ok(checked.every(([, ,legacy])=>legacy===false));
  await query(session,"later","error");
});

test("a replayed local context must actually be well formed",async t=>{
  const source="def invalid := fun (x : tt) => tt;";
  const {program,result}=await setup(t,source);
  assert.equal(result.gaps.length,1);
  const point=[...program.scopePoints.values()].find(point=>point.origin.module==="main"
    &&point.origin.start===source.lastIndexOf("tt")&&point.phase==="expression");
  assert.ok(point.available,"describing the prefix is not a proof that it is a context");
  const session=new ContextualSession(program,point.id);
  const answer=await query(session,"tt","unavailable");
  assert.equal(answer.stage,"validation");
  assert.equal(session.accepted.length,0);
});

test("scratch bindings, shadowing and concurrent requests are isolated between sessions",async t=>{
  const source="def source_(x : Unit) : Unit := x;";
  const {program}=await setup(t,source);
  const a=at(program,source,"x;"),b=at(program,source,"x;");
  const requests=[a.run("let held := x"),a.run("typeof held")];
  const results=(await Promise.all(requests)).flat();
  assert.deepEqual(results.map(result=>result.kind),["defined","type"]);
  await query(b,"held","error");
  await query(a,"let x := fun (y : Unit) => x","defined");
  await query(a,"typeof held","type","Unit");
  await query(a,"typeof x","type","Unit -> Unit");
  await query(b,"typeof x","type","Unit");
});

test("rechecks invalidate a session before asynchronous source discovery completes",async t=>{
  const source="import dep; def selected : Unit := tt;";
  let release,slow=false;
  const reader=async()=>{if(slow)await new Promise(resolve=>release=resolve);return "def imported : Unit := tt;";};
  const {program}=await setup(t,source,{reader});
  const session=at(program,source,"tt");
  slow=true;
  const checking=program.check(source,"main");
  await Promise.resolve();
  await query(session,"tt","unavailable");
  release();await checking;
  await query(session,"tt","unavailable");
});

test("a failed accepted-history replay reports the entry and preserves history",async t=>{
  const source="def selected : Unit := tt;",{program}=await setup(t,source);
  const session=at(program,source,"tt");
  await query(session,"let held := tt","defined");
  const before=session.accepted,bindLet=Translator.prototype.bindLet;
  Translator.prototype.bindLet=function(statement,scope) {
    if(scope.unit.moduleName.startsWith("contextual-session/"))throw new KernelError("Injected history budget exhaustion.","budget");
    return bindLet.call(this,statement,scope);
  };
  let result;
  try {result=await query(session,"typeof held","unavailable");}
  finally {Translator.prototype.bindLet=bindLet;}
  assert.equal(result.stage,"history");assert.equal(result.entry,1);assert.equal(result.failure,"budget");
  assert.deepEqual(session.accepted,before);
  await query(session,"typeof held","type","Unit");
});

test("prefix resource exhaustion cannot select a nearby point or run a query",async t=>{
  const source="def earlier : Unit := tt; def selected(x : Unit) : Unit := x;";
  const {program}=await setup(t,source);
  const point=[...program.scopePoints.values()].find(point=>point.origin.module==="main"
    &&point.origin.start===source.lastIndexOf("x")&&point.phase==="expression");
  for(const kind of ["fuel","budget","deadline"]) {
    const session=new ContextualSession(program,point.id),term=Translator.prototype.term;
    Translator.prototype.term=function(node,scope,expected) {
      if(scope.checker.kernel.handle!==program.kernel.handle&&scope.unit.declaring==="selected")
        throw Object.assign(Error(`Injected ${kind} exhaustion.`),{kind});
      return term.call(this,node,scope,expected);
    };
    let result;
    try {result=await query(session,"tt","unavailable");}
    finally {Translator.prototype.term=term;}
    assert.equal(result.failure,kind);
    assert.equal(result.stage,"prefix");
    assert.equal(result.costs.query,null);
  }
});

test("resource replay preserves deadline epochs and the original kernel retry cap",async t=>{
  const source="def first : Unit := tt; def second : Unit := tt;";
  let program;
  // Capture through real check callbacks, as the benchmark installs limits.
  const {CubicalProgram}=await import("../web/cubical-program.mjs");
  program=new CubicalProgram(module,async()=>"",{collectScopes:true,onDeclarationStart(_module,declaration) {
    if(declaration.name.text==="first")program.kernel.setDeadline(60000);
  }});
  t.after(()=>program.dispose());
  program.kernel.stepBudget=10000n;program.kernel.maxQuerySteps=20000n;
  await program.check(source,"main");
  const snapshot=program.scopeReplay.snapshot(),kernel=new CubicalKernel(module);
  t.after(()=>kernel.dispose());
  const callbacks=replayPolicyCallbacks(snapshot,kernel);
  for(const event of snapshot.events) {
    const before=kernel.deadlineGeneration;
    const previous=snapshot.events[snapshot.events.indexOf(event)-1]?.policy??snapshot.initialPolicy;
    callbacks[event.stage==="start"?"onDeclarationStart":"onDeclaration"](event.module,{name:{text:event.name}});
    assert.equal(kernel.deadlineGeneration-before,event.policy.deadlineGeneration===previous.deadlineGeneration?0:1);
    assert.equal(kernel.stepBudget,10000n);assert.equal(kernel.maxQuerySteps,20000n);
  }
  assert.equal(kernelReplayPolicy(kernel).deadlineDuration,60000);
  // Later live adjustments cannot loosen this session's saved budget.
  program.kernel.stepBudget=10000000n;
  const session=at(program,source,"tt");
  await query(session,"tt","value","tt");
});

test("replay observes failed prefix directives before entering a later scope",async t=>{
  const source="evaluate tt expecting tt; def selected(x : Unit) : Unit := x;";
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  const target=at(program,source,"x;");
  const events=program.scopeReplay.snapshot().events;
  assert.deepEqual(events.slice(0,2).map(event=>event.stage),["directive-start","directive-end"]);
  const evaluate=Translator.prototype.evaluate;
  for(const kind of ["fuel","budget","deadline"]) {
    Translator.prototype.evaluate=function(){throw Object.assign(Error(`prefix directive ${kind}`),{kind});};
    let answer;
    try {answer=await query(target,"x","unavailable");}
    finally {Translator.prototype.evaluate=evaluate;}
    assert.equal(answer.failure,kind);
    assert.equal(answer.stage,"prefix");
    assert.equal(answer.costs.query,null);
  }
  await query(target,"x","value","x");
});

test("recorded fuel limits cannot be changed by mutating the caller's options",async t=>{
  const source="def selected(x : Unit) : Unit := x;",declarationFuel={queries:50000};
  const {program,result}=await setup(t,source,{options:{declarationFuel}});
  assert.deepEqual(result.gaps,[]);
  declarationFuel.queries=0;
  await program.check(source,"main");
  assert.equal(program.scopeReplay.snapshot().fuelLimits.declarationFuel.queries,50000);
  await query(at(program,source,"x;"),"x","value","x");
});

test("context collection requires the transaction policy used by isolated replay",async t=>{
  assert.throws(()=>new CubicalProgram(module,async()=>"",{collectScopes:true,manageTransactions:false}),/requires declaration transactions/);
  const {program}=await setup(t,"def f : Unit := tt;");
  program.manageTransactions=false;
  await assert.rejects(program.check("def g : Unit := tt;","main"),/requires declaration transactions/);
});

test("recursive queries retain permissions through compiled nested match refinements",async t=>{
  const source=`inductive N { zero; succ(n : N); }
def f(n : N) : N {
  match n { zero => { exact zero; } succ(k) => {
    match k {
      zero => { exact zero; }
      succ(zero) => { exact zero; }
      succ(succ(j)) => { exact f(k); }
    }
  } }
}`;
  const {program,result}=await setup(t,source);
  assert.deepEqual(result.gaps,[]);
  await query(at(program,source,"f(k)"),"typeof f(k)","type","N");
  await query(at(program,source,"f(k)"),"typeof f(n)","error");
});
