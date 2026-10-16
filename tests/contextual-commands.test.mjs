import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {ContextualSession} from "../web/contextual-session.mjs";

const module=await create();
const nat="inductive Nat { zero; succ(n : Nat); }\n";
async function setup(t,source,marker,{phase="before",length=marker.length}={}) {
  const {program,result}=await checkProgram(t,source,{module,options:{collectScopes:true}});
  assert.deepEqual(result.gaps,[]);
  assert.equal(source.split(marker).length,2);
  const start=source.indexOf(marker),points=[...program.scopePoints.values()].filter(point=>point.origin.module==="main"
    &&point.origin.start===start&&point.origin.end===start+length&&point.phase===phase);
  assert.equal(points.length,1,JSON.stringify(points));
  assert.ok(points[0].available,points[0].reason);
  const session=new ContextualSession(program,points[0].id);
  t.after(()=>session.dispose());
  return {program,session};
}
async function query(session,input,kind) {
  const [result]=await session.run(input);
  assert.equal(result.kind,kind,JSON.stringify(result));
  assert.deepEqual(JSON.parse(JSON.stringify(result)),result);
  return result;
}

test("/locals separates shadowed identities and preserves checked types through scratch history",async t=>{
  const source="def f(A : U0, x : A) : Unit { let saved := x; let x := tt; exact tt; }";
  const {session}=await setup(t,source,"exact tt;");
  const first=await query(session,"/locals","locals");
  const visible=first.bindings.filter(row=>row.visible),shadowed=first.bindings.filter(row=>!row.visible);
  assert.deepEqual(visible.map(({label,type})=>[label,type]),[["A","U0"],["saved","A"],["x","Unit"]]);
  assert.deepEqual(shadowed.map(({label,type})=>[label,type]),[["x","A"]]);
  assert.equal(shadowed[0].origin.start,source.indexOf("x : A"));
  assert.equal(visible.at(-1).origin.start,source.indexOf("x := tt"));
  assert.notEqual(visible.at(-1).resolution.id,shadowed[0].resolution.id);
  await query(session,"let x := A","defined");
  const after=await query(session,"/locals","locals");
  assert.deepEqual(after.bindings.filter(row=>row.label==="x").map(({type,visible})=>[type,visible]),
    [["A",false],["Unit",false],["U0",true]]);
  assert.equal(session.accepted.length,1);
  await query(session,"typed(saved = saved, refl(saved))","value");
});

test("/locals follows model openings without treating the hidden parameter as visible",async t=>{
  const source=nat+`theory T(U < UU0) { M : U; c : M; }
    def chosen : T(U0) := T.make(Nat, zero);
    def f(c : Nat) : Nat { use chosen; exact c; }`;
  const {session}=await setup(t,source,"exact c;");
  const result=await query(session,"/locals","locals"),cs=result.bindings.filter(row=>row.label==="c");
  assert.equal(cs.length,2);
  assert.deepEqual(cs.map(row=>row.visible),[false,true]);
  assert.equal(cs[1].resolution.tag,"projected");
  assert.equal(cs[1].origin.start,source.indexOf("chosen; exact"));
  assert.equal(cs[1].type,"chosen.M");
  await query(session,"typed(chosen.M, c)","value");
  await query(session,"typed(c = zero, refl(c))","value");
});

test("shadowed lets and obtain components retain the same branch refinements as visible locals",async t=>{
  const labels=new Set(["v","m","p","a","b"]);
  for(const kind of ["match","induction"])await t.test(kind,async t=>{
    const collected=[];
    for(const shadowed of [false,true]) {
      const source=nat+`def f(n : Nat) : Nat {
        let v := n; let m := succ(n); let p := refl(n);
        obtain (a, b) := typed(Nat and (n = n), (succ(n), refl(n)));
        ${shadowed?"let v := zero; let m := zero; let p := tt; let a := zero; let b := tt;":""}
        ${kind} n {
          zero => { exact m; }
          succ(k) ${kind==="induction"?"with ih":""} => { exact k; }
        }
      }`;
      const rows=[];
      for(const marker of ["exact m;","exact k;"]) {
        const {session}=await setup(t,source,marker);
        const locals=await query(session,"/locals","locals");
        rows.push(locals.bindings.filter(row=>labels.has(row.label)&&row.visible!==shadowed)
          .map(({label,type,value})=>({label,type,value})));
      }
      collected.push(rows);
    }
    assert.deepEqual(collected[1],collected[0]);
    assert.equal(collected[0][0].find(row=>row.label==="m").value,"succ(zero)");
    assert.equal(collected[0][0].find(row=>row.label==="p").type,"zero = zero");
    assert.equal(collected[0][1].find(row=>row.label==="m").value,"succ(succ(k))");
    assert.equal(collected[0][1].find(row=>row.label==="p").type,"succ(k) = succ(k)");
  });
});

test("opened-member receipts retain their source behavior through branch refinement",async t=>{
  const source=nat+`theory T(U < UU0) { M : U; c : M; }
    def f(n : Nat) : Nat {
      use T.make(Nat, n);
      match n { zero => { exact c; } succ(k) => { exact k; } }
    }`;
  const off=await checkProgram(t,source,{module});
  const on=await checkProgram(t,source,{module,options:{collectScopes:true}});
  assert.deepEqual(on.result.gaps,[]);
  assert.deepEqual(on.result.outputs,off.result.outputs);
  assert.deepEqual(on.result.links,off.result.links);
  assert.deepEqual(on.program.kernel.work(),off.program.kernel.work());
  const {session}=await setup(t,source,"exact c;");
  assert.equal((await query(session,"n","value")).text,"zero");
  assert.equal((await query(session,"c","value")).text,"n");
});

test("/locals describes universe variables and actual interval coordinates",async t=>{
  const poly="def poly{{U < UU0}}(A : U, x : A) : A := x;";
  const {session:universe}=await setup(t,poly,"x;",{phase:"expression",length:1});
  const listed=await query(universe,"/locals","locals");
  assert.ok(listed.bindings.some(row=>row.label==="U"&&row.visible&&row.type));
  const line="def line(p : tt = tt) : tt = tt := path i => p @ i;";
  const {session:dimension}=await setup(t,line,"p @ i",{phase:"expression"});
  const coordinates=await query(dimension,"/locals","locals");
  assert.ok(coordinates.bindings.some(row=>row.label==="i"&&row.visible&&row.type==="Interval"));
  await query(dimension,"p @ i","value");
});

test("proof experiments check the selected goal without changing source or scratch history",async t=>{
  const source=nat+"def proof(k : Nat) : k = k { exact refl(k); }";
  const {program,session}=await setup(t,source,"exact refl(k);");
  const before={work:program.kernel.work(),definitions:[...program.kernel.definitions],symbols:JSON.stringify(program.symbols)};
  const goal=await query(session,"/goal","goal");
  assert.equal(goal.goal,"k = k");
  assert.equal(goal.expected,null);
  await query(session,"let saved := k","defined");
  const accepted=JSON.stringify(session.accepted);
  const proof=await query(session,"/prove { let temporary := saved; exact refl(temporary); }","proof");
  assert.equal(proof.goal,goal.goal);
  await query(session,"/prove { exact refl(succ(k)); }","error");
  await query(session,"temporary","error");
  await query(session,"/prove { rfl; }","proof");
  assert.equal(JSON.stringify(session.accepted),accepted);
  assert.equal((await query(session,"/goal","goal")).goal,goal.goal);
  assert.deepEqual({work:program.kernel.work(),definitions:[...program.kernel.definitions],symbols:JSON.stringify(program.symbols)},before);
});

test("proof experiments use the ordinary goal-dependent binder resolver",async t=>{
  const source="def identity : forall A : U0. A -> A { intro A; intro x; exact x; }";
  const {session}=await setup(t,source,"intro A;");
  await query(session,"/prove { intro B; intro y; exact y; }","proof");
  await query(session,"/prove { intro B; intro y; exact tt; }","error");
  await query(session,"B","error");
  const extra=await session.run("/prove { intro B; intro y; exact y; } def escaped : Unit := tt;");
  assert.deepEqual(extra.map(result=>result.kind),["proof","error"]);
  await query(session,"escaped","error");
  assert.equal(session.accepted.length,0);
});

test("proof experiments can inspect shadowed evidence without making it available to hlevel",async t=>{
  const source=`import hlevels;
    def probe_(A : U0, p : Unit -> IsProp(U0, A)) : IsSet(U0, A and A) {
      let h : IsProp(U0, A) { exact p(tt); }
      let h := tt;
      hlevel with [p(tt)];
    }`;
  const {program,session}=await setup(t,source,"hlevel with [p(tt)];");
  const before={work:program.kernel.work(),definitions:[...program.kernel.definitions]};
  const locals=await query(session,"/locals","locals");
  assert.deepEqual(locals.bindings.filter(row=>row.label==="h").map(row=>[row.visible,row.type]),
    [[false,"IsProp(U0, A)"],[true,"Unit"]]);
  assert.match((await query(session,"/prove { hlevel; }","error")).text,/hlevel could not prove/);
  await query(session,"/prove { hlevel with [p(tt)]; }","proof");
  assert.equal(session.accepted.length,0);
  assert.deepEqual({work:program.kernel.work(),definitions:[...program.kernel.definitions]},before);
});

test("retained proof queries shadow evidence like the same authored block",async t=>{
  const prelude="import hlevels; theory T(U < UU0) { M : U; h : M; } ";
  const declaration=body=>`def probe_(A : U0, p : Unit -> IsProp(U0, A)) : IsSet(U0, A and A) { ${body} }`;
  const {session}=await setup(t,prelude+declaration("hlevel with [p(tt)];"),"hlevel with [p(tt)];");
  for(const shadow of ["", "let h := tt;", "obtain (h, other) := typed(Unit and Unit, (tt, tt));", "use T.make(Unit, tt);"]) {
    const body=`let h := p(tt); ${shadow} hlevel;`,source=prelude+declaration(body);
    for(const collectScopes of [false,true]) {
      const checked=await checkProgram(t,source,{module,options:{collectScopes}});
      try {
        assert.equal(checked.result.gaps.length,shadow?1:0,JSON.stringify(checked.result.gaps));
        if(shadow)assert.match(checked.result.gaps[0].reason,/hlevel could not prove/);
      } finally {checked.program.dispose();}
    }
    const result=await query(session,`/prove { ${body} }`,shadow?"error":"proof");
    if(shadow)assert.match(result.text,/hlevel could not prove/);
  }
  assert.equal(session.accepted.length,0);
});

test("scratch shadowing hides search evidence while preserving its inspected identity and explicit aliases",async t=>{
  const source=`import hlevels;
    def probe_(A : U0, p : Unit -> IsProp(U0, A)) : IsSet(U0, A and A) { hlevel with [p(tt)]; }`;
  const {session}=await setup(t,source,"hlevel with [p(tt)];");
  await query(session,"/prove { hlevel; }","error");
  await query(session,"let h := p(tt)","defined");
  await query(session,"/prove { hlevel; }","proof");
  await query(session,"let h := tt","defined");
  assert.match((await query(session,"/prove { hlevel; }","error")).text,/hlevel could not prove/);
  const locals=await query(session,"/locals","locals");
  assert.deepEqual(locals.bindings.filter(row=>row.label==="h").map(row=>[row.visible,row.type]),
    [[false,"IsProp(U0, A)"],[true,"Unit"]]);
  await query(session,"/prove { hlevel with [p(tt)]; }","proof");
  await query(session,"let h := p(tt)","defined");
  await query(session,"let saved := h","defined");
  await query(session,"let h := tt","defined");
  await query(session,"/prove { hlevel; }","proof");
  assert.equal(session.accepted.length,5);
});

test("proof introductions shadow retained let evidence without dropping an unshadowed proof",async t=>{
  const declaration=body=>`import hlevels;
    def probe_(A : U0, p : Unit -> IsProp(U0, A)) : Unit -> IsSet(U0, A and A) { ${body} }`;
  const {session}=await setup(t,declaration("intro x; hlevel with [p(tt)];"),"intro x;");
  for(const name of ["x","h"]) {
    const body=`let h := p(tt); intro ${name}; hlevel;`;
    const checked=await checkProgram(t,declaration(body),{module});
    assert.equal(checked.result.gaps.length,name==="h"?1:0,JSON.stringify(checked.result.gaps));
    await query(session,`/prove { ${body} }`,name==="h"?"error":"proof");
  }
});

test("expression contexts distinguish expected types from active proof goals",async t=>{
  const source=nat+"def f(k : Nat) : Nat := k;";
  const {session}=await setup(t,source,"k;",{phase:"expression",length:1});
  const result=await query(session,"/goal","goal");
  assert.equal(result.goal,null);
  assert.equal(result.expected,"Nat");
  assert.match((await query(session,"/prove { exact k; }","error")).text,/no active proof goal/);
  await query(session,"k","value");
});

test("inspection and ordinary print commands use the selected context",async t=>{
  const source=nat+"def f(k : Nat) : Nat { let next_ := succ(k); exact next_; }";
  const {session}=await setup(t,source,"exact next_;");
  const first=await query(session,"print(inspect(next_))","inspection");
  assert.ok(first.text.length);
  assert.equal((await query(session,"inspect next_","inspection")).text,first.text);
  assert.equal((await query(session,"print(typeof(next_))","type")).text,"Nat");
  assert.equal((await query(session,"print(evaluate(next_))","value")).text,"succ(k)");
  await query(session,"print(inspect(absent))","error");
  assert.equal(session.accepted.length,0);
  assert.match((await query(session,"/help","help")).text,/\/prove/);
  await query(session,"/unknown","error");
});

test("context inspection commands reject stale sessions",async t=>{
  const source="def f(x : Unit) : Unit := x;";
  const {program,session}=await setup(t,source,"x;",{phase:"expression",length:1});
  await program.check(source,"main");
  await query(session,"/locals","unavailable");
  await query(session,"/goal","unavailable");
});

test("witness readout keeps its closedness restriction in a local context",async t=>{
  const source="import nat; import h1_truncation; def f(k : Nat) : Nat := k;";
  const {session}=await setup(t,source,"k;",{phase:"expression",length:1});
  const closed=await query(session,"witness merely(U0, Nat, succ(zero))","value");
  assert.match(closed.text,/Nat/);
  await query(session,"witness merely(U0, Nat, k)","error");
  const printed=await query(session,"print(witness(merely(U0, Nat, succ(zero))))","value");
  assert.equal(printed.text,closed.text);
});

test("context queries retain published declarations with explicit logical assumptions",async t=>{
  const source="import truncation; def f(x : Unit) : Unit := x;";
  const {program,session}=await setup(t,source,"x;",{phase:"expression",length:1});
  const registry=program.compilationBindings,value=program.modules.get("truncation").get("Mere");
  assert.equal(value.tag,"App");
  const binding=registry.ofValue(value);
  assert.equal(binding.id,registry.declaration("truncation__Mere").binding.id);
  assert.equal(registry.ofValue(structuredClone(value)),null,"core equality confers no declaration identity");
  await query(session,"typeof Mere(Unit)","type");
  await query(session,"typeof merely(Unit, x)","type");
  await query(session,"witness merely(Unit, x)","error");
});
