import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {Worker} from "node:worker_threads";

async function workerFor(t) {
  const worker=new Worker(new URL("./fixtures/cubical-worker-harness.mjs",import.meta.url));
  t.after(()=>worker.terminate());
  const requests=new Map(),barriers=new Map(),replies=[];
  let serial=0,ready,failed;
  const started=new Promise((resolve,reject)=>{ready=resolve;failed=reject;});
  worker.on("message",message=>{
    if(message.ready)return ready();
    if(message.held)return barriers.get(message.held)?.();
    if(message.progress)return;
    replies.push(message.id);
    const {resolve,reject}=requests.get(message.id);
    requests.delete(message.id);
    if(message.error)reject(new Error(message.error.message));else resolve(message.result);
  });
  worker.on("error",error=>{failed(error);for(const {reject} of requests.values())reject(error);});
  await started;
  return {
    replies,
    request(command,args={}) {
      const id=++serial;
      const result=new Promise((resolve,reject)=>requests.set(id,{resolve,reject}));
      worker.postMessage({id,command,args});return result;
    },
    hold(module) {
      const entered=new Promise(resolve=>barriers.set(module,resolve));
      worker.postMessage({hold:module});return entered;
    },
    release:module=>worker.postMessage({release:module}),
  };
}

test("queued REPL requests and a recheck finish in submission order",{timeout:6000},async t=>{
  const worker=await workerFor(t);
  await worker.request("check",{source:"def base : Unit := tt;",module:"main"});
  const held=worker.hold("hlevels");
  const first=worker.request("repl",{input:"import hlevels;"});
  await held;
  const second=worker.request("repl",{input:"typeof tt;"});
  const check=worker.request("check",{source:"def latest : Unit := tt;",module:"main"});
  worker.release("hlevels");
  const [imported,typed,checked]=await Promise.all([first,second,check]);
  assert.equal(imported[0].kind,"info");
  assert.deepEqual(typed.map(({kind,text})=>({kind,text})),[{kind:"type",text:"Unit"}]);
  assert.deepEqual(checked.gaps,[]);
  assert.deepEqual(worker.replies,[1,2,3,4]);
});

test("an older check cannot overwrite a newer submitted source",{timeout:6000},async t=>{
  const worker=await workerFor(t),held=worker.hold("hlevels");
  const earlier=worker.request("check",{source:"import hlevels; def earlier : Unit := tt;",module:"main"});
  await held;
  const later=worker.request("check",{source:"def latest : Unit := tt;",module:"main"});
  // Let an incorrectly concurrent second check finish before the first one.
  const release=setTimeout(()=>worker.release("hlevels"),100);
  t.after(()=>clearTimeout(release));
  for(const result of await Promise.all([earlier,later]))assert.deepEqual(result.gaps,[]);
  const results=await worker.request("repl",{input:"typeof latest;"});
  assert.deepEqual(results.map(({kind,text})=>({kind,text})),[{kind:"type",text:"Unit"}]);
  assert.deepEqual(worker.replies,[1,2,3]);
});

test("worker contextual sessions use exact scope IDs and keep scratch histories separate",async t=>{
  const worker=await workerFor(t),source="def f(x : Unit) : Unit { exact x; }";
  await worker.request("check",{source,module:"main"});
  await assert.rejects(worker.request("contexts"),/contextual scopes enabled/);
  await worker.request("check",{source,module:"main",collectScopes:true});
  const listed=await worker.request("contexts"),points=listed.points.filter(point=>point.phase==="before"
    &&point.origin.start===source.indexOf("exact x;"));
  assert.equal(points.length,1);
  const [point]=points;
  assert.equal(point.revision,listed.revision);
  assert.ok(point.declarationId);
  assert.ok(listed.points.every(point=>!Object.hasOwn(point,"state")&&!Object.hasOwn(point,"lexical")));
  const first=await worker.request("context-open",{scope:point.id}),second=await worker.request("context-open",{scope:point.id});
  const run=(session,input)=>worker.request("context-run",{session:session.session,input});
  assert.equal((await run(first,"let scratch := x"))[0].kind,"defined");
  const [one,two]=await Promise.all([run(first,"scratch"),run(second,"scratch")]);
  assert.equal(one[0].kind,"value");
  assert.equal(two[0].kind,"error");
  assert.equal((await run(first,"/goal"))[0].goal,"Unit");
  assert.equal((await run(first,"/prove { exact scratch; }"))[0].kind,"proof");
  await worker.request("context-close",{session:first.session});
  await assert.rejects(run(first,"x"),/stale or closed/);
  assert.equal((await run(second,"x"))[0].kind,"value");
});

test("edits and failed rechecks revoke contextual sessions while preserving the module REPL",async t=>{
  const worker=await workerFor(t),source="def f(x : Unit) : Unit := x;";
  const checked=async()=>{
    await worker.request("check",{source,module:"main",collectScopes:true});
    const {points}=await worker.request("contexts");
    const selected=points.filter(point=>point.phase==="expression"&&point.origin.start===source.indexOf("x;"));
    assert.equal(selected.length,1);
    return {scope:selected[0].id,...await worker.request("context-open",{scope:selected[0].id})};
  };
  const first=await checked();
  await worker.request("context-invalidate");
  await assert.rejects(worker.request("context-run",{session:first.session,input:"x"}),/stale or closed/);
  await assert.rejects(worker.request("context-open",{scope:first.scope}),/completed source check/);
  assert.equal((await worker.request("repl",{input:"typeof f;"}))[0].kind,"type");
  const second=await checked();
  await assert.rejects(worker.request("check",{source:"def",module:"main",collectScopes:true}));
  await assert.rejects(worker.request("context-run",{session:second.session,input:"x"}),/stale or closed/);
  await assert.rejects(worker.request("context-open",{scope:second.scope}),/completed source check/);
  const third=await checked();
  assert.notEqual(third.scope,second.scope);
  await assert.rejects(worker.request("context-open",{scope:second.scope}),/completed source check/);
  assert.equal((await worker.request("context-run",{session:third.session,input:"x"}))[0].kind,"value");
});

test("an edit arriving during import loading cannot publish selectable old contexts",{timeout:6000},async t=>{
  const worker=await workerFor(t),held=worker.hold("hlevels");
  const check=worker.request("check",{source:"import hlevels; def f(x : Unit) : Unit := x;",module:"main",collectScopes:true});
  await held;
  // Revocation must be acknowledged while the check is still loading. A
  // queued acknowledgement would trip the UI's shorter control watchdog.
  await worker.request("context-invalidate");
  assert.deepEqual(worker.replies,[2]);
  worker.release("hlevels");
  assert.deepEqual((await check).gaps,[]);
  await assert.rejects(worker.request("contexts"),/contextual scopes enabled/);
});

test("generated declaration links and contextual summaries share binding identities",async t=>{
  const worker=await workerFor(t),source="theory T(U < UU0) { M : U; def get(x : M) : M := x; }";
  await worker.request("check",{source,module:"main",collectScopes:true});
  const generated=await worker.request("generation",{module:"main"}),{points}=await worker.request("contexts");
  const headers=generated.links.filter(link=>link.binding==="main__T.get"&&link.name==="T.get");
  assert.ok(headers.length);
  const selected=points.filter(point=>point.declarationId===headers[0].bindingId&&point.phase==="expression"
    &&point.origin.start===source.indexOf("x;"));
  assert.equal(selected.length,1);
  const {session}=await worker.request("context-open",{scope:selected[0].id});
  assert.equal((await worker.request("context-run",{session,input:"x"}))[0].text,"x");
});
