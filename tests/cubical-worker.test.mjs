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
