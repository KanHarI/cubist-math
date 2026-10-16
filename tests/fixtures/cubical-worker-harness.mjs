// Run the browser worker unchanged in a Node worker, with an import barrier
// controlled by the test. Requests and responses cross a real worker boundary.
import "../fresh-build.mjs";
import {parentPort} from "node:worker_threads";
import {readFile} from "node:fs/promises";
const held=new Map();
globalThis.self={postMessage:message=>parentPort.postMessage(message)};
globalThis.fetch=async url=>{
  const file=new URL(url),module=file.pathname.split("/").at(-1).replace(/\.cubist$/,"");
  if(held.has(module)) {
    const released=new Promise(resolve=>held.set(module,resolve));
    parentPort.postMessage({held:module});
    await released;
  }
  file.pathname=file.pathname.replace(/\/web\/(library|archive|cubist-tests)\//,"/$1/");
  try {const text=await readFile(file,"utf8");return {ok:true,text:async()=>text};}
  catch(error) {if(error.code!=="ENOENT")throw error;return {ok:false,status:404};}
};
parentPort.on("message",message=>{
  if(message.hold)held.set(message.hold,null);
  else if(message.release) {held.get(message.release)?.();held.delete(message.release);}
  else self.onmessage({data:message});
});
await import("../../web/cubical-worker.mjs");
