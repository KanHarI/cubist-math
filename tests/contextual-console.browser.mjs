import assert from "node:assert/strict";
import {spawn} from "node:child_process";
import {readFile} from "node:fs/promises";
import {chromium} from "playwright";
import {assertFreshBuild} from "../tools/build-stamp.mjs";
import {contextualScenarios} from "./fixtures/contextual-sessions.mjs";

assertFreshBuild();
const server=spawn("python3",["tools/serve.py","--port","0"],{stdio:["ignore","pipe","pipe"]});
server.stderr.resume();
let browser;
try {
  const port=await new Promise((resolve,reject)=>{
    let output="";
    const timer=setTimeout(()=>reject(new Error("Server did not start")),10000);
    server.once("error",reject);
    server.once("exit",code=>{clearTimeout(timer);reject(new Error(`Server exited ${code}`));});
    server.stdout.on("data",data=>{
      output+=data;
      const match=output.match(/127\.0\.0\.1:(\d+)\//);
      if(match){clearTimeout(timer);resolve(match[1]);}
    });
  });
  browser=await chromium.launch({headless:true});
  const page=await browser.newPage({viewport:{width:1280,height:1000}});
  const errors=[];page.on("pageerror",error=>errors.push(error.message));
  const idle=()=>page.waitForFunction(()=>!document.querySelector("#check").disabled&&document.querySelector("#check-loader").hidden);
  const open=async(source,embedded=false)=>{
    await page.goto("about:blank");
    await page.goto(`http://127.0.0.1:${port}/proof.html?example=1${embedded?"&embed=1":""}#source=${Buffer.from(source).toString("base64url")}`);
    if(embedded) {
      await page.waitForFunction(()=>document.querySelector("#check")?.disabled===false);
      await page.evaluate(source=>window.postMessage({type:"cubist-inspect",source,offset:source.indexOf("ih(m.1)")},location.origin),source);
      await page.waitForFunction(()=>document.querySelector("#inspect-name")?.textContent==="ih");
    }
    await idle();
  };
  const collect=async()=>{await page.locator("#collect-contexts").check();await idle();};
  const chooseLine=async(text,generated=false)=>{
    const row=page.locator(`${generated?"#generated-source":"#read-source"} .source-line`).filter({hasText:text});
    await row.locator(".context-entry").click();
    assert.equal(await page.locator("#context-instance").inputValue(),"","opening a line never chooses an arbitrary instance");
    assert.equal(await page.locator("#context-panel fieldset").evaluate(node=>node.disabled),true);
  };
  const options=()=>page.locator("#context-instance option").evaluateAll(nodes=>nodes.filter(node=>node.value).map(node=>({id:node.value,text:node.textContent})));
  const select=async id=>{
    await page.locator("#context-instance").selectOption(id);
    await page.waitForFunction(()=>!document.querySelector("#context-panel fieldset").disabled);
  };
  const enter=async(input,kind,pattern,root="#context-panel")=>{
    const form=page.locator(`${root} .repl-form`),results=page.locator(`${root} .repl-result`);
    const count=await results.count();
    await form.locator("textarea").fill(input);
    await form.locator(".repl-run").click();
    await page.waitForFunction(({root,count})=>document.querySelectorAll(`${root} .repl-result`).length>count
      &&!document.querySelector(`${root} .repl-form`).classList.contains("busy"),{root,count});
    const result=results.last();
    assert.match(await result.getAttribute("class"),new RegExp(`repl-${kind}\\b`));
    const text=await result.textContent();
    if(pattern)assert.match(text,pattern);
    return text;
  };
  const source=`inductive Nat { zero; succ(n : Nat); }
def f(k : Nat) : Nat {
  let next_ := succ(k);
  exact next_;
}`;
  await open(source);
  assert.equal(await page.locator(".context-entry").count(),0,"collection is opt-in");
  await collect();
  await chooseLine("exact next_;");
  const before=(await options()).filter(option=>option.text.includes("Before statement"));
  assert.equal(before.length,1);
  await select(before[0].id);
  await enter("/locals","locals",/next_ : Nat := succ\(k\)/);
  await enter("/goal","goal",/Nat/);
  await enter("let scratch := next_;","defined",/scratch : Nat/);
  await enter("/prove { exact scratch; }","proof",/Checked against Nat/);
  await enter("typeof scratch;","type",/^Nat$/);
  await enter("typeof scratch;","error",/scratch/,"#repl");
  await page.locator("#context-panel .repl-restart").click();
  await page.waitForFunction(()=>document.querySelector("#context-panel .repl-log").textContent.includes("Started a new session"));
  await enter("scratch;","error",/scratch/);
  await enter("next_;","value",/^succ\(k\)$/);
  await page.locator("#context-panel .context-close").click();
  assert.equal(await page.locator("#context-panel").isVisible(),false);
  await chooseLine("exact next_;");await select(before[0].id);
  await enter("scratch;","error",/scratch/);

  // Editing revokes the live context even though the last checked source is
  // still on display. A failed recheck must never revive its scope IDs.
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("def");
  assert.equal(await page.locator("#context-panel fieldset").evaluate(node=>node.disabled),true);
  assert.match(await page.locator("#context-status").textContent(),/stale/);
  await idle();await page.locator("#check").click();await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(),true);
  assert.equal(await page.locator("#context-panel fieldset").evaluate(node=>node.disabled),true);
  await page.locator("#editor").fill(source);await idle();await page.locator("#check").click();await idle();
  await chooseLine("exact next_;");
  const checked=(await options()).filter(option=>option.text.includes("Before statement"));
  assert.notEqual(checked[0].id,before[0].id);
  await select(checked[0].id);await enter("next_;","value",/^succ\(k\)$/);
  console.log("PASS contextual source console, explicit selection, proof experiments, scratch isolation and edit/recheck lifecycle");

  const branches=contextualScenarios.find(item=>item.id==="branch-instance-set");
  await open(branches.source);await collect();await chooseLine("def both");
  const instances=(await options()).filter(option=>/ · zero · instance \d of 2$/.test(option.text));
  assert.equal(instances.length,2,JSON.stringify(await options()));
  const refinements=[],verdicts=[];
  for(const instance of instances) {
    await select(instance.id);
    refinements.push(await enter("/locals","locals"));
    // Check the selected instance, not a conjunction over the written body.
    const form=page.locator("#context-panel .repl-form");
    await form.locator("textarea").fill("typed(a = zero, refl(a));");
    await form.locator(".repl-run").click();
    await page.waitForFunction(()=>!document.querySelector("#context-panel .repl-form").classList.contains("busy"));
    verdicts.push(await page.locator("#context-panel .repl-result").last().getAttribute("class"));
  }
  assert.notEqual(refinements[0],refinements[1]);
  assert.deepEqual(verdicts.sort(),["repl-result repl-error","repl-result repl-value"]);
  console.log("PASS overlapping wildcard instances expose distinct refinements and query results");

  await open(`theory T(U < UU0) { M : U; def get(x : M) : M := x; }
def copied(x : Unit) : Unit := x;`);
  await collect();await page.locator("#generated-mode").click();await idle();
  await chooseLine("def T.get",true);
  const helperOptions=await options();
  assert.equal(new Set(helperOptions.map(option=>option.text)).size,helperOptions.length,"distinct instances have distinct labels");
  const helper=helperOptions.filter(option=>option.text.includes(" · Expression · ")&&option.text.endsWith(" · x"));
  assert.equal(helper.length,1,JSON.stringify(await options()));
  assert.match(helper[0].text,/T\.get/);
  await select(helper[0].id);await enter("x;","value",/^x$/);
  await chooseLine("def copied",true);
  const copied=(await options()).filter(option=>option.text.endsWith(" · x"));
  assert.equal(copied.length,1);
  await select(copied[0].id);await enter("typeof x;","type",/^Unit$/);
  console.log("PASS generated declaration binding IDs and copied source context ranges");

  // Replacing a worker revokes capabilities without sending a close request
  // to a terminated worker or leaving its watchdog in the new request map.
  await page.route("**/cubist-version",route=>route.fulfill({json:{version:"contextual-browser-replacement"}}));
  await page.locator("#check").click();await idle();
  assert.match(await page.locator("#source-notice").textContent(),/compiler was updated/);
  assert.equal(await page.locator("#context-panel fieldset").evaluate(node=>node.disabled),true);
  await chooseLine("def copied",true);
  const replaced=(await options()).filter(option=>option.text.endsWith(" · x"));
  assert.notEqual(replaced[0].id,copied[0].id);
  await select(replaced[0].id);await enter("typeof x;","type",/^Unit$/);
  console.log("PASS compiler replacement revokes the old console and leaves the new worker usable");
  await page.setViewportSize({width:420,height:900});
  const width=await page.locator("#context-panel").evaluate(node=>node.getBoundingClientRect().width);
  assert.ok(width<=420,"the contextual console fits a narrow viewport");
  if(process.env.CUBIST_CONTEXT_SCREENSHOT)await page.locator("#context-panel").screenshot({path:process.env.CUBIST_CONTEXT_SCREENSHOT});

  // Control delivery explicitly: a real worker's synchronous checker cannot
  // reliably be paused between a browser edit and a returning message.
  const lifecycle=await page.evaluate(async()=>{
    const {createContextualConsole}=await import("./contextual-console.mjs");
    const panel=document.querySelector("#context-panel").cloneNode(true);
    panel.removeAttribute("id");document.body.append(panel);
    const target=document.createElement("div");document.body.append(target);
    const row=()=>{const node=document.createElement("div");node.className="source-line";target.replaceChildren(node);};
    const pending=[],closed=[],listed=["a","b"].map(id=>({id,origin:{module:"main",start:0,end:1},
      phase:"expression",declaration:"f",declarationId:"f",available:true}));
    let holdIndex=false;
    const request=(command,args)=>{
      if(command==="context-close"){closed.push(args.session);return Promise.resolve();}
      if(command==="contexts"&&!holdIndex)return Promise.resolve({points:listed});
      return new Promise((resolve,reject)=>pending.push({command,args,resolve,reject}));
    };
    const controller=createContextualConsole(panel,{request}),snapshot={sources:{main:"x"}},view={source:"x"};
    const picker=panel.querySelector("select"),controls=panel.querySelector("fieldset");
    const flush=()=>new Promise(resolve=>setTimeout(resolve,0));
    const change=id=>{picker.value=id;picker.dispatchEvent(new Event("change"));};
    const check=()=>{const token=controller.invalidate();controller.checked(snapshot,token,true);};
    const decorate=async()=>{row();await controller.decorate(target,view,{module:"main"});};
    check();await decorate();target.querySelector("button").click();
    change("a");change("b");
    const [first,second]=pending.splice(0);
    second.resolve({session:"second"});await flush();
    const openedStatus=panel.querySelector("[role=status]").textContent;
    first.reject(new Error("Late opening error"));await flush();
    const lateOpenIgnored=!controls.disabled&&panel.querySelector("[role=status]").textContent===openedStatus;
    panel.querySelector("textarea").value="x;";
    panel.querySelector("form").dispatchEvent(new Event("submit",{cancelable:true}));
    await flush();
    const [query]=pending.splice(0);
    controller.invalidate();
    query.resolve([{kind:"value",text:"STALE VALUE"}]);await flush();
    const lateQueryIgnored=controls.disabled&&!panel.querySelector(".repl-log").textContent.includes("STALE VALUE");

    check();await decorate();target.querySelector("button").click();change("b");
    pending.shift().resolve({session:"third"});await flush();
    panel.querySelector(".repl-restart").click();await flush();
    const restarting=panel.querySelector("form").classList.contains("busy")&&panel.querySelector(".repl-run").disabled;
    const [restart]=pending.splice(0);
    controller.invalidate();restart.reject(new Error("Restart was revoked"));await flush();
    const failedRestartHandled=controls.disabled&&panel.querySelector(".repl-error").textContent==="Restart was revoked";

    check();holdIndex=true;row();
    const oldIndex=controller.decorate(target,view,{module:"main"});
    const [index]=pending.splice(0);
    check();holdIndex=false;await decorate();
    index.reject(new Error("Late index error"));await oldIndex;
    const lateIndexIgnored=!target.querySelector("button").disabled;

    check();holdIndex=true;
    let inspected=true;
    const oldInspection=controller.openInspection({module:"main",scope:"a"},()=>inspected);
    const [inspectionIndex]=pending.splice(0);inspected=false;
    inspectionIndex.resolve({points:listed});await oldInspection;
    const changedInspectionIgnored=controls.disabled&&pending.length===0;
    check();holdIndex=false;inspected=true;
    const openingInspection=controller.openInspection({module:"main",scope:"b"},()=>inspected);
    await flush();const [inspectionOpen]=pending.splice(0);inspected=false;
    inspectionOpen.resolve({session:"old-inspection"});await openingInspection;
    const changedInspectionClosed=controls.disabled&&closed.includes("old-inspection");
    panel.remove();target.remove();
    return {lateOpenIgnored,lateQueryIgnored,restarting,failedRestartHandled,lateIndexIgnored,changedInspectionIgnored,changedInspectionClosed};
  });
  for(const [name,passed] of Object.entries(lifecycle))assert.equal(passed,true,name);
  console.log("PASS delayed opening/query/index responses and revoked restart remain isolated");

  await open(`import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M; }
initial N : T(U0);`);
  await collect();await page.locator("#generated-mode").click();await idle();
  await chooseLine("inductive N",true);
  const constructorContexts=await options();
  assert.equal(constructorContexts.length,2);
  const constructorResults=[];
  for(const point of constructorContexts) {
    await select(point.id);
    const text=await enter("typeof N.c;","(?:type|error)");
    constructorResults.push([await page.locator("#context-panel .repl-result").last().getAttribute("class"),text]);
  }
  assert.deepEqual(constructorResults.map(([kind])=>kind).sort(),["repl-result repl-error","repl-result repl-type"],
    "the header cannot see constructors; the later constructor scope can see the earlier one");
  assert.equal(constructorResults.find(([kind])=>kind.endsWith("repl-type"))[1],"N");
  console.log("PASS generated inductive contexts distinguish the header from earlier constructor availability");

  await page.unroute("**/cubist-version");
  const tree=(await readFile(new URL("../library/universe_smallness.cubist",import.meta.url),"utf8"))
    .split("// No small family")[0].replace("import contractible_maps;","");
  for(const embedded of [false,true]) {
    await open(tree,embedded);
    assert.equal(await page.locator("#collect-contexts").isChecked(),false);
    if(!embedded)await page.locator('#read-source button[data-name="ih"]').last().click();
    const button=page.getByRole("button",{name:"Open REPL in this context",exact:true});
    await button.waitFor({state:"visible"});await idle();
    assert.equal(await page.locator('#kernel-context-list .kernel-context-row[data-name="m"]').count(),1);
    await button.click();
    await page.waitForFunction(()=>!document.querySelector("#context-panel fieldset").disabled);
    assert.equal(await page.locator("#inspect-name").textContent(),"ih","collection preserves the inspected occurrence");
    assert.equal(await page.locator("#collect-contexts").isChecked(),true);
    assert.equal((await options()).length,1,"inspection opens its exact instance directly");
    await enter("typeof ih;","type",/member/);
    await enter("typeof m;","type",/children/);
    await enter("let saved := ih;","defined",/saved/);
    await enter("typeof saved;","type",/member/);
    await page.locator('#read-source button[data-name="ih"]').first().click();await idle();
    assert.equal(await page.locator('#kernel-context-list .kernel-context-row[data-name="m"]').count(),0);
    await button.click();
    await page.waitForFunction(()=>!document.querySelector("#context-panel fieldset").disabled);
    await enter("typeof m;","error",/m/);
    await enter("typeof saved;","error",/saved/);
    if(!embedded) {
      await page.locator("#edit-mode").click();await page.locator("#editor").fill(tree+"\n// edited");
      assert.equal(await button.isDisabled(),true);
      assert.equal(await page.locator("#context-panel fieldset").evaluate(node=>node.disabled),true);
    }
  }
  console.log("PASS inspector opens exact induction-hypothesis contexts on demand, including embedded views and dirty-source invalidation");
  assert.deepEqual(errors,[]);
} finally {
  await browser?.close();server.kill();
}
