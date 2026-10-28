import { browserTest } from "./browser-test.mjs";
// Exercise the published static artifact (or a live URL), without serve.py's
// development-only import rewriting and version endpoint.
import assert from "node:assert/strict";

await browserTest(async ({ browser, base }) => {
  if (!base.endsWith("/")) base += "/";
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  page.setDefaultTimeout(180000);
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  page.on("response", response => {
    if (response.status() >= 400 && new URL(response.url()).origin === new URL(base).origin)
      errors.push(`${response.status()} ${response.url()}`);
  });
  assert.equal((await page.goto(base)).status(), 200);
  assert.match(await page.title(), /Proof highlights/);
  assert.equal(await page.getByRole("link", { name: "GitHub repository", exact: true }).getAttribute("href"), "https://github.com/KanHarI/cubist-math");
  assert.equal(await page.locator(".proof-card").count(), 10);
  for (const width of [1440, 390, 320]) {
    await page.setViewportSize({ width, height: 900 });
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth > innerWidth), false);
  }
  await page.setViewportSize({ width: 1440, height: 1000 });
  const version = await page.request.get(new URL("cubist-version", base).href);
  assert.equal(version.status(), 200);
  assert.match((await version.json()).version, /^[a-f0-9]{64}$/);
  console.log("PASS static landing, repository link, mobile layout, build version");
  const contracts=await page.evaluate(async()=>{
    const {benchmark}=await import("./benchmark-runner.mjs");
    return benchmark({area:"tests",modules:["contracts","absent"],limitMs:10000,readSource:async name=>name==="contracts"?`
# test(expected) # expect_error(E606) def expected : Void := tt;
# test(broken_contract) # expect_error(E343) def unexpected : Void := tt;`:null});
  });
  assert.deepEqual(contracts.declarations.map(row=>row.category),["intended","failed"]);
  await page.route("**/benchmark-results-tests.json",route=>route.fulfill({json:{...contracts,complete:true}}));
  await page.goto(new URL("benchmark.html?area=tests",base).href);
  await page.waitForFunction(()=>document.querySelector("#status")?.textContent.includes("1 test contract failures"));
  assert.match(await page.locator("#comparison").textContent(),/broken_contract/);
  assert.match(await page.locator("#status").textContent(),/1 import failures/);
  assert.match(await page.locator("#comparison").textContent(),/Imports: absent:/);
  assert.match(await page.locator("#entries").textContent(),/Expected failure:/);
  await page.unroute("**/benchmark-results-tests.json");
  console.log("PASS static benchmark shares test contracts and displays contract failures");
  for (const [proof, name, backend] of [["euclid", "euclid", "cubical"], ["cubical_paths", "reverse_twice", "cubical"], ["f4_galois_correspondence", "f4_galois_correspondence", "cubical"]]) {
    await page.goto(new URL(`proof.html?proof=${proof}&name=${name}&backend=${backend}`, base).href);
    await page.waitForFunction(() => document.querySelector("#check")?.disabled === false && document.querySelector("#check-loader")?.hidden);
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.equal(await page.locator("#inspect-name").textContent(), name);
    await page.waitForFunction(() => document.querySelector("#kernel-view")?.disabled === false);
    assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /unavailable/);
    if (proof === "euclid") {
      // A line number shows the goal at that proof statement and the names in scope.
      await page.locator('.source-line[data-line="10"] .line-number').click();
      assert.equal(await page.locator("#inspect-name").textContent(), "Goal at line 10");
      assert.match(await page.locator("#inspect-type").textContent(), /exists p : UNat\. Prime\(p\) and n < p/);
      assert.match(await page.locator("#locals").textContent(), /n\s*UNat/);
    }
    console.log(`PASS static worker, WASM, checking and folded inspection: ${proof} (${backend})`);
  }
  // Reference examples are checked in the browser; a linked name opens the
  // workspace's kernel inspector for it.
  await page.goto(new URL("reference/types.html", base).href);
  await page.waitForSelector("#values .example-token");
  await page.locator("#values .example-token", { hasText: "seven" }).first().click();
  const inspector = page.frameLocator(".inspector-drawer iframe");
  await inspector.locator("#inspect-name").filter({ hasText: /^seven$/ }).waitFor();
  await inspector.locator("#kernel-view:not([disabled])").waitFor();
  assert.equal((await inspector.locator("#kernel-expression").textContent()).trim(), "7");
  assert.equal((await inspector.locator("#kernel-type").textContent()).trim(), "UNat");
  await page.locator("#tour-numbers").scrollIntoViewIfNeeded();
  await page.waitForSelector("#tour-numbers .example-token");
  assert.match(await page.locator("#tour-numbers .example-bar span").first().textContent(), /evaluate at line 8: 6/);
  // An imported module's name opens the module in the workspace.
  const moduleLink = page.locator("#tour-numbers a.example-module").first();
  assert.equal(await moduleLink.textContent(), "unat");
  assert.match(await moduleLink.getAttribute("href"), /proof\.html\?proof=unat$/);
  // 0 is the constructor itself, not notation.
  assert.deepEqual(await page.locator("#tour-numbers pre code").first().evaluate(code =>
    [...code.querySelectorAll("*")].filter(node => node.textContent === "0").map(node => node.classList.contains("macro"))), [false]);
  // A numeral's expansion shows at once on hover.
  await page.locator('#tour-numbers [data-tip*="succ("]').first().hover();
  assert.match(await page.locator(".token-tip:not([hidden])").textContent(), /^\d+ expands to succ\(/);
  assert.match(await page.locator(".drawer-head a").getAttribute("href"), /proof\.html\?example=1#source=/);
  console.log("PASS reference examples: in-browser checking, linked names, embedded kernel inspector, evaluate results, instant macro tips");
  // An excerpt is checked with the module it quotes: its names open the
  // inspector, and its workspace link opens that module at the declaration.
  await page.goto(new URL("reference/induction.html", base).href);
  // The first of unat's excerpts is its declaration of UNat.
  const excerpt = page.locator('pre > code[data-check="excerpt"][data-module="unat"]').first();
  const excerptBar = excerpt.locator("xpath=../following-sibling::div[contains(@class, 'example-bar')][1]");
  await excerpt.scrollIntoViewIfNeeded();
  await excerpt.locator(".example-token", { hasText: /^UNat$/ }).first().waitFor();
  assert.match(await excerptBar.locator("span").textContent(), /^Quoted from unat · Click a name/);
  assert.match(await excerptBar.locator("a").getAttribute("href"), /proof\.html\?proof=unat&name=UNat$/);
  await excerpt.locator(".example-token", { hasText: /^UNat$/ }).first().click();
  await inspector.locator("#inspect-name").filter({ hasText: /^UNat$/ }).waitFor();
  assert.deepEqual(await inspector.locator("#inspect-constructors li code").allTextContents(), ["zero : UNat", "succ : UNat -> UNat"]);
  assert.match(await page.locator(".drawer-head a").getAttribute("href"), /proof\.html\?proof=unat&name=UNat$/);
  console.log("PASS reference excerpts: checked with their module, linked names, the module's workspace link");
  // A print is reported with the assumptions its term relies on (#317's
  // review round 2, finding 4).
  await page.goto(new URL("reference/assumptions.html", base).href);
  const printed = page.locator('pre > code[data-check="accept"]', { hasText: "print(inspect(LEM(U0)));" });
  await printed.scrollIntoViewIfNeeded();
  const printedBar = printed.locator("xpath=../following-sibling::div[contains(@class, 'example-bar')][1]").locator("span").first();
  await printedBar.filter({ hasText: "print inspect" }).waitFor();
  assert.match(await printedBar.textContent(), /print inspect at line 3: LEM\(U0\), assumes LEM$/);
  console.log("PASS reference prints: each with the assumptions its term relies on");
  // The reference's REPL bar opens and closes.
  const dockToggle = page.locator(".repl-dock-toggle");
  await dockToggle.click();
  assert.equal(await page.locator(".repl-dock-body").isVisible(), true);
  await dockToggle.click();
  assert.equal(await page.locator(".repl-dock-body").isVisible(), false);
  // Enter each REPL entry and wait for its results.
  const enter = async text => {
    const input = page.locator(".repl-text").last();
    await input.fill(text);
    await input.press("Enter");
    await page.waitForFunction(() => !document.querySelector(".repl-form.busy"));
  };
  const lastResults = async count => (await page.locator(".repl-log").last().locator(".repl-result").allTextContents()).slice(-count);
  // Any checked example opens in the REPL bar, which shows what it defines.
  // Examples are found by their source, and enhanced once scrolled near.
  const seven = (tab = page) => tab.locator("#values pre", { hasText: "def seven := 7;" });
  const sevenBar = (tab = page) => seven(tab).locator("xpath=following-sibling::div[contains(@class, 'example-bar')][1]");
  await page.goto(new URL("reference/types.html", base).href);
  await seven().scrollIntoViewIfNeeded();
  await sevenBar().locator(".repl-fork").click();
  await page.waitForFunction(() => [...document.querySelectorAll(".repl-dock .repl-result")].some(line => line.textContent === "seven : UNat"));
  await enter("evaluate seven");
  assert.deepEqual(await lastResults(1), ["7"]);
  console.log("PASS examples open in the REPL bar with their definitions");
  // A read-only REPL transcript forks into the REPL bar, with the example
  // before it loaded, and can be continued there.
  await page.goto(new URL("reference/first-proof.html", base).href);
  await page.locator("pre.repl-transcript", { hasText: "evaluate !!lt_succ;" })
    .locator("xpath=following-sibling::div[contains(@class, 'example-bar')][1]").locator(".repl-fork").click();
  await page.waitForFunction(() => document.querySelectorAll(".repl-dock .repl-result").length >= 4 && !document.querySelector(".repl-form.busy"));
  await enter("evaluate !!exists_greater_number(10)");
  assert.deepEqual(await lastResults(2), ["(6, 0, refl(6))", "(11, 0, refl(11))"]);
  console.log("PASS read-only REPL transcripts fork into the REPL bar");
  await page.goto(new URL("proof.html?proof=unat", base).href);
  await page.locator("#read-source .reference").first().waitFor();
  assert.equal(await page.locator("#proof-title").textContent(), "Library: unat");
  assert.equal(await page.locator("#archive-note").isHidden(), true);
  // The console under a proof has the proof's names loaded.
  await enter("typeof unat_add_comm;");
  await enter("let y := add(2, 3);");
  await enter("y");
  assert.deepEqual(await lastResults(3), ["forall x : UNat. forall y : UNat. x + y = y + x", "y : UNat", "5"]);
  console.log("PASS library module in the workspace, with its console");
  // Every link to an axiom shows its definition's source: the axioms a
  // result relies on, and the inspector's axiom lists (#317's review round
  // 6, finding 3).
  await page.goto(new URL("proof.html?proof=h1_classical", base).href);
  const axiomSource = async button => {
    await button.click();
    await page.locator("#inspect-name").filter({ hasText: /^LEM$/ }).waitFor();
    await page.locator("#view-source:not([hidden])").waitFor();
    assert.match(await page.locator("#view-source").getAttribute("href"), /^proof\.html\?proof=classical_axioms&name=LEM&offset=\d+$/);
  };
  await axiomSource(page.locator("#result .axiom-dependencies button", { hasText: /^LEM$/ }).first());
  const userOfLEM = page.locator("#result > div", { has: page.locator(".axiom-dependencies button", { hasText: /^LEM$/ }) }).first().locator("button").first();
  for (const list of ["#inspect-axioms", "#kernel-axioms-list"]) {
    await userOfLEM.click();
    await page.locator(`${list} button`, { hasText: /^LEM$/ }).waitFor();
    await axiomSource(page.locator(`${list} button`, { hasText: /^LEM$/ }));
  }
  console.log("PASS axiom links show their definitions' source");
  await page.goto(new URL("repl.html", base).href);
  for (const text of ["import unat;", "use unat;", "let x := 7;", "typeof x;", "evaluate x;", "def wrong : x = 8 {\n  exact refl(7);\n}"]) await enter(text);
  assert.deepEqual(await lastResults(4), ["x : UNat", "UNat", "7", "E606: Type mismatch: found 7 = 7, expected x = 8."]);
  console.log("PASS REPL page: let, typeof, evaluate, rejected entries");
  // The worker's runtime shows a value form where the kernel's head queries
  // stop (K344), and a stop at its limits leaves the session usable.
  for (const text of ["def count_into(n, total : UNat) : UNat := match n {\n  zero => total;\n  succ(k) => count_into(k, succ(total));\n};",
    "evaluate count_into(2 * 255, 0);", "evaluate count_into(100 * 100 * 100, 0);", "evaluate x + 1;"]) await enter(text);
  assert.deepEqual(await lastResults(3), ["510", "E488: The runtime's evaluation of the value form exhausted its allocation budget of 20,000,000 cells.", "8"]);
  console.log("PASS REPL page: the runtime's value forms and its limits");
  // Nested eliminators: past the kernel's recursion guard (ck_enter, 448
  // steps) a path judgement fails with K336, as often as asked, before the
  // worker's own engine stack runs out at 622 levels; the worker goes on.
  for (const text of ["inductive Lamp { dark; lit; }", "def toggle(f : Lamp) : Lamp := match f { dark => lit; lit => dark; };",
    "def parity(n : UNat) : Lamp := match n { zero => dark; succ(m) => toggle(parity(m)); };",
    "def deep : parity(2 * 200) = dark := refl(dark);",
    ...[1, 2, 3, 4].map(i => `def past_${i} : parity(10 * 200) = dark := refl(dark);`),
    "def after : toggle(dark) = lit := refl(lit);"]) await enter(text);
  assert.deepEqual(await lastResults(6), ["deep : parity(2 * 200) = dark",
    ...Array(4).fill("K336: Native reduction recursion depth exceeded."), "after : toggle(dark) = lit"]);
  console.log("PASS REPL page: the kernel's recursion guard in the worker, and the worker after it");
  // A kernel instance that fails, as when the engine's own stack runs out
  // inside it, is never entered again: its worker answers the request with
  // the failure, marked fatal, and stops, failing every request it held.
  // The page starts a new worker and builds again what it holds: a REPL
  // restores its session, the proof page checks its source again.
  const injected = await browser.newContext();
  // The runtime's snapshot arms its worker's kernel to fail, if its plan says.
  await injected.route("**/cubical-runtime.mjs*", async route => {
    const response = await route.fetch(), body = await response.text();
    const edited = body.replace("function snapshot(kernel, judgement, budget) {", "$& globalThis.armKernelFault?.();");
    assert.notEqual(edited, body);
    await route.fulfill({ response, body: edited });
  });
  // Each worker loads the kernel anew, and fails as the next plan says, with
  // the engine's RangeError out of an export: at the first export a runtime
  // value form's snapshot calls ("snapshot"), at the first folded normal
  // form ("normal"), in the first inspection ("inspection"), or only on
  // demand: a message the worker does not know arms the next kernel call,
  // the next `_cb_free` (with a trap), or the next call made while a check's
  // steps are read, and a REPL entry /fail-next-kernel-call arms the next
  // kernel call. "unavailable" fails the kernel's load. Each load is
  // announced (`kernelAsked`), and held up while `kernelHeld` is pending.
  const plans = [];
  let kernelHeld = null, kernelAsked = () => {};
  await injected.route("**/dist/cubical.mjs*", async route => {
    const plan = plans.shift() ?? "on demand";
    kernelAsked();
    if (kernelHeld) await kernelHeld;
    if (plan === "unavailable") return route.abort();
    const response = await route.fetch(), body = await response.text();
    assert.match(body, /export default Module;\s*$/);
    await route.fulfill({ response, body: body.replace(/export default Module;\s*$/, `const plan = ${JSON.stringify(plan)};
let armed = false, freeing = false, inSteps = false, snapshots = 0, normals = 0, inspections = 0;
globalThis.armKernelFault = () => { if (plan === "snapshot" && !snapshots++) armed = true; };
self.addEventListener("message", ({ data }) => {
  if (data?.command === "fail-next-kernel-call" || data?.command === "repl" && data.args?.input === "/fail-next-kernel-call"
    || plan === "inspection" && data?.command === "inspect" && !inspections++) armed = true;
  if (data?.command === "fail-next-free") freeing = true;
  if (data?.command === "fail-in-steps") inSteps = true;
});
const overflow = () => { throw new RangeError("Maximum call stack size exceeded"); };
const readingSteps = () => {
  const limit = Error.stackTraceLimit;
  Error.stackTraceLimit = 200;
  try { return new Error().stack.includes("get steps"); } finally { Error.stackTraceLimit = limit; }
};
export default async options => {
  const module = await Module(options);
  for (const name of Object.keys(module).filter(name => name.startsWith("_cb_"))) {
    const call = module[name];
    module[name] = (...args) => {
      if (armed) { armed = false; overflow(); }
      if (freeing && name === "_cb_free") { freeing = false; throw new WebAssembly.RuntimeError("unreachable"); }
      if (inSteps && readingSteps()) { inSteps = false; overflow(); }
      if (plan === "normal" && name === "_cb_normalize_folded" && !normals++) overflow();
      return call(...args);
    };
  }
  return module;
};`) });
  });
  // The lists module, served as the test says: a stand-in, held up while
  // `listsHeld` is pending, and each request for it announced.
  let lists = "def h : Unit := tt;\n", listsHeld = null, listsAsked = () => {};
  await injected.route("**/lists.cubist*", async route => {
    listsAsked();
    if (listsHeld) await listsHeld;
    await route.fulfill({ body: lists, contentType: "text/plain" });
  });
  const fault = "E668: The kernel's WebAssembly instance failed (Maximum call stack size exceeded), and is not used again: nothing computed after the failure is kept.";
  const restarted = [fault, "The kernel was restarted. The session's entries were checked again."];
  const entries = async (target, texts) => {
    for (const text of texts) {
      await target.locator(".repl-text").last().fill(text);
      await target.locator(".repl-text").last().press("Enter");
      await target.waitForFunction(() => !document.querySelector(".repl-form.busy"));
    }
    return target.locator(".repl-log").last().locator(".repl-result").allTextContents();
  };
  // The REPL page: its first worker fails in a value form's snapshot, its
  // second in a folded normal form. Each time the session is restored on a
  // new worker, each statement that extended it as the entry it was: the
  // query typeof tt was entry repl_3, so repl_5, which names repl_4, still
  // finds it.
  plans.push("snapshot", "normal");
  const faulty = await injected.newPage();
  await faulty.goto(new URL("repl.html", base).href);
  assert.deepEqual((await entries(faulty, ["import unat;", "use unat;", "typeof tt;", "let x := 7;", "let saved := repl_4::x;",
    "evaluate x + 1;", "evaluate !!x;", "evaluate x + 1;", "typeof x;", "typeof saved;"])).slice(-7),
    [...restarted, ...restarted, "8", "UNat", "UNat"]);
  // A new worker that cannot load answers too, and the console is free.
  plans.push("snapshot", "unavailable");
  const stranded = await injected.newPage();
  await stranded.goto(new URL("repl.html", base).href);
  assert.deepEqual((await entries(stranded, ["import unat;", "use unat;", "evaluate 1 + 1;"])).slice(-3), [fault,
    "E227: Unable to load the checking worker. Build with make wasm.",
    "The kernel was restarted. The session's entries could not be checked again, and what they defined is gone."]);
  await stranded.close();
  console.log("PASS REPL page: a failed kernel stops its worker; a new one restores the session, under its entries' names");
  // Workers driven by their messages: every request a failure ends is
  // answered, fatal, and nothing is left waiting.
  await faulty.evaluate(() => {
    const workers = new Map();
    window.startWorker = async name => {
      const worker = new Worker(new URL("cubical-worker.mjs", location.href), { type: "module" });
      const replies = new Map();
      let serial = 0, started;
      const ready = new Promise(resolve => { started = resolve; });
      worker.onmessage = ({ data }) => { if (data.ready) started(); else if (data.progress === undefined) replies.get(data.id)?.(data); };
      await ready;
      workers.set(name, (command, args = {}) => Promise.race([
        new Promise(resolve => { const id = ++serial; replies.set(id, resolve); worker.postMessage({ id, command, args }); }),
        new Promise(resolve => setTimeout(() => resolve({ timeout: true }), 60000))]));
    };
    window.request = (name, command, args) => workers.get(name)(command, args);
  });
  const request = (name, command, args) => faulty.evaluate(([name, command, args]) => window.request(name, command, args), [name, command, args]);
  const fatal = (id, cause = "Maximum call stack size exceeded") => ({ id, error: { kind: "fault", fatal: true,
    message: `The kernel's WebAssembly instance failed (${cause}), and is not used again: nothing computed after the failure is kept.` } });
  // A check's steps are read when its reply is made, inside the boundary.
  const lamp = "inductive Lamp { dark; lit; }\ndef x : Lamp { exact dark; }\n";
  await faulty.evaluate(() => window.startWorker("steps"));
  await request("steps", "fail-in-steps");
  assert.deepEqual(await request("steps", "check", { source: lamp }), fatal(2));
  // A check is installed as its reply is made: a trap freeing the program it
  // replaces is answered too.
  await faulty.evaluate(() => window.startWorker("install"));
  assert.equal((await request("install", "check", { source: lamp })).result.complete, true);
  await request("install", "fail-next-free");
  assert.deepEqual(await request("install", "check", { source: lamp }), fatal(3, "unreachable"));
  // An inspection, a contextual query and a signature.
  const scoped = { source: "import unat;\nuse unat;\ninductive Lamp { dark; lit; }\ndef x : UNat := 7;\n", collectScopes: true };
  for (const [name, command, args] of [["inspect", "inspect", { binding: "current__x" }],
    ["context", "context-run", { input: "typeof x;" }], ["signature", "signature", { binding: "current__Lamp" }]]) {
    await faulty.evaluate(name => window.startWorker(name), name);
    await request(name, "check", scoped);
    if (name === "context") {
      const point = (await request(name, "contexts")).result.points.at(-1);
      args.session = (await request(name, "context-open", { scope: point.id })).result.session;
    }
    await request(name, "fail-next-kernel-call");
    const reply = await request(name, command, args);
    assert.deepEqual(reply, fatal(reply.id), name);
  }
  await faulty.close();
  console.log("PASS workers: every request a kernel failure ends is answered, fatal, and the worker stops");
  // The proof page: its worker's kernel fails in an inspection, with another
  // inspection queued behind it, after the module it imports has changed and
  // its source has been edited. Both are answered; a new worker checks the
  // edited source again, held up reading that import past the thirty seconds
  // an inspection has (the page's clock runs them at once), while an
  // inspection asked meanwhile waits for it; and the page reads everything
  // again from the check: the assumption the import now states, its
  // contexts, and its console's session, restored statement by statement.
  const workspace = await injected.newPage();
  const shown = (selector, page = workspace) => page.evaluate(selector => document.querySelector(selector)?.textContent ?? "", selector);
  const until = async (selector, test, page = workspace) => {
    for (let tries = 0; !test(await shown(selector, page)); tries++) {
      assert.ok(tries < 1200, `${selector}: ${await shown(selector, page)}`);
      await new Promise(resolve => setTimeout(resolve, 100));
    }
  };
  const helped = "import lists;\ndef x : Unit := h;\ndef y(n : Unit) : Unit := n;\ndef base : Unit := tt;\n";
  await workspace.goto(new URL(`proof.html?example=1#source=${Buffer.from(helped).toString("base64url")}`, base).href);
  await until("#status", text => text.endsWith("checked · no axioms"));
  await workspace.locator("#collect-contexts").check();
  await until("#context-panel [role=status]", text => text.startsWith("Open a context"));
  // A statement the session refuses, and an entry of two statements, the
  // first of which extends the session.
  const unknown = "E237: Unknown command /fail-next-kernel-call. /help lists the commands.";
  assert.deepEqual((await entries(workspace, ["let kept := tt;", "let surprise := added;", "let saved := base; typeof absent;",
    "/fail-next-kernel-call"])).slice(-5),
    ["kept : Unit", "E343: Untranslated name: added", "saved : Unit", "E343: Untranslated name: absent", unknown]);
  // The source, edited and not checked: base is gone, and added is there.
  await workspace.locator("#edit-mode").click();
  await workspace.locator("#editor").fill(helped.replace("def base", "def added"));
  await workspace.locator("#read-mode").click();
  lists = "def h := axiom Unit;\n";
  await workspace.clock.install();
  let release;
  listsHeld = new Promise(resolve => { release = resolve; });
  const asked = new Promise(resolve => { listsAsked = resolve; });
  // A local variable where it is used: its inspection links to its context.
  const occurrence = workspace.locator('#read-source button[data-name="n"]').last();
  await workspace.locator('#read-source [data-name="x"]').first().click();
  await occurrence.click();
  await Promise.race([asked, new Promise((_, reject) =>
    setTimeout(() => reject(new Error("No new worker read the import.")), 120000))]);
  await workspace.locator('#read-source [data-name="y"]').first().click();
  await new Promise(resolve => setTimeout(resolve, 1000));
  await workspace.clock.runFor(31000);
  release();
  listsHeld = null; listsAsked = () => {};
  await until("#status", text => text.endsWith("checked · 1 explicit assumptions"));
  assert.match(await shown("#source-notice"), /^The kernel's WebAssembly instance failed, so a new checking worker checks your current source again/);
  await until("#context-panel [role=status]", text => text.startsWith("Open a context"));
  await occurrence.click();
  await workspace.locator("#open-context-repl").waitFor();
  await workspace.locator("#open-context-repl").click();
  await until("#context-panel [role=status]", text => text.includes("Results apply only to this selected instance"));
  // What extended the session is checked again, as it was, and nothing
  // else: saved, over a base that is gone, is lost, and named; surprise,
  // refused before, is refused still, though added is there now.
  assert.deepEqual((await entries(workspace, ["typeof surprise;", "typeof saved;", "typeof kept;"])).slice(-4), [
    "The kernel was restarted. These entries could not be checked again, and what they defined is gone: let saved := base;",
    "E343: Untranslated name: surprise", "E343: Untranslated name: saved", "Unit"]);
  console.log("PASS proof page: a failed kernel stops its worker; a new one checks the source again, and the page reads it all again");
  // A worker that replaced a failed one and fails too before the reader
  // does anything, here in the inspection the page asks of it once it has
  // checked the source again and restored the console's session: the page
  // starts no other, and says so. The reader's check starts one, which is
  // replaced once more when it fails.
  plans.push("inspection", "inspection");
  assert.deepEqual((await entries(workspace, ["/fail-next-kernel-call", "typeof kept;"])).slice(-2), [unknown, fault]);
  await until("#source-notice", text => text === "The kernel failed again in the checking worker that replaced a failed one, so no other starts on its own: check the source to start one.");
  await new Promise(resolve => setTimeout(resolve, 2000));
  assert.deepEqual(plans, ["inspection"]);
  await workspace.locator("#check").click();
  await until("#source-notice", text => text.startsWith("The kernel's WebAssembly instance failed, so a new checking worker checks"));
  assert.deepEqual((await entries(workspace, ["typeof kept;"])).slice(-3), [restarted[1], restarted[1], "Unit"]);
  assert.deepEqual(plans, []);
  await workspace.close();
  console.log("PASS proof page: a worker that replaced a failed one and fails too is not replaced until the reader checks again");
  // An embedded proof page, a reference page's inspector: its kernel fails
  // in an example's inspection, and the example the reference page sends
  // while the new worker loads is the one the new worker checks.
  plans.push("inspection");
  const framed = await injected.newPage();
  await framed.goto(new URL("proof.html?example=1&embed=1", base).href);
  await until("#status", text => text === "Ready to check", framed);
  let load;
  kernelHeld = new Promise(resolve => { load = resolve; });
  const loading = new Promise(resolve => { kernelAsked = resolve; });
  const send = source => framed.evaluate(source => postMessage({ type: "cubist-inspect", source }, location.origin), source);
  await send("def first : Unit := tt;\n");
  await Promise.race([loading, new Promise((_, reject) =>
    setTimeout(() => reject(new Error("No new worker loaded the kernel.")), 120000))]);
  await send("def second : Unit := tt;\n");
  load();
  kernelHeld = null; kernelAsked = () => {};
  await until("#inspect-name", text => text === "second", framed);
  assert.equal(await framed.evaluate(() => document.querySelector("#editor").value), "def second : Unit := tt;\n");
  await framed.close();
  await injected.close();
  console.log("PASS embedded proof page: an example sent while a new worker loads is the one it checks");
  // Slash commands: /modules lists what import can load; /clear and /restart
  // act on the console.
  await enter("/modules lists");
  assert.match((await lastResults(1))[0], /^Library \(1\): lists\n/);
  await enter("/clear");
  assert.equal(await page.locator(".repl-log").last().locator(".repl-result, .repl-entry").count(), 0);
  await enter("/restart");
  await page.waitForFunction(() => document.querySelector(".repl-log")?.textContent.includes("Started a new session."));
  await enter("typeof x;");
  assert.deepEqual(await lastResults(1), ["E343: Untranslated name: x"]);
  console.log("PASS REPL page: /modules, /clear and /restart");
  // The Files page opens on the library's folder, names a selected file in
  // its title, and Back returns to no selection.
  await page.goto(new URL("files.html", base).href);
  await page.waitForSelector("#tree details.folder");
  assert.equal(await page.title(), "Cubist · Files");
  assert.deepEqual(await page.locator("#tree > details").evaluateAll(roots => roots.map(root => root.open)), [true, false, false, false]);
  await page.locator('#tree a[data-path="library/unat.cubist"]').click();
  await page.waitForFunction(() => document.querySelector("#file-source")?.textContent.includes("inductive"));
  assert.equal(await page.title(), "unat.cubist · Cubist files");
  await page.goBack();
  await page.waitForFunction(() => document.title === "Cubist · Files");
  assert.ok(await page.locator("#file-empty").isVisible());
  assert.equal(await page.locator("#tree a[aria-current]").count(), 0);
  // The Files page lists every source by folder, under its four roots, and a
  // documentation example opens in the workspace by its path, and checks.
  await page.goto(new URL(`files.html?path=${encodeURIComponent("docs/examples/h1/winding.cubist")}`, base).href);
  await page.waitForFunction(() => document.querySelector("#file-source")?.textContent.includes("inductive"));
  assert.deepEqual(await page.locator("#tree > details > summary .folder-name").allTextContents(),
    ["Library", "Cubist tests", "Archive", "Documentation examples"]);
  assert.ok(await page.locator('a[data-path="docs/examples/h1/winding.cubist"][aria-current]').isVisible());
  await page.fill("#file-filter", "glue_printed");
  assert.equal(await page.locator("#tree li.file:not([hidden])").count(), 1);
  await page.locator("#file-open").click();
  await page.waitForFunction(() => /checked/.test(document.querySelector("#status")?.textContent) &&
    !/incomplete/.test(document.querySelector("#status").textContent));
  assert.equal(await page.locator("#proof-title").textContent(), "Documentation example: docs/examples/h1/winding.cubist");
  console.log("PASS Files page: folders, filter, preview, and a documentation example checked in the workspace");
  // The workspace's explorer marks the open file and opens another in its
  // place; closed, it stays closed. Its folders stay as they were left: the
  // library's is open since unat opened in this tab.
  assert.ok(await page.locator('#explorer-tree a[data-path="docs/examples/h1/winding.cubist"][aria-current]').isVisible());
  assert.ok(await page.locator('#explorer-tree details[data-path="library"]').evaluate(details => details.open));
  await page.locator('#explorer-tree a[data-path="library/lists.cubist"]').click();
  await page.waitForFunction(() => document.querySelector("#proof-title")?.textContent === "Library: lists");
  assert.ok(await page.locator('#explorer-tree a[data-path="library/lists.cubist"][aria-current]').isVisible());
  await page.locator("#explorer-toggle").click();
  assert.ok(await page.locator("#explorer-tree").isHidden());
  await page.reload();
  await page.waitForFunction(() => document.querySelector("#proof-title")?.textContent === "Library: lists");
  assert.equal(await page.locator("#explorer-toggle").getAttribute("aria-expanded"), "false");
  assert.ok(await page.locator("#explorer-tree").isHidden());
  console.log("PASS workspace explorer: current file, opening a file, closing");
  // The first proof's Elaboration panel opens on demand and shows every
  // declaration, down to the kernel's opcodes, with a link for more info.
  await page.goto(new URL("reference/first-proof.html#elaboration", base).href);
  const elaboration = page.locator("#elaboration details.elaboration");
  await elaboration.locator("summary").click();
  await elaboration.locator(".elaboration-declaration").nth(2).waitFor();
  assert.equal(await elaboration.locator(".elaboration-declaration").count(), 3);
  assert.match(await elaboration.textContent(), /intro n;\s*⊢ forall n : UNat\. exists m : UNat\. lt\(n, m\)\s*builds fun \(n : UNat\) => \?/);
  assert.match(await elaboration.getByRole("link", { name: "For more info" }).first().getAttribute("href"), /kernel-overview\.html$/);
  // The kernel's check as a THTH-style forward derivation, with comments.
  const derivation = elaboration.locator(".derivation").first();
  assert.match(await derivation.textContent(), /\/\/ \{\} ⊢ UNat : U0\s*2 SortBegin\(\)/);
  assert.match(await derivation.textContent(), /\/\/ \{n : UNat\}\s*\d+ CtxExt\(2\)/);
  assert.ok(await elaboration.locator(".derivation-scaffold").count() > 0);
  await page.goto(new URL("reference/kernel-terms.html", base).href);
  assert.equal(await page.locator("#opcodes tbody tr").count(), 53);
  console.log("PASS elaboration panel and the kernel terms table");
  await page.goto(new URL("workbench.html", base).href);
  await page.waitForFunction(() => document.querySelector("#status")?.textContent.includes("checked"));
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  assert.equal(await page.locator("#name").textContent(), "example");
  // The workbench shares the site's navigation, with its return link.
  assert.deepEqual(await page.locator("header nav a").allTextContents(),
    ["Proof highlights", "Files", "Kernel reference", "Language reference", "REPL", "GitHub repository", "← Back to Cubist"]);
  assert.deepEqual(errors, []);
  console.log(`PASS static kernel workbench (${base})`);
  // Every transport consumer must finish with an error when the worker
  // cannot import its kernel, including clients started only on first use.
  const unavailable = await browser.newContext();
  await unavailable.route("**/dist/cubical.mjs*", route => route.abort());
  const failed = await unavailable.newPage();
  const failureErrors = [];
  failed.on("pageerror", error => failureErrors.push(error.message));
  const proof = new URL(`proof.html?example=1#source=${Buffer.from("import unat;\ndef x : Unit := tt;").toString("base64url")}`, base).href;
  await failed.goto(proof);
  await failed.waitForFunction(() => document.querySelector("#diagnostic")?.textContent.includes("Build with make wasm."));
  assert.equal(await failed.locator("#check-loader").isHidden(), true);
  assert.equal(await failed.locator("#source-panel").getAttribute("aria-busy"), "false");
  // The source is readable without a check: previewed and highlighted, its
  // line numbers not yet inspectable, the inspector explaining itself, and an
  // import link opening its module.
  await failed.locator("#read-mode").click();
  assert.equal(await failed.locator("#read-source .source-line").count(), 2);
  assert.ok(await failed.locator("#read-source .keyword").count() > 0);
  assert.equal(await failed.locator("#read-source button.line-number").count(), 0);
  assert.match(await failed.locator("#source-hint").textContent(), /did not check/);
  assert.ok(await failed.locator("#inspect-empty").isVisible());
  assert.equal(await failed.locator("#kernel-terms").isVisible(), false);
  await failed.locator('#read-source a.reference[data-name="unat"]').click();
  await failed.waitForURL("**/proof.html?proof=unat");
  await failed.goto(new URL("reference/types.html", base).href);
  await seven(failed).scrollIntoViewIfNeeded();
  await sevenBar(failed).filter({ hasText: "Not checked" }).waitFor();
  // Enhancement is lazy: scroll to start a new request after failure is known.
  const laterExample = failed.locator('pre > code[data-check="reject"]').last();
  await laterExample.scrollIntoViewIfNeeded();
  await failed.waitForFunction(() => [...document.querySelectorAll('pre > code[data-check="reject"]')].at(-1)
    ?.parentElement.nextElementSibling?.textContent.includes("Not checked"));
  await failed.goto(new URL("repl.html", base).href);
  await failed.locator(".repl-text").fill("tt");
  await failed.locator(".repl-text").press("Enter");
  await failed.waitForFunction(() => document.querySelector(".repl-error")?.textContent.includes("Build with make wasm.")
    && !document.querySelector(".repl-form.busy"));
  await unavailable.unroute("**/dist/cubical.mjs*");
  await failed.goto(proof);
  await failed.waitForFunction(() => document.querySelector("#status")?.textContent.includes("· checked"));
  assert.equal(await failed.locator("#diagnostic").isVisible(), false);
  assert.deepEqual(failureErrors, [], "worker failures must not leave uncaught page errors");
  await unavailable.close();
  console.log("PASS worker startup failures settle in workspace, reference and REPL; a fresh worker recovers");
}, { base: process.argv[2], site: true });
