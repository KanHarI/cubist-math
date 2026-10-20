import { browserTest } from "./browser-test.mjs";
import assert from "node:assert/strict";
import { gaps } from "./frontend-generation-cases.mjs";
const natural = {tag:"Sort",signature:"unat__UNat",parameters:[],levels:[]};
const zero = {tag:"Con",index:0,name:"zero",sort:natural};
const one = {tag:"App",fn:{tag:"Con",index:1,name:"succ",sort:natural},arg:zero};
await browserTest(async ({ browser, base }) => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors = []; page.on("pageerror", error => errors.push(error.message));
  const settled = target => target.waitForFunction(() => document.body.dataset.busy === "false");
  const idle = async () => {
    try {
      await page.waitForFunction(() => document.querySelector("#check")?.disabled === false && document.querySelector("#check-loader")?.hidden);
    } catch (error) {
      console.error(await page.locator("#diagnostic").textContent(), errors); throw error;
    }
  };
  const inspected = name => page.waitForFunction(name =>
    document.querySelector("#inspect-name")?.textContent === name &&
    document.querySelector("#kernel-view")?.disabled === false, name);
  const openProof = async (proof, name) => {
    await page.goto(`${base}/proof.html?proof=${proof}&name=${name}`);
    await idle(); await inspected(name);
  };
  // The navigation links also open the workbench without a proof transfer.
  // Its standalone example must use the bundled unary source.
  // Inject one inspection failure at the host boundary to exercise recovery
  // without making a kernel declaration fail.
  await page.context().route("**/cubical-program.mjs*", async route => {
    const response = await route.fetch(), body = await response.text();
    await route.fulfill({ response, headers: { ...response.headers(), "cache-control": "no-store" }, body: body + `
      const originalInspect = CubicalProgram.prototype.inspect;
      CubicalProgram.prototype.inspect = function(binding, ...args) {
        if (binding === "workbench__identity") throw Error("Injected inspection failure");
        return originalInspect.call(this, binding, ...args);
      };
    ` });
  });
  await page.goto(`${base}/workbench.html`);
  await page.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  await settled(page);
  await page.context().unroute("**/cubical-program.mjs*");
  assert.equal(await page.locator("#name").textContent(), "example");
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  assert.equal(await page.locator("#normalize").isDisabled(), false);
  assert.equal(await page.locator("#delta-expression").isDisabled(), false);
  // Native operations keep the actual Step judgement and select an occurrence
  // by its root/operand path; a refusal must not invalidate the checked view.
  await page.locator("#workbench-view").selectOption("assembly"); await settled(page);
  assert.equal(await page.locator("#kernel-parent").evaluate(button => getComputedStyle(button).cursor), "default");
  assert.equal(await page.locator('#kernel-operands [data-unfold-operand="0"]').textContent(), "δ unfold identity");
  assert.equal(await page.locator("#kernel-tree").getAttribute("open"), null);
  assert.equal(await page.locator("#kernel-tree-content").textContent(), "");
  assert.ok((await page.locator("#kernel-tree").boundingBox()).y > (await page.locator("#kernel-apply").boundingBox()).y);
  await page.locator("#kernel-tree > summary").click(); await settled(page);
  await page.locator("#kernel-tree-content .native-tree-node").first().waitFor();
  assert.match(await page.locator("#kernel-tree-content").textContent(), /CC_APP.*CC_DEFREF.*identity/);
  const argumentBranch = page.locator('#kernel-tree-content summary[data-path="[1]"]');
  await argumentBranch.click(); await settled(page);
  await page.locator('#kernel-tree-content [data-path="[1,0]"]').waitFor();
  assert.match(await page.locator('#kernel-tree-content [data-path="[1,0]"]').textContent(), /CC_CON/);
  await page.locator('#kernel-tree-content [data-path="[0]"] button').click(); await settled(page);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[0\].*CC_DEFREF/);
  await page.locator("#kernel-root").click(); await settled(page);
  await page.locator("#kernel-tree > summary").click();
  // A collapsed selection round trip must not retain a stale tree cache key.
  await page.locator('#kernel-operands [data-operand="0"]').click(); await settled(page);
  await page.locator("#kernel-root").click(); await settled(page);
  await page.locator("#kernel-tree > summary").click();
  await page.locator("#kernel-tree-content .native-tree-node").first().waitFor();
  await settled(page);
  await page.locator("#kernel-tree > summary").click();
  const originalSyntax = await page.locator("#syntax").inputValue();
  await page.locator("#kernel-apply").click(); await settled(page);
  assert.match(await page.locator("#diagnostic").textContent(), /Beta needs a lambda/);
  assert.equal(await page.locator("#kernel-apply").isDisabled(), false);
  assert.equal(await page.locator("#syntax").inputValue(), originalSyntax);
  await page.locator('#kernel-operands [data-operand="0"]').click(); await settled(page);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[0\].*CC_DEFREF/);
  assert.equal(await page.locator("#kernel-preview").textContent(), "identity");
  await page.locator("#kernel-delta").click(); await settled(page);
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[0\].*CC_LAM/);
  const betaAction = page.locator('#kernel-actions [data-kernel-rule="beta"]');
  assert.equal(await betaAction.textContent(), "β reduce containing application");
  assert.equal(await betaAction.getAttribute("data-kernel-path"), "[]");
  // A refused parent operation retains the lambda selection and its history.
  await page.locator("#kernel-budget").fill("1");
  await betaAction.click(); await settled(page);
  assert.match(await page.locator("#diagnostic").textContent(), /budget exhausted/);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[0\].*CC_LAM/);
  await page.locator("#kernel-budget").fill("100000");
  await betaAction.click(); await settled(page);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[\]/);
  await page.locator("#back").click(); await settled(page);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[0\].*CC_LAM/);
  await page.locator("#kernel-parent").click(); await settled(page);
  assert.equal(await betaAction.textContent(), "β reduce application");
  await betaAction.click(); await settled(page);
  await page.locator("#workbench-view").selectOption("graph"); await settled(page);
  assert.match(await page.locator(".graph-root .graph-highlight").textContent(), /beta on the term at the root/);
  assert.ok(await page.locator(".graph-highlight", { hasText: "delta on the term at [0]" }).count() > 0);
  await page.locator("#back").click(); await settled(page);
  await page.locator("#back").click(); await settled(page);
  assert.match(await page.locator("#status").textContent(), /restored previous judgement/);
  assert.equal(await page.locator("#syntax").inputValue(), originalSyntax);
  // Clipboard copies a diagnostic log, including refused attempts and Back.
  // Use the actual clipboard API, then exercise the denied-access fallback.
  await page.context().grantPermissions(["clipboard-read", "clipboard-write"]);
  await page.locator("#copy-trace").click();
  await page.waitForFunction(() => document.querySelector("#trace-status").textContent.startsWith("Copied"));
  const copiedTrace = JSON.parse(await page.evaluate(() => navigator.clipboard.readText()));
  assert.equal(copiedTrace.format, "cubist-workbench-trace");
  assert.ok(copiedTrace.entries.some(e => e.command === "step" && e.status === "refused"));
  assert.ok(copiedTrace.entries.some(e => e.command === "step" && e.rule === "beta" && e.status === "accepted"));
  assert.ok(copiedTrace.entries.some(e => e.command === "back"));
  assert.ok(copiedTrace.entries.find(e => e.command === "step" && e.rule === "delta").detail.before.nodes[0].definition);
  await page.evaluate(() => Object.defineProperty(navigator.clipboard, "writeText", {
    configurable: true, value: async () => { throw new DOMException("Denied", "NotAllowedError"); },
  }));
  await page.locator("#copy-trace").click();
  await page.locator("#trace-fallback").waitFor({ state: "visible" });
  assert.equal(JSON.parse(await page.locator("#trace-fallback").inputValue()).format, copiedTrace.format);
  assert.equal(await page.locator("#trace-fallback").evaluate(el => el.selectionEnd - el.selectionStart),
    (await page.locator("#trace-fallback").inputValue()).length);
  await page.evaluate(() => delete navigator.clipboard.writeText);
  await page.locator("#workbench-view").selectOption("assembly"); await settled(page);
  await page.locator("#kernel-root").click(); await settled(page);
  await page.locator("#kernel-rule").selectOption("normalize"); await settled(page);
  await page.locator("#kernel-budget").fill("1"); await settled(page);
  await page.locator('#kernel-actions [data-kernel-rule="normalize"]').click(); await settled(page);
  assert.match(await page.locator("#diagnostic").textContent(), /budget exhausted/);
  assert.equal(await page.locator("#kernel-apply").isDisabled(), false);
  await page.locator("#kernel-budget").fill("100000"); await settled(page);
  await page.locator("#kernel-apply").click(); await settled(page);
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await page.locator("#back").click(); await settled(page);
  await page.locator('#kernel-operands [data-operand="0"]').click(); await settled(page);
  await page.locator("#workbench-view").selectOption("math"); await settled(page);
  await page.locator('#expression [data-name="identity"]').click(); await settled(page);
  assert.match(await page.locator("#diagnostic").textContent(), /Injected inspection failure/);
  assert.match(await page.locator("#status").textContent(), /previous checked judgement retained/);
  assert.equal(await page.locator("#normalize").isDisabled(), false);
  assert.equal(await page.locator("#back").isDisabled(), true, "a failed inspection adds no history");
  await page.locator("#mathematical-view details > summary").click(); await settled(page);
  await page.locator("#syntax").fill(JSON.stringify(zero)); await settled(page);
  assert.equal(await page.locator("#kernel-apply").isDisabled(), true);
  await page.locator("#check").click(); await settled(page);
  await page.locator("#workbench-view").selectOption("assembly"); await settled(page);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[\].*CC_CON/);
  assert.equal(await page.locator("#back").isDisabled(), true);
  await page.locator("#workbench-view").selectOption("math"); await settled(page);
  await page.locator("#syntax").fill(originalSyntax); await settled(page); await page.locator("#check").click(); await settled(page);
  await page.locator("#workbench-view").selectOption("assembly"); await settled(page);
  await page.locator('#kernel-operands [data-operand="0"]').click(); await settled(page);
  await page.locator("#workbench-view").selectOption("math"); await settled(page);
  await page.locator("#normalize").click(); await settled(page);
  assert.equal(await page.locator("#expression").textContent(), "2");
  await page.locator("#workbench-view").selectOption("assembly"); await settled(page);
  assert.match(await page.locator("#kernel-selection").textContent(), /expression \[\].*CC_APP/);
  // Rejected navigation preserves the selected occurrence; a fatal WASM trap
  // disables the session and gives a reload instruction instead of a refusal.
  const broken = await browser.newPage();
  const brokenErrors = []; broken.on("pageerror", error => brokenErrors.push(error.message));
  await broken.context().route("**/cubical-workbench-worker.mjs", async route => {
    const response = await route.fetch();
    const body = (await response.text()).replace("await session.handle(command, args)", "await injectedHandle(command, args)");
    await route.fulfill({ response, headers: { ...response.headers(), "cache-control": "no-store" }, body: `let refusedPreview = false;\n` + body + `
      async function injectedHandle(command, args) {
        if (command === "occurrence" && args.path.length === 1 && args.path[0] === 1 && !refusedPreview) {
          refusedPreview = true; throw Error("Injected preview failure");
        }
        if (command === "step" && args.rule === "face") throw new WebAssembly.RuntimeError("Injected fatal trap");
        if (command === "step" && args.rule === "whnf") await new Promise(resolve => setTimeout(resolve, 1000));
        return session.handle(command, args);
      }
    ` });
  });
  await broken.goto(`${base}/workbench.html?view=ast`);
  await broken.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  await settled(broken);
  await broken.locator('#kernel-operands [data-operand="1"]').click(); await settled(broken);
  assert.match(await broken.locator("#diagnostic").textContent(), /Injected preview failure/);
  assert.match(await broken.locator("#kernel-selection").textContent(), /expression \[\]/);
  await broken.locator('#kernel-operands [data-operand="1"]').click(); await settled(broken);
  assert.match(await broken.locator("#kernel-selection").textContent(), /expression \[1\]/);
  await broken.context().grantPermissions(["clipboard-read", "clipboard-write"]);
  await broken.locator('#kernel-actions [data-kernel-rule="whnf"]').click();
  await broken.waitForFunction(() => document.body.dataset.busy === "true");
  await broken.locator("#copy-trace").click();
  await broken.waitForFunction(() => document.querySelector("#trace-status").textContent.startsWith("Copied"));
  const pendingTrace = JSON.parse(await broken.evaluate(() => navigator.clipboard.readText()));
  assert.equal(pendingTrace.entries.at(-1).status, "running");
  await settled(broken);
  await broken.locator("#kernel-rule").selectOption("face");
  await broken.locator("#kernel-apply").click(); await settled(broken);
  assert.match(await broken.locator("#status").textContent(), /Kernel worker stopped.*Reload/);
  assert.match(await broken.locator("#diagnostic").textContent(), /Injected fatal trap/);
  assert.equal(await broken.locator("#kernel-apply").isDisabled(), true);
  assert.equal(await broken.locator("#check").isDisabled(), true);
  assert.equal(await broken.locator("#copy-trace").isDisabled(), false);
  await broken.context().grantPermissions(["clipboard-read", "clipboard-write"]);
  await broken.locator("#copy-trace").click();
  await broken.waitForFunction(() => document.querySelector("#trace-status").textContent.startsWith("Copied"));
  const fatalTrace = JSON.parse(await broken.evaluate(() => navigator.clipboard.readText()));
  assert.equal(fatalTrace.entries.at(-1).status, "worker-failed");
  assert.match(fatalTrace.entries.at(-1).error.message, /Injected fatal trap/);
  assert.ok(fatalTrace.current.workerFailed);
  assert.deepEqual(brokenErrors, []);
  await broken.close();
  // An example opened in the workspace keeps its source in #source=… while the
  // quick reference's links scroll and move focus, so a reload reopens it.
  const example = Buffer.from("def kept_after_reload : UNat := 7;").toString("base64")
    .replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  await page.goto(`${base}/proof.html?example=1#source=${example}`); await idle();
  await page.locator("#guide-link").click();
  assert.equal(await page.locator("#language-guide").getAttribute("open"), "");
  await page.locator('.quick-topics a[href="#quick-paths"]').click();
  assert.equal(new URL(page.url()).hash, `#source=${example}`, "a topic link keeps the example's source");
  assert.equal(await page.evaluate(() => document.activeElement?.id), "quick-paths");
  assert.ok(await page.locator("#quick-paths").evaluate(heading => heading.getBoundingClientRect().top < innerHeight));
  await page.locator('.quick-topics a[href="#quick-universes"]').focus();
  await page.keyboard.press("Enter");
  assert.equal(await page.evaluate(() => document.activeElement?.id), "quick-universes", "Enter moves focus to the topic");
  assert.equal(new URL(page.url()).hash, `#source=${example}`);
  await page.reload(); await idle();
  assert.match(await page.locator("#editor").inputValue(), /kept_after_reload/);
  // Structured parse locations survive the real worker request boundary.
  const parseFailure=await page.evaluate(async()=>{
    const {WorkerRequests}=await import("./worker-requests.mjs");
    const requests=new WorkerRequests(new Worker("./cubical-worker.mjs",{type:"module"}));
    try {
      await requests.request("check",{source:"def broken := ;",module:"diagnostic_probe"});
      return null;
    } catch(error) {return {offset:error.offset,diagnostic:error.diagnostic};}
    finally {requests.terminate();}
  });
  assert.ok(parseFailure,"malformed source must return a worker error");
  assert.equal(parseFailure.diagnostic.primary.module,"diagnostic_probe");
  assert.equal(parseFailure.diagnostic.primary.start,parseFailure.offset);
  assert.equal(parseFailure.diagnostic.kind,"parse");
  // Frontend generation is a read-only snapshot of the last check, including
  // imported modules. Editing never changes that snapshot until a recheck.
  const generatedExample = `import hlevels;
theory Generated(U < UU0) { M : set U; c : M; }
// Keep this definition and its documentation.
def unchanged(x : Unit) : Unit := x;
initial N : Generated(U0);`;
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(generatedExample);
  await page.locator("#check").click(); await idle();
  await page.locator("#generated-mode").click(); await idle();
  const generatedSource = page.locator("#generated-source");
  assert.equal(await generatedSource.evaluate(element => element.tagName), "DIV");
  assert.equal(await generatedSource.locator("textarea, [contenteditable]").count(), 0);
  assert.ok(await generatedSource.locator(".keyword").count() > 0);
  assert.ok(await generatedSource.locator(".comment").count() > 0);
  assert.ok(await generatedSource.locator(".line-number").count() > 0);
  const generatedTextContent = async () => (await generatedSource.locator(".line-code").allTextContents()).join("\n");
  assert.equal(await page.locator("#generated-mode").getAttribute("aria-pressed"), "true");
  assert.equal(await page.locator("#editor").isVisible(), false);
  assert.equal(await page.locator("#read-source").isVisible(), false);
  const generatedText = await generatedTextContent();
  assert.match(generatedText, /def Generated\.Hom\.id/);
  assert.match(generatedText, /inductive N : set U0/);
  assert.match(generatedText, /\/\/ theory Generated\(U < UU0\)/);
  assert.match(generatedText, /\/\/ initial N : Generated\(U0\);/);
  assert.match(generatedText, /\/\/ Keep this definition and its documentation\.\ndef unchanged\(x : Unit\) : Unit := x;/);
  assert.doesNotMatch(generatedText, /display unavailable/);
  await generatedSource.locator('button[data-name="unchanged"]').first().click(); await inspected("unchanged");
  assert.equal(await page.locator("#kernel-type").textContent(), "Unit→Unit");
  const unchangedLine = generatedSource.locator(".source-line").filter({ hasText: "def unchanged" });
  await unchangedLine.locator('button[data-name="x"]').last().click(); await inspected("x");
  assert.equal(await page.locator("#kernel-type").textContent(), "Unit");
  const generatedIdentity = generatedSource.locator('button[data-name="Generated.Hom.id"]').first();
  await generatedIdentity.click(); await inspected("Generated.Hom.id");
  assert.ok((await page.locator("#kernel-type").textContent()).length > 0);
  assert.equal(await generatedSource.locator(".source-line.active").count(), 1);
  assert.equal(await page.locator("#read-source .source-line.active").count(), 0);
  await page.locator("#view-source").click();
  assert.equal(await page.locator("#read-source").isVisible(), true);
  assert.equal(await page.locator("#read-source .source-line.active").getAttribute("data-line"), "2");
  await page.locator('#read-source button[data-name="Generated"]').first().click(); await inspected("Generated");
  await page.locator("#back").click(); await inspected("Generated.Hom.id");
  assert.equal(await generatedSource.isVisible(), true, "Back restores the generated selection");
  await generatedSource.locator('button[data-name="IsSet"]').first().click(); await inspected("IsSet");
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=hlevels/);
  await generatedSource.locator('button[data-name="N"]').first().click(); await idle();
  assert.equal(await page.locator("#inspect-signature").isVisible(), true);
  assert.match(await page.locator("#inspect-kind").textContent(), /Declared type/);
  await page.locator("#generated-module").selectOption("hlevels"); await idle();
  assert.match(await generatedTextContent(), /Frontend generation · hlevels/);
  assert.match(await generatedTextContent(), /No frontend-generated declarations/);
  assert.match(await generatedTextContent(), /def IsSet/);
  await generatedSource.locator('button[data-name="IsSet"]').first().click(); await inspected("IsSet");
  await page.locator("#generated-module").selectOption("reference_example"); await idle();
  assert.equal(await generatedTextContent(), generatedText);
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(generatedExample.replaceAll("Generated", "Replacement"));
  await page.locator("#generated-mode").click(); await idle();
  assert.equal(await generatedTextContent(), generatedText);
  assert.match(await page.locator("#dirty").textContent(), /Generated Cubist show the last checked version/);
  await generatedSource.locator('button[data-name="Generated.Hom.id"]').first().click(); await inspected("Generated.Hom.id");
  await page.locator("#check").click(); await idle();
  assert.equal(await generatedSource.isVisible(), true);
  assert.match(await generatedTextContent(), /def Replacement\.Hom\.id/);
  assert.doesNotMatch(await generatedTextContent(), /def Generated\./);
  const replacementText = await generatedTextContent();
  // A parse failure preserves the previous program and its generation.
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("theory Broken {");
  await page.locator("#check").click(); await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), true);
  await page.locator("#generated-mode").click(); await idle();
  assert.equal(await generatedTextContent(), replacementText);
  await generatedSource.locator('button[data-name="Replacement.Hom.id"]').first().click(); await inspected("Replacement.Hom.id");
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`import hlevels;
theory Failed(U < UU0) { M : set U; c : M; law bad : c = tt; }`);
  await page.locator("#check").click(); await idle();
  await page.locator("#generated-mode").click(); await idle();
  assert.match(await generatedTextContent(), /Failed:base · failed/);
  assert.match(await generatedTextContent(), /Failed:hom · blocked/);
  assert.match(await page.locator("#generated-status").textContent(), /check incomplete/);
  await generatedSource.locator('button[data-name="Failed.Hom.id"]').first().click();
  assert.equal(await page.locator("#kernel-terms").isVisible(), false);
  assert.match(await page.locator("#inspect-description").textContent(), /Not checked by cubical C/);
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("def plain : Unit := tt;");
  await page.locator("#check").click(); await idle();
  await page.locator("#generated-mode").click(); await idle();
  assert.match(await generatedTextContent(), /No frontend-generated declarations/);
  assert.match(await generatedTextContent(), /def plain : Unit := tt;/);
  await generatedSource.locator('button[data-name="plain"]').first().click(); await inspected("plain");
  assert.equal(await page.locator("#generated-module option").count(), 1);
  assert.equal(await page.locator("#editor").inputValue(), "def plain : Unit := tt;");
  // The original remains inspectable after a duplicate is refused, and the
  // separate diagnostic points to the second declaration rather than it.
  const duplicate = Buffer.from("def kept : Unit := tt;\ndef kept : U0 := Unit;\ndef client : Unit := kept;").toString("base64url");
  await page.goto(`${base}/proof.html?example=1#source=${duplicate}`); await page.reload(); await idle();
  const duplicateError = page.locator("#result .declaration-error");
  assert.equal(await duplicateError.count(), 1);
  assert.match(await duplicateError.textContent(), /E872.*Duplicate declaration kept/);
  assert.match(await page.locator("#result").textContent(), /Verified client/);
  await duplicateError.getByRole("button", {name:"View source"}).click();
  assert.equal(await page.locator(".source-line.active").getAttribute("data-line"), "2");
  await page.locator('#read-source button[data-name="kept"]').first().click(); await inspected("kept");
  assert.equal(await page.locator("#kernel-type").textContent(), "Unit");
  // G9: every freshened law occurrence has its written label and navigates
  // to the binder, even when the uses occupy different source lines.
  const lawSource = gaps.G9.source.replace("law l(c : M) : k(c) = op(c, c);",
    "law l(c : M) :\n    k(c) =\n    op(c, c);");
  const lawLine = lawSource.slice(0, lawSource.indexOf("law l(c : M)")).split("\n").length;
  await page.goto(`${base}/proof.html?example=1#source=${Buffer.from(lawSource).toString("base64url")}`);
  await page.reload(); await idle(); await page.locator("#read-mode").click();
  const lawOccurrences = page.locator(`#read-source .source-line:is(${[0, 1, 2].map(n => `[data-line="${lawLine + n}"]`).join(", ")}) button[data-name="c"]`);
  assert.equal(await lawOccurrences.count(), 4);
  for (let index = 0; index < 4; index++) {
    await lawOccurrences.nth(index).click(); await inspected("c");
    assert.equal(await page.locator("#kernel-expression").textContent(), "c");
    assert.doesNotMatch(await page.locator("#kernel-context").textContent(), /\bc1\b/);
    await page.locator("#view-source").click();
    assert.equal(await page.locator(".source-line.active").getAttribute("data-line"), String(lawLine));
  }
  // A copied failure links both the caller and the precise imported source.
  const producer = `import unat;
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0) { M : U;
  def bad(n : UNat, x : Edge) : UNat := match x { lo => add(n, zero); hi => n; }
    obligations by { rw [unat_add_zero]; };
}`;
  await page.route("**/library/hlevels.cubist", route => route.fulfill({contentType:"text/plain",body:producer}));
  const consumer = "import hlevels;\ntheory Child(U < UU0) extends Parent {}";
  await page.goto(`${base}/proof.html?example=1#source=${Buffer.from(consumer).toString("base64url")}`);
  await page.reload(); await idle();
  const failure = page.locator("#result > div").filter({has:page.getByRole("button",{name:"Child.bad",exact:true})});
  await failure.locator(".diagnostic-site").filter({hasText:"Source: reference_example:2:"}).click();
  assert.match(await page.locator("#read-source .source-line.active").textContent(),/extends Parent/);
  const related = failure.locator(".diagnostic-site").filter({hasText:"Related: hlevels:5:"});
  assert.ok((await related.getAttribute("href")).includes(`offset=${producer.indexOf("unat_add_zero")}`));
  await related.click(); await idle();
  assert.equal(new URL(page.url()).searchParams.get("proof"),"hlevels");
  assert.match(await page.locator("#read-source .source-line.active").textContent(),/rw \[unat_add_zero\]/);
  await page.locator("#back").click(); await idle();
  assert.equal(await page.locator("#editor").inputValue(),consumer);
  await page.locator("#generated-mode").click(); await idle();
  await generatedSource.locator('button[data-name="Child.bad"]').first().click();
  await page.waitForFunction(()=>document.querySelector("#inspect-name").textContent==="Child.bad"
    && !document.querySelector("#view-source").hidden);
  const inheritedSource=await page.locator("#view-source").getAttribute("href");
  assert.match(inheritedSource,/proof=hlevels&name=Parent/);
  assert.ok(inheritedSource.includes(`offset=${producer.indexOf("bad(n")}`));
  await page.locator("#view-source").click(); await idle();
  assert.match(await page.locator("#read-source .source-line.active").textContent(),/def bad\(n/);
  await page.locator("#back").click(); await idle();
  assert.equal(await page.locator("#editor").inputValue(),consumer);
  await page.unroute("**/library/hlevels.cubist");
  // A name-only deep link inspects an inherited declaration without treating
  // its producer's offset as a position in the client document.
  const inheritedProducer="// "+"p".repeat(100)+"\ntheory Parent(U < UU0) { M : U; def twice(x : M) : M := x; }";
  const authoredStart=inheritedProducer.indexOf("twice(x"),header="import hlevels;\n",unrelated="// Unrelated client documentation.\n";
  const inheritedConsumer=header+"\n".repeat(authoredStart-header.length-unrelated.length)+unrelated
    +"def client_only : Unit := tt;\ntheory Child(U < UU0) extends Parent {}";
  await page.route("**/library/hlevels.cubist",route=>route.fulfill({contentType:"text/plain",body:inheritedProducer}));
  await page.goto(`${base}/proof.html?example=1&name=Child.twice#source=${Buffer.from(inheritedConsumer).toString("base64url")}`);
  await idle();await inspected("Child.twice");
  assert.equal(await page.locator("#read-source .source-line.active").count(),0);
  assert.ok((await page.locator("#view-source").getAttribute("href")).includes(`offset=${authoredStart}`));
  await page.locator("#view-source").click();await idle();
  assert.equal(new URL(page.url()).searchParams.get("proof"),"hlevels");
  assert.match(await page.locator("#read-source .source-line.active").textContent(),/def twice/);
  await page.unroute("**/library/hlevels.cubist");
  // An inductive header wrapped over lines keeps its h-level keyword, which
  // the highlighter finds in the whole source, not the line alone (H1).
  const wrapped = Buffer.from("inductive Wrapped(\n  A : U0\n) : prop {\n  point(a : A);\n}\n").toString("base64")
    .replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  // Only the hash differs from the page already open, so goto alone changes
  // the hash in place: reload to load the new source.
  await page.goto(`${base}/proof.html?example=1#source=${wrapped}`); await page.reload(); await idle();
  await page.locator("#read-mode").click();
  const modifier = page.locator("#read-source .source-line").nth(2).locator("span, button").filter({ hasText: /^prop$/ });
  assert.equal(await modifier.count(), 1, "the modifier is a token of its own");
  assert.match(await modifier.getAttribute("class"), /keyword/);
  // A declared type has no checked term: the inspector shows its signature
  // and its eliminator's clause types (the H1 specification's 6.5).
  await page.locator('#read-source button[data-name="Wrapped"]').first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name")?.textContent === "Wrapped"
    && !document.querySelector("#inspect-signature").hidden);
  assert.equal(await page.locator("#inspect-kind").textContent(), "Declared type · prop");
  assert.deepEqual(await page.locator("#inspect-constructors li code").allTextContents(),
    ["point : A -> Wrapped", "Wrapped.squash : forall x : Wrapped. forall x1 : Wrapped. x = x1"]);
  assert.match(await page.locator("#inspect-constructors li").nth(1).textContent(), /2 positions · 1 dimension · generated/);
  assert.equal(await page.locator("#inspect-eliminator-motive").textContent(), "For a motive P : Wrapped(A) -> U, one clause per constructor:");
  const clauses = await page.locator("#inspect-clauses li code").allTextContents();
  assert.equal(clauses[0], "point_case : forall x : A. P(point(x))");
  assert.match(clauses[1], /^squash_case : .*PathP\(fun \(i : Interval\) => P\(Wrapped\.squash\(x, x1\) @ i\), x2, x3\)$/);
  // Since H1's release a declared type carries no marker.
  assert.doesNotMatch(await page.locator("#inspect-axioms").textContent(), /kernel extension/);
  assert.equal(await page.locator("#kernel-terms").isVisible(), false, "no checked term to show");
  assert.deepEqual(errors, []);
  // UNat is an ordinary imported declaration: both occurrences in Z lead to
  // its signature and View source opens the actual inductive, not this use.
  await openProof("signed_integers", "Z");
  const naturalUses = page.locator('.source-line').filter({ hasText: "def Z := UNat or UNat;" })
    .locator('button[data-name="UNat"]');
  assert.equal(await naturalUses.count(), 2);
  await naturalUses.first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name")?.textContent === "UNat"
    && !document.querySelector("#inspect-signature").hidden);
  assert.deepEqual(await page.locator("#inspect-constructors li code").allTextContents(),
    ["zero : UNat", "succ : UNat -> UNat"]);
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=unat&name=UNat/);
  await page.locator("#view-source").click(); await idle();
  assert.equal(new URL(page.url()).searchParams.get("proof"), "unat");
  assert.equal(new URL(page.url()).searchParams.get("name"), "UNat");
  assert.match(await page.locator(".source-line.active").textContent(), /inductive UNat : U0/);
  assert.match(await page.locator("#editor").inputValue(), /succ\(n : UNat\)/);
  await page.locator("#back").click(); await idle();
  assert.equal(new URL(page.url()).searchParams.get("proof"), "signed_integers");
  assert.equal(await page.locator("#inspect-name").textContent(), "UNat");
  await openProof("suspension", "S1");
  for (const name of ["Suspension", "north", "south", "meridian", "suspension_induction", "suspension_meridian_beta"]) {
    const link = page.locator(`#read-source button[data-name="${name}"]`).first();
    assert.ok(await link.count(), `${name} has a source reference`);
    assert.doesNotMatch(await link.getAttribute("class"), /keyword|macro/);
    await link.click(); await inspected(name);
    assert.ok((await page.locator("#kernel-expression").textContent()).length > 0);
    assert.equal(await page.locator("#view-source").isVisible(), true);
  }
  await openProof("circle_group_identity", "circle_group_isomorphism");
  await page.locator('#read-source button[data-name="refl"]').first().click(); await inspected("refl");
  assert.match(await page.locator("#kernel-type").textContent(), /base/);
  await page.locator('#read-source button[data-name="="]').first().click(); await inspected("=");
  assert.match(await page.locator("#kernel-expression").textContent(), /CircleLoopGroup/);
  await page.locator('#read-source button[data-name="winding"]').first().click(); await inspected("winding");
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=circle/);
  await openProof("euclid", "euclid");
  assert.equal(await page.locator(".library").count(), 0);
  const sourceBounds = await page.locator("#source-panel").boundingBox();
  const resultsBounds = await page.locator("#result").boundingBox();
  assert.ok(resultsBounds.y >= sourceBounds.y + sourceBounds.height);
  assert.equal(await page.locator("#kernel-expression").textContent(), "euclid");
  await page.locator("#toggle-kernel-body").click();
  assert.match(await page.locator("#kernel-expression").textContent(), /λ.*n/);
  await page.locator("#toggle-kernel-body").click();
  const width = (await page.locator(".inspector").boundingBox()).width;
  await page.locator("#widen-inspector").click();
  assert.ok((await page.locator(".inspector").boundingBox()).width > width);
  await page.locator('.source-line [data-name="hd"]').first().click(); await inspected("hd");
  assert.equal(await page.locator("#kernel-type").textContent(), "Divides(succ(succ(i)),m)");
  assert.equal(await page.locator("#kernel-expression").textContent(), "hd");
  assert.equal(await page.locator("#kernel-context-list button").first().textContent(), "n");
  await page.locator('#kernel-type [data-name="i"]').click(); await inspected("i");
  assert.equal(await page.locator("#kernel-type").textContent(), "UNat");
  await page.locator("#back").click(); await inspected("hd");
  await page.locator('#kernel-context-list button').first().click(); await inspected("n");
  await page.locator("#back").click(); await inspected("hd");
  await page.locator("#kernel-view").selectOption("raw");
  assert.match(await page.locator("#kernel-type").textContent(), /"Fst"/);
  await page.locator("#kernel-view").selectOption("expanded");
  assert.match(await page.locator("#kernel-type").textContent(), /prime_divisor_exists/);
  await page.locator("#kernel-view").selectOption("notation");
  assert.equal(await page.locator("#kernel-type").textContent(), "Divides(succ(succ(i)),m)");
  const popup = page.waitForEvent("popup");
  await page.locator("#open-kernel-type").click();
  const workbench = await popup;
  workbench.on("pageerror", error => errors.push(error.message));
  await workbench.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked")); await settled(workbench);
  // It opens on the kernel graph, the instruction kernel's derivation.
  assert.equal(await workbench.locator("#workbench-view").inputValue(), "graph");
  await workbench.locator("#graph-listing .graph-row").first().waitFor();
  await workbench.locator("#workbench-view").selectOption("math"); await settled(workbench);
  assert.equal(await workbench.locator("#expression").textContent(), "Divides(succ(succ(i)),m)");
  assert.match(await workbench.locator("#context").textContent(), /n :UNat/);
  await workbench.locator("#fold-names").uncheck(); await settled(workbench);
  assert.match(await workbench.locator("#expression").textContent(), /prime_divisor_exists/);
  await workbench.locator("#fold-names").check(); await settled(workbench);
  await workbench.locator('#expression [data-name="i"]').click(); await settled(workbench);
  await workbench.waitForFunction(() => document.querySelector("#name")?.textContent === "i");
  await workbench.locator("#back").click(); await settled(workbench);
  await workbench.locator("#mathematical-view details > summary").click(); await settled(workbench);
  // The exported type is itself a U0 term: replace it with UNat and recheck.
  await workbench.locator("#syntax").fill(JSON.stringify(natural)); await settled(workbench);
  await workbench.locator("#check").click(); await settled(workbench);
  assert.equal(await workbench.locator("#expression").textContent(), "UNat");
  await workbench.locator("#syntax").fill('{"tag":"Var","name":"missing"}'); await settled(workbench);
  await workbench.locator("#check").click(); await settled(workbench);
  assert.equal(await workbench.locator("#diagnostic").isVisible(), true);
  assert.equal(await workbench.locator("#normalize").isDisabled(), true);
  await workbench.close();

  const assemblyPopup = page.waitForEvent("popup");
  await page.locator("#open-kernel-assembly").click();
  const assemblyBench = await assemblyPopup;
  assemblyBench.on("pageerror", error => errors.push(error.message));
  await assemblyBench.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked")); await settled(assemblyBench);
  assert.equal(await assemblyBench.locator("#workbench-view").inputValue(), "assembly");
  assert.equal(await assemblyBench.locator("#mathematical-view").isVisible(), false);
  assert.ok(await assemblyBench.locator(".assembly-table tbody tr").count() > 0);
  assert.match(await assemblyBench.locator(".assembly-roots").textContent(), /Context/);
  const reference = assemblyBench.locator('.assembly-table tr[data-opcode="CC_DEFREF"]').first();
  await reference.locator("[data-expand-definition]").click();
  await settled(assemblyBench);
  assert.equal(await assemblyBench.locator(".assembly-table tr.selected").count(), 1);
  const operand = assemblyBench.locator(".assembly-table .assembly-reference").first();
  const handle = await operand.getAttribute("data-handle"); await operand.click();
  await settled(assemblyBench);
  assert.equal(await assemblyBench.locator(".assembly-table tr.selected").getAttribute("id"), `assembly-node-${handle}`);
  // The kernel graph derives the view again in instruction mode, and its
  // node links lead back into the assembly's syntax graph.
  await assemblyBench.locator("#workbench-view").selectOption("graph"); await settled(assemblyBench);
  assert.match(await assemblyBench.locator("#graph-status").textContent(), /^\d+ judgements?, \d+ highlighted steps?; #\d+ is the conclusion\.$/);
  // hd is a local definition over n : UNat, derived with its context entry.
  assert.match(await assemblyBench.locator(".graph-row.graph-root .graph-statement").textContent(),
    /^\{n : UNat\} ⊢ prime_divisor_exists\(.*\)\.2\.2 : Divides\(/);
  // A lookup's definition is derived on request, as the lookup's premise, or
  // says which rule it still needs.
  const rows = await assemblyBench.locator(".graph-row").count();
  const expand = assemblyBench.locator(".graph-expand").first();
  const name = (await expand.textContent()).replace("Derive the body of ", "");
  await expand.click();
  await settled(assemblyBench);
  const outcome = assemblyBench.locator(".graph-definition", { hasText: new RegExp(`^(${name} is defined by #\\d+|The body of ${name} is not in instruction mode yet)`) });
  assert.equal(await outcome.count(), 1);
  assert.ok(await assemblyBench.locator(".graph-row").count() >= rows);
  await assemblyBench.locator(".graph-row.graph-root .graph-node").first().click(); await settled(assemblyBench);
  assert.equal(await assemblyBench.locator("#workbench-view").inputValue(), "assembly");
  assert.equal(await assemblyBench.locator(".assembly-table tr.selected").count(), 1);
  const downloaded = assemblyBench.waitForEvent("download");
  await assemblyBench.locator("#assembly-download").click(); await settled(assemblyBench);
  assert.match((await downloaded).suggestedFilename(), /\.ast\.txt$/);
  await assemblyBench.locator("#workbench-view").selectOption("math"); await settled(assemblyBench);
  assert.equal(await assemblyBench.locator("#mathematical-view").isVisible(), true);
  assert.equal(await assemblyBench.locator("#type").textContent(), "Divides(succ(succ(i)),m)");
  assert.ok((await assemblyBench.locator("#syntax").inputValue()).length > 0);
  await assemblyBench.locator("#workbench-view").selectOption("assembly"); await settled(assemblyBench);
  await assemblyBench.locator("#source-back").click();
  await assemblyBench.waitForFunction(() => document.querySelector("#inspect-name")?.textContent === "hd" && document.querySelector("#kernel-view")?.disabled === false);
  await assemblyBench.close();

  await page.locator('.source-line [data-name="prime_divisor_exists"]').first().click();
  await inspected("prime_divisor_exists"); await page.locator("#view-source").click(); await idle();
  assert.match(page.url(), /proof=primes/);
  await page.locator("#back").click(); await inspected("prime_divisor_exists");
  assert.match(page.url(), /proof=euclid/);

  await openProof("group_univalence", "group_isomorphism_is_equality");
  const groupType = await page.locator("#kernel-type").textContent();
  assert.match(groupType, /GroupIso/);
  assert.doesNotMatch(groupType, /G\d|H\d/);
  await page.locator("#toggle-kernel-body").click();
  const derived = page.locator('#kernel-expression [data-name="ua"]').first();
  await derived.click(); await inspected("ua");
  assert.match(await page.locator("#inspect-description").textContent(), /introduces no axiom/);

  await openProof("field_logic", "FieldExists");
  assert.match(await page.locator("#kernel-expression").textContent(), /‖/);
  await page.locator("#kernel-truncation-sugar").uncheck();
  assert.match(await page.locator("#kernel-expression").textContent(), /Truncate/);
  await page.locator('#kernel-expression [data-name="Truncate"]').first().click();
  await inspected("Truncate");

  await openProof("cubical_paths", "reverse_twice");
  await page.locator('.source-line').filter({ hasText: "fun (i : Interval) => p @ flip(i)" }).locator('[data-name="p"]').click();
  await inspected("p");
  assert.match(await page.locator("#kernel-context-list").textContent(), /Interval coordinates/);
  await page.setViewportSize({ width: 600, height: 900 });
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
  await page.setViewportSize({ width: 1440, height: 1000 });
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`import unat;
    use unat;
    def N := UNat;
    def IdentityType(A : U0) := A;
    def Alias := IdentityType(N);
    def id_(n : UNat) := n;
    def poly(U < UU0, A : U, x : A) : A := x;
    def value := typed(Alias, id_(0));`);
  await page.locator("#check").click(); await idle(); await inspected("value");
  const reductionPopup = page.waitForEvent("popup");
  await page.locator("#open-kernel-expression").click();
  const reductionBench = await reductionPopup;
  reductionBench.on("pageerror", error => errors.push(error.message));
  await reductionBench.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked")); await settled(reductionBench);
  await reductionBench.locator("#workbench-view").selectOption("math"); await settled(reductionBench);
  const selectReduction = async (side, kind, path = []) => {
    const before = await reductionBench.locator("#syntax").inputValue();
    await reductionBench.locator(`#${kind}-${side}`).click(); await settled(reductionBench);
    assert.equal(await reductionBench.locator("#syntax").inputValue(), before, "highlighting must not reduce");
    const site = reductionBench.locator(`#${side} [data-reduction-path='${JSON.stringify(path)}']`);
    if (kind === "beta") await site.press("Enter"); else await site.click();
    await settled(reductionBench);
  };
  assert.equal(await reductionBench.locator("#type").textContent(), "Alias");
  await selectReduction("type", "delta");
  assert.equal(await reductionBench.locator("#type").textContent(), "IdentityType(N)");
  await selectReduction("type", "delta", ["fn"]);
  assert.match(await reductionBench.locator("#type").textContent(), /λ/);
  await selectReduction("type", "beta");
  assert.equal(await reductionBench.locator("#type").textContent(), "N");
  await selectReduction("type", "delta");
  assert.equal(await reductionBench.locator("#type").textContent(), "UNat");
  await reductionBench.locator("#back").click(); await settled(reductionBench);
  assert.equal(await reductionBench.locator("#type").textContent(), "N");
  await reductionBench.locator("#normalize-type").click(); await settled(reductionBench);
  assert.equal(await reductionBench.locator("#type").textContent(), "UNat");
  await selectReduction("expression", "delta", ["arg", "fn"]);
  assert.match(await reductionBench.locator("#reduction-status").textContent(), /δ expression: id/);
  await selectReduction("expression", "beta");
  await selectReduction("expression", "beta");
  assert.equal(await reductionBench.locator("#expression").textContent(), "0");
  await reductionBench.locator("#beta-expression").click(); await settled(reductionBench);
  assert.match(await reductionBench.locator("#reduction-status").textContent(), /No β sites/);
  await reductionBench.locator("#back").click(); await settled(reductionBench);
  assert.match(await reductionBench.locator("#expression").textContent(), /λ/);
  await reductionBench.locator("#normalize").click(); await settled(reductionBench);
  assert.equal(await reductionBench.locator("#expression").textContent(), "0");
  await reductionBench.locator("#mathematical-view details > summary").click(); await settled(reductionBench);
  const ref = { tag: "DefRef", name: "cubical_paths__id_" };
  const repeated = { tag: "App", fn: ref, arg: { tag: "App", fn: ref, arg: zero } };
  await reductionBench.locator("#syntax").fill(JSON.stringify(repeated)); await settled(reductionBench);
  await reductionBench.locator("#check").click(); await settled(reductionBench);
  await reductionBench.locator("#delta-expression").click(); await settled(reductionBench);
  assert.equal(await reductionBench.locator("#expression .reduction-site").count(), 2);
  assert.equal(await reductionBench.locator("#type .reduction-site").count(), 0);
  await reductionBench.keyboard.press("Escape");
  assert.equal(await reductionBench.locator(".reduction-site").count(), 0);
  assert.deepEqual(JSON.parse(await reductionBench.locator("#syntax").inputValue()), repeated);
  await selectReduction("expression", "delta", ["arg", "fn"]);
  assert.equal(await reductionBench.locator("#name").textContent(), "value", "reducing a name must not navigate to it");
  const reducedOccurrence = JSON.parse(await reductionBench.locator("#syntax").inputValue());
  assert.equal(reducedOccurrence.fn.tag, "DefRef");
  assert.equal(reducedOccurrence.arg.fn.tag, "Lam");
  await selectReduction("expression", "beta", ["arg"]);
  const identity = { tag: "Lam", name: "x", domain: natural, body: { tag: "Var", name: "x" } };
  const nestedBeta = { tag: "App", fn: identity, arg: { tag: "App", fn: identity, arg: zero } };
  await reductionBench.locator("#syntax").fill(JSON.stringify(nestedBeta)); await settled(reductionBench);
  await reductionBench.locator("#check").click(); await settled(reductionBench);
  await reductionBench.locator("#beta-expression").click(); await settled(reductionBench);
  assert.equal(await reductionBench.locator("#expression .reduction-site").count(), 2);
  await reductionBench.locator('#expression [data-reduction-path=\'["arg"]\']').click(); await settled(reductionBench);
  const selectedInner = JSON.parse(await reductionBench.locator("#syntax").inputValue());
  assert.equal(selectedInner.fn.tag, "Lam");
  assert.deepEqual(selectedInner.arg, zero);
  await reductionBench.locator("#back").click(); await settled(reductionBench);
  assert.deepEqual(JSON.parse(await reductionBench.locator("#syntax").inputValue()), nestedBeta);
  await reductionBench.locator("#syntax").fill(JSON.stringify(repeated)); await settled(reductionBench);
  await reductionBench.locator("#check").click(); await settled(reductionBench);
  await reductionBench.locator("#delta-expression").click(); await settled(reductionBench);
  await reductionBench.locator("#unhighlight").click(); await settled(reductionBench);
  assert.equal(await reductionBench.locator(".reduction-site").count(), 0);
  await reductionBench.locator("#delta-expression").click(); await settled(reductionBench);
  await reductionBench.locator("#syntax").fill(JSON.stringify(one)); await settled(reductionBench);
  assert.equal(await reductionBench.locator(".reduction-site").count(), 0);
  await reductionBench.locator("#unhighlight").click(); await settled(reductionBench);
  assert.deepEqual(JSON.parse(await reductionBench.locator("#syntax").inputValue()), one);
  assert.equal(await reductionBench.locator("[data-reduction]:enabled").count(), 0);
  const polymorphic = { tag: "App", fn: { tag: "App",
    fn: { tag: "LApp", fn: { tag: "DefRef", name: "cubical_paths__poly" }, level: 0 },
    arg: natural }, arg: zero };
  await reductionBench.locator("#syntax").fill(JSON.stringify(polymorphic));
  await reductionBench.locator("#check").click(); await settled(reductionBench);
  await reductionBench.locator("#delta-expression").click();
  const polySite = reductionBench.locator('#expression [data-name="poly"]');
  assert.match(await polySite.getAttribute("class"), /reduction-site/);
  assert.deepEqual(JSON.parse(await polySite.getAttribute("data-reduction-path")), ["fn", "fn", "fn"]);
  await polySite.click(); await settled(reductionBench);
  assert.equal(JSON.parse(await reductionBench.locator("#syntax").inputValue()).fn.fn.fn.tag, "LLam");
  await reductionBench.close();
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`import primes;
    use unat;
    simp_rule unat_add_zero;
    def frozen(n : UNat) : n + 0 = n { simp; }
  `);
  await page.locator("#check").click(); await idle();
  await page.locator('#read-source button[data-name="simp"]').click(); await inspected("simp");
  assert.equal(await page.locator("#rewrite-trace button").count(),1);
  await page.locator("#rewrite-trace button").click(); await inspected("simp step 1");
  await page.locator("#back").click(); await inspected("simp");
  assert.equal(await page.locator("#freeze-simp").isVisible(),true);
  await page.locator("#freeze-simp").click(); await idle();
  assert.match(await page.locator("#editor").inputValue(),/simp only \[unat_add_zero\];/);
  assert.equal(await page.locator("#diagnostic").isVisible(),false);
  if(!await page.locator("#editor").isVisible()) await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`import unat;
    def generic_calc(U < UU0, x : UNat) : x = x {
      calc { x = x by refl(x); }
    }
    def generic_simp(U < UU0, f : UNat -> UNat, n : UNat, h : f(n) = n) : f(n) = n {
      simp [h];
    }`);
  await page.locator("#check").click(); await idle();
  await page.locator('#read-source button[data-name="calc"]').click(); await inspected("calc");
  assert.match(await page.locator("#kernel-type").textContent(),/=/);
  await page.locator('#read-source button[data-name="by"]').click(); await inspected("calc step 1");
  await page.locator('#read-source button[data-name="simp"]').click(); await inspected("simp");
  assert.equal(await page.locator("#rewrite-trace button").count(),1);
  // One check covers every level, so a generic proof is offered the edit too.
  assert.equal(await page.locator("#freeze-simp").isVisible(),true);
  const genericTransfer=await page.evaluate(async()=>{
    const [{default:createCubical},{CubicalProgram},{saveWorkbenchTransfer}]=await Promise.all([
      import("/dist/cubical.mjs"),import("/cubical-program.mjs"),import("/workbench-transfer.mjs")]);
    const source=`import primes; use unat;
      def generic(U < UU0, n : UNat) : n + 0 = n {
        calc { n + 0 = n by unat_add_zero(n); }
      }`;
    // A module the archive does not hold, such as unat, is read as missing;
    // the program then loads unat's bundled source.
    const program=new CubicalProgram(await createCubical(),async name=>{
      const response=await fetch(`/archive/first-library/${name}.cubist`);
      return response.ok?response.text():null;
    });
    try {
      const result=await program.check(source,"browser_generic_calc");
      const offset=source.indexOf("by unat_add_zero");
      const step=result.links.find(link=>link.start===offset&&link.role==="calculation step");
      return saveWorkbenchTransfer(program.export(step.binding));
    } finally {program.dispose();}
  });
  await page.goto(`${base}/workbench.html?transfer=${genericTransfer}`);
  await page.waitForFunction(()=>document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  assert.equal(await page.locator("#name").textContent(),"calc step 1");
  assert.match(await page.locator("#type").textContent(),/=/);
  const sharedTransfer=await page.evaluate(async()=>{
    const [{default:createCubical},{CubicalProgram},{saveWorkbenchTransfer}]=await Promise.all([
      import("/dist/cubical.mjs"),import("/cubical-program.mjs"),import("/workbench-transfer.mjs")]);
    let source="import unat; use unat; def shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 := A;";
    for(let i=1;i<=28;i++)source+=`let T${i} := F(T${i-1},T${i-1});`;
    source+="let h : forall x : T28. x = x { intro x; exact path i => x; } rfl; }";
    const program=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");});
    try {
      const result=await program.check(source,"browser_shared_inspection");
      const h=result.links.find(link=>link.name==="h");
      return saveWorkbenchTransfer(program.export(h.binding));
    } finally {program.dispose();}
  });
  await page.goto(`${base}/workbench.html?transfer=${sharedTransfer}`);
  await page.waitForFunction(()=>document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  assert.match(await page.locator("#syntax").inputValue(),/Raw syntax exceeds the display limit/);
  assert.equal(await page.locator("#check").isDisabled(),true);
  assert.ok((await page.locator("#expression").textContent()).length>0);
  // A page's imports resolve by where its source lives, as the CLI checks it:
  // the library is self-contained, so on a library page importing an archive
  // module leaves the check incomplete, while an archive proof, such as the
  // default Euclid page, may import the library.
  // The page keeps an edited draft across visits, so each edit starts from
  // the repository's source.
  const statusAfterImport = async (proof, root, header) => {
    const original = await (await page.request.get(`${base}/${root}/${proof}.cubist`)).text();
    await page.goto(`${base}/proof.html?proof=${proof}`); await idle();
    if (!await page.locator("#editor").isVisible()) await page.locator("#edit-mode").click();
    await page.locator("#editor").fill(`${header}\n${original}`);
    await page.locator("#check").click(); await idle();
    return page.locator("#status").textContent();
  };
  assert.match(await statusAfterImport("universe_automorphisms", "library", "import classical;"), /check incomplete/);
  assert.match(await statusAfterImport("euclid", "archive/first-library", "import classical_axioms;"), /· checked/);
  assert.match(await statusAfterImport("euclid", "archive/first-library", "import classical;"), /· checked/);
  assert.match(await statusAfterImport("universe_automorphisms", "library", "import unat;"), /· checked/);
  // A check started from Edit shows the checked source, revealing the named
  // declaration; editing that goes on during the check stays open instead.
  const editDuringCheck = async typed => {
    await page.goto(`${base}/proof.html?proof=euclid&name=euclid`); await idle();
    await page.locator("#edit-mode").click();
    await page.locator("#editor").fill(`${await page.locator("#editor").inputValue()}\n// edited before the check`);
    await page.locator("#check").click();
    await page.waitForFunction(() => document.querySelector("#status")?.textContent === "Checking…");
    if (typed) await page.locator("#editor").evaluate(editor => {
      editor.value += "\n// typed during the check";
      editor.dispatchEvent(new Event("input", { bubbles: true }));
    });
    await idle(); await inspected("euclid");
    return page.locator("#editor").isVisible();
  };
  assert.equal(await editDuringCheck(false), false);
  assert.match(await page.locator("#read-source .source-line.active").textContent(), /def euclid/);
  assert.equal(await editDuringCheck(true), true);
  assert.match(await page.locator("#dirty").textContent(), /not checked/);
  assert.deepEqual(errors, []);
  console.log("PASS cubical inspector: folding, navigation, simp trace/freeze, generic transfer, bounded raw syntax, workbench editing, and imports by place");
});
