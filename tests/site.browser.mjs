// Exercise the published static artifact (or a live URL), without serve.py's
// development-only import rewriting and version endpoint.
import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { chromium } from "playwright";

let base = process.argv[2];
let server;
let browser;
try {
  if (!base) {
    server = spawn("python3", ["-u", "-m", "http.server", "0", "--bind", "127.0.0.1", "--directory", "build/site"],
      { stdio: ["ignore", "pipe", "pipe"] });
    server.stderr.resume();
    base = await new Promise((resolve, reject) => {
      let output = "";
      const timeout = setTimeout(() => reject(new Error("Static test server did not start")), 10000);
      server.once("error", reject);
      server.once("exit", code => { clearTimeout(timeout); reject(new Error(`Server exited: ${code}`)); });
      server.stdout.on("data", data => {
        output += data;
        const match = output.match(/port (\d+)/);
        if (match) { clearTimeout(timeout); resolve(`http://127.0.0.1:${match[1]}/`); }
      });
    });
  }
  if (!base.endsWith("/")) base += "/";
  browser = await chromium.launch({ headless: true });
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
  assert.equal(await page.locator(".proof-card").count(), 8);
  for (const width of [1440, 390, 320]) {
    await page.setViewportSize({ width, height: 900 });
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth > innerWidth), false);
  }
  await page.setViewportSize({ width: 1440, height: 1000 });
  const version = await page.request.get(new URL("mathscript-version", base).href);
  assert.equal(version.status(), 200);
  assert.match((await version.json()).version, /^[a-f0-9]{64}$/);
  console.log("PASS static landing, repository link, mobile layout, build version");
  for (const [proof, name, backend] of [["euclid", "euclid", "cubical"], ["cubical_paths", "reverse_twice", "cubical"], ["f4_galois_correspondence", "f4_galois_correspondence", "cubical"]]) {
    await page.goto(new URL(`proof.html?proof=${proof}&name=${name}&backend=${backend}`, base).href);
    await page.waitForFunction(() => !document.querySelector("#check").disabled && document.querySelector("#check-loader").hidden);
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.equal(await page.locator("#inspect-name").textContent(), name);
    await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
    assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /unavailable/);
    if (proof === "euclid") {
      // A line number shows the goal at that proof statement and the names in scope.
      await page.locator('.source-line[data-line="8"] .line-number').click();
      assert.equal(await page.locator("#inspect-name").textContent(), "Goal at line 8");
      assert.match(await page.locator("#inspect-type").textContent(), /exists p : Nat\. Prime\(p\) and n < p/);
      assert.match(await page.locator("#locals").textContent(), /n\s*Nat/);
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
  assert.equal((await inspector.locator("#kernel-type").textContent()).trim(), "Nat");
  await page.locator("#tour-numbers").scrollIntoViewIfNeeded();
  await page.waitForSelector("#tour-numbers .example-token");
  assert.match(await page.locator("#tour-numbers .example-bar span").first().textContent(), /evaluate at line 7: 6/);
  // An imported module's name opens the module in the workspace.
  const moduleLink = page.locator("#tour-numbers a.example-module").first();
  assert.equal(await moduleLink.textContent(), "naturals");
  assert.match(await moduleLink.getAttribute("href"), /proof\.html\?proof=naturals$/);
  // 0 is the constructor itself, not notation.
  assert.deepEqual(await page.locator("#tour-numbers pre code").first().evaluate(code =>
    [...code.querySelectorAll("*")].filter(node => node.textContent === "0").map(node => node.classList.contains("macro"))), [false]);
  // A numeral's expansion shows at once on hover.
  await page.locator('#tour-numbers [data-tip*="succ("]').first().hover();
  assert.match(await page.locator(".token-tip:not([hidden])").textContent(), /^\d+ expands to succ\(/);
  assert.match(await page.locator(".drawer-head a").getAttribute("href"), /proof\.html\?example=1#source=/);
  console.log("PASS reference examples: in-browser checking, linked names, embedded kernel inspector, evaluate results, instant macro tips");
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
  await page.goto(new URL("reference/types.html", base).href);
  await page.locator("#values .example-bar .repl-fork").first().click();
  await page.waitForFunction(() => [...document.querySelectorAll(".repl-dock .repl-result")].some(line => line.textContent === "seven : Nat"));
  await enter("evaluate seven");
  assert.deepEqual(await lastResults(1), ["7"]);
  console.log("PASS examples open in the REPL bar with their definitions");
  // A read-only REPL transcript forks into the REPL bar, with the example
  // before it loaded, and can be continued there.
  await page.goto(new URL("reference/first-proof.html", base).href);
  await page.locator(".repl-fork", { hasText: "Fork into REPL" }).nth(1).click();
  await page.waitForFunction(() => document.querySelectorAll(".repl-dock .repl-result").length >= 4 && !document.querySelector(".repl-form.busy"));
  await enter("evaluate exists_greater_number(10)");
  assert.deepEqual(await lastResults(2), ["(6, 0, refl(6))", "(11, 0, refl(11))"]);
  console.log("PASS read-only REPL transcripts fork into the REPL bar");
  await page.goto(new URL("proof.html?proof=naturals", base).href);
  await page.locator("#read-source .reference").first().waitFor();
  assert.equal(await page.locator("#proof-title").textContent(), "Library: naturals");
  assert.equal(await page.locator("#archive-note").isHidden(), true);
  // The console under a proof has the proof's names loaded.
  await enter("typeof nat_add_comm;");
  await enter("let y := add(2, 3);");
  await enter("y");
  assert.deepEqual(await lastResults(3), ["forall x : Nat. forall y : Nat. x + y = y + x", "y : Nat", "5"]);
  console.log("PASS library module in the workspace, with its console");
  await page.goto(new URL("repl.html", base).href);
  for (const text of ["let x := 7;", "typeof x;", "evaluate x;", "def wrong : x = 8 {\n  exact refl(7);\n}"]) await enter(text);
  assert.deepEqual(await lastResults(4), ["x : Nat", "Nat", "7", "Type mismatch: found 7 = 7, expected x = 8."]);
  console.log("PASS REPL page: let, typeof, evaluate, rejected entries");
  // The first proof's Elaboration panel opens on demand and shows every
  // declaration, down to the kernel's opcodes, with a link for more info.
  await page.goto(new URL("reference/first-proof.html#elaboration", base).href);
  const elaboration = page.locator("#elaboration details.elaboration");
  await elaboration.locator("summary").click();
  await elaboration.locator(".elaboration-declaration").nth(2).waitFor();
  assert.equal(await elaboration.locator(".elaboration-declaration").count(), 3);
  assert.match(await elaboration.textContent(), /intro n;\s*⊢ forall n : Nat\. exists m : Nat\. lt\(n, m\)\s*builds fun \(n : Nat\) => \?/);
  assert.match(await elaboration.getByRole("link", { name: "For more info" }).first().getAttribute("href"), /kernel\.html$/);
  // The kernel's check as a THTH-style forward derivation, with comments.
  const derivation = elaboration.locator(".derivation").first();
  assert.match(await derivation.textContent(), /\/\/ \{\} ⊢ Nat : U0\s*1 NatForm\(\)/);
  assert.match(await derivation.textContent(), /\/\/ \{n : Nat\}\s*2 CtxExt\(1\)/);
  assert.ok(await elaboration.locator(".derivation-scaffold").count() > 0);
  await page.goto(new URL("kernel.html", base).href);
  assert.equal(await page.locator("#opcodes tbody tr").count(), 42);
  console.log("PASS elaboration panel and the kernel reference outline");
  await page.goto(new URL("workbench.html", base).href);
  await page.waitForFunction(() => document.querySelector("#status").textContent.includes("checked"));
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  assert.equal(await page.locator("#name").textContent(), "example");
  assert.deepEqual(errors, []);
  console.log(`PASS static kernel workbench (${base})`);
} finally {
  await browser?.close();
  server?.kill();
}
