import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright";

const server = spawn("python3", [fileURLToPath(new URL("../tools/serve.py", import.meta.url)), "--port", "0"],
  { stdio: ["ignore", "pipe", "pipe"] });
let browser;
try {
  const port = await new Promise((resolve, reject) => {
    let output = "";
    const timer = setTimeout(() => reject(new Error("Test server did not start")), 10000);
    server.once("error", reject);
    server.once("exit", code => { clearTimeout(timer); reject(new Error(`Test server exited: ${code}`)); });
    server.stdout.on("data", data => {
      output += data;
      const match = output.match(/127\.0\.0\.1:(\d+)\//);
      if (match) { clearTimeout(timer); resolve(match[1]); }
    });
  });
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage({ viewport: { width: 1440, height: 1050 } });
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  const idle = () => page.waitForFunction(() => !document.querySelector("#check").disabled &&
    document.querySelector("#check-loader").hidden);
  const inspect = async name => {
    await page.locator(`#definitions [data-name="${name}"]`).click();
    await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
    await page.locator("#kernel-details > summary").click();
  };
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=euclid`);
  await idle();
  await inspect("InfinitelyManyPrimes");
  const expression = "forall n : Nat, exists p : Nat, Prime(p) and n < p";
  assert.equal(await page.locator("#kernel-view").inputValue(), "mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), expression);
  await page.locator("#kernel-view").selectOption("raw");
  assert.notEqual(await page.locator("#kernel-expression").innerText(), expression);
  assert.match(await page.locator("#kernel-view-note").innerText(), /Raw checked kernel/);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), expression);
  await inspect("euclid");
  assert.equal(await page.locator("#kernel-type").innerText(), "InfinitelyManyPrimes");
  assert.equal(await page.locator("#kernel-expression").innerText(), "euclid");
  await inspect("Prime");
  assert.match(await page.locator("#kernel-expression").innerText(), /^fun \(p : Nat\) => .*Divides/);
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("def InfinitelyManyPrimes : Void { exact tt; }");
  await page.locator("#check").click();
  await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), true);
  await inspect("InfinitelyManyPrimes");
  assert.equal(await page.locator("#kernel-expression").innerText(), expression);

  // Raw mode retains the existing explicit tree-budget expansion.
  const deep = Array.from({ length: 50 }, (_, i) => `forall n${i} : Nat, `).join("") + "Nat";
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`def Deep = ${deep};`);
  await page.locator("#check").click();
  await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await inspect("Deep");
  assert.equal(await page.locator("#kernel-expression").innerText(), deep);
  await page.locator("#kernel-view").selectOption("raw");
  assert.equal(await page.locator("#expand-kernel").isVisible(), true);
  await page.locator("#expand-kernel").click();
  await idle();
  assert.equal(await page.locator("#expand-kernel").isVisible(), false);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), deep);
  assert.deepEqual(errors, []);
  console.log("Folded MathScript, raw kernel, imports, checked snapshots, and full expansion passed.");
} finally {
  await browser?.close();
  server.kill();
}
