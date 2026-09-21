import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { chromium } from "playwright";
const server = spawn("python3", ["tools/serve.py", "--port", "0"], { stdio: ["ignore", "pipe", "pipe"] });
server.stderr.resume();
let browser;
try {
  const port = await new Promise((resolve, reject) => {
    let output = "";
    const timer = setTimeout(() => reject(new Error("Server did not start")), 10000);
    server.once("error", reject);
    server.once("exit", code => { clearTimeout(timer); reject(new Error(`Server exited ${code}`)); });
    server.stdout.on("data", data => {
      output += data;
      const match = output.match(/127\.0\.0\.1:(\d+)\//);
      if (match) { clearTimeout(timer); resolve(match[1]); }
    });
  });
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors = []; page.on("pageerror", error => errors.push(error.message));
  const idle = async () => {
    try {
      await page.waitForFunction(() => !document.querySelector("#check").disabled && document.querySelector("#check-loader").hidden);
    } catch (error) {
      console.error(await page.locator("#diagnostic").textContent(), errors); throw error;
    }
  };
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=euclid&name=euclid`);
  await idle();
  assert.equal(await page.locator("#kernel-backend").inputValue(), "cubical");
  assert.match(await page.locator("#check-detail").textContent(), /^[\d,]+ kernel steps\n[\d,]+ of [\d,]+ declarations processed/);
  assert.match(await page.locator("#status").textContent(), /Cubical C · checked/);
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  for (const id of ["share-syntax", "reuse-checks", "compact-paths"]) {
    assert.equal(await page.locator(`#${id}`).isVisible(), true);
    assert.equal(await page.locator(`#${id}`).isChecked(), true);
  }
  await page.locator("#reuse-checks").uncheck(); await idle();
  assert.match(await page.locator("#status").textContent(), /Cubical C · checked/);
  await page.locator("#reuse-checks").check(); await idle();
  assert.match(await page.locator("#kernel-view-note").textContent(), /Native cubical C/);
  await page.locator('.source-line [data-name="prime_divisor_exists"]').first().click();
  await idle();
  await page.locator("#view-source").click();
  await idle();
  assert.match(page.url(), /proof=primes/);
  await page.locator("#back").click(); await idle();
  assert.match(page.url(), /proof=euclid/);
  await page.locator('.source-line [data-name="n"]').first().click(); await idle();
  assert.ok(await page.locator("#kernel-context-list li").count());
  const opened = page.waitForEvent("popup");
  await page.locator("#open-kernel-type").click();
  const workbench = await opened;
  await workbench.waitForURL(/cubical-workbench\.html/);
  await workbench.waitForFunction(() => document.querySelector("#status").textContent.startsWith("Cubical C checked"));
  assert.ok(await workbench.locator("#context .context-entry").count());
  assert.match(await workbench.locator("#source-back").getAttribute("href"), /proof\.html/);
  await workbench.locator("details summary").click();
  await workbench.locator("#syntax").fill('{"tag":"Var","name":"not_in_context"}');
  assert.equal(await workbench.locator("#normalize").isDisabled(), true);
  await workbench.locator("#check").click();
  assert.equal(await workbench.locator("#diagnostic").isVisible(), true);
  await workbench.close();
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("theorem wrong : 0 = 1 { exact refl(0); }");
  await page.locator("#check").click(); await idle();
  assert.match(await page.locator("#status").textContent(), /migration incomplete/);
  assert.match(await page.locator("#result").textContent(), /Not checked wrong/);
  assert.equal(await page.locator("#kernel-details").isVisible(), false);
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=cubical_paths&name=reverse_twice`);
  await idle();
  assert.match(await page.locator("#status").textContent(), /Cubical C · checked/);
  assert.equal(await page.locator("#inspect-name").textContent(), "reverse_twice");
  // Select p inside the interval body, rather than its declaration outside it.
  await page.locator('.source-line [data-name="p"]').nth(1).click();
  await idle();
  assert.match(await page.locator("#kernel-context-list").textContent(), /Interval coordinates/);
  const intervalOpened = page.waitForEvent("popup");
  await page.locator("#open-kernel-expression").click();
  const intervalWorkbench = await intervalOpened;
  await intervalWorkbench.waitForFunction(() => document.querySelector("#status").textContent.startsWith("Cubical C checked"));
  assert.match(await intervalWorkbench.locator("#context").textContent(), /Interval coordinates/);
  await intervalWorkbench.close();
  await page.goto(`http://127.0.0.1:${port}/benchmark.html`);
  await page.waitForFunction(() => document.querySelector("#status").textContent.startsWith("Completed"));
  assert.ok(await page.locator("#entries tr").count() > 2000);
  assert.equal(await page.locator("#limit-ms").inputValue(), "100");
  await page.locator("#run").click();
  await page.waitForFunction(() => document.querySelectorAll("#entries tr").length > 10);
  assert.equal(await page.locator("#cancel").isDisabled(), false);
  await page.locator("#cancel").click();
  assert.match(await page.locator("#status").textContent(), /Cancelled/);
  await page.locator("#run").click();
  await page.waitForFunction(() => document.querySelector("#status").textContent.startsWith("Completed"), null, { timeout: 180000 });
  assert.ok(await page.locator("#entries tr").count() > 2000);
  assert.equal(await page.locator("#run").isDisabled(), false);
  assert.equal(await page.locator("#download").isDisabled(), false);
  console.log("Browser benchmark:", await page.locator("#counts").innerText());
  assert.match(await page.locator("#counts").innerText(), /within 100 ms/);
  await page.locator("#category").selectOption("checked");
  const times = await page.locator("#entries tr td:nth-child(3)").allTextContents();
  const milliseconds = times.map(text => Number.parseFloat(text.replaceAll(",", "")));
  assert.ok(milliseconds.every((time, index) => index === 0 || milliseconds[index - 1] >= time));
  await page.locator("#category").selectOption("failed");
  assert.equal(await page.locator('#entries tr:not([data-category="failed"])').count(), 0);
  assert.deepEqual(errors, []);
  console.log("PASS native proof/workbench flows and browser corpus benchmark with cancellation and live results");
} finally { await browser?.close(); server.kill(); }
