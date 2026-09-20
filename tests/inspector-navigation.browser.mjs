import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright";

const server = spawn("python3", [fileURLToPath(new URL("../tools/serve.py", import.meta.url)), "--port", "0"],
  { stdio: ["ignore", "pipe", "pipe"] });
server.stderr.resume();
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
  const page = await browser.newPage();
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  const inspected = (target, name) => target.waitForFunction(name =>
    document.querySelector("#inspect-name").textContent === name &&
    !document.querySelector("#kernel-view").disabled, name);
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=euclid`);
  await inspected(page, "euclid");
  assert.equal(await page.locator("#kernel-group-binders").isChecked(), false);
  for (const name of ["hp", "hd"]) {
    await page.locator(`.source-line [data-name="${name}"]`).first().click();
    await inspected(page, name);
    assert.equal(await page.locator("#kernel-type").textContent(), name === "hp"
      ? "Prime(add(2,i))" : "Divides(add(2,i),succ(factorial(n)))");
    assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /unavailable/);
    assert.equal(await page.locator('#kernel-context-list [data-name="i"]').count() > 0, true);
    if (name === "hd") {
      assert.equal(await page.locator('#kernel-context-list > [data-name="hp"] .kernel-context-type').textContent(), "Prime(add(2,i))");
      assert.equal(await page.locator('#kernel-context-list > [data-name="hp"] [data-name="Prime"]').count(), 1);
    }
  }
  // Import navigation preserves both the selected local and its prior history.
  await page.locator('.source-line a[data-name="primes"]').click();
  await page.waitForFunction(() => !document.querySelector("#back").hidden &&
    !document.querySelector("#kernel-view").disabled);
  await page.locator("#back").click();
  await inspected(page, "hd");
  assert.equal(new URL(page.url()).searchParams.get("proof"), "euclid");
  await page.locator("#back").click();
  await inspected(page, "hp");

  // Imported definition source returns to its inspection, then the local.
  await page.locator('#kernel-type [data-name="Prime"]').click();
  await inspected(page, "Prime");
  await page.locator("#view-source").click();
  await inspected(page, "Prime");
  assert.equal(new URL(page.url()).searchParams.get("proof"), "primes");
  await page.locator("#back").click();
  await inspected(page, "Prime");
  assert.equal(new URL(page.url()).searchParams.get("proof"), "euclid");
  await page.locator("#back").click();
  await inspected(page, "hp");

  await page.locator('.source-line [data-name="hd"]').first().click();
  await inspected(page, "hd");
  const popup = page.waitForEvent("popup");
  await page.locator("#open-kernel-expression").click();
  const workbench = await popup;
  workbench.on("pageerror", error => errors.push(error.message));
  await workbench.locator("#back-mathscript").waitFor({ state: "visible" });
  assert.equal(await workbench.locator("#expression").textContent(), "hd");
  assert.equal(await workbench.locator("#active-name").textContent(), "hd");
  assert.deepEqual(await workbench.locator("#kernel-context > div").evaluateAll(rows => rows.map(row => row.dataset.name)), ["n", "i", "hp", "hd"]);
  assert.match(await workbench.locator('#kernel-context > [data-name="hp"]').textContent(), /hp : \(Prime .* i\)\)/);
  assert.match(await workbench.locator("#type").textContent(), /Divides.*factorial n/);
  await workbench.locator("#clear").click();
  assert.equal(await workbench.locator(".term.selected").count(), 0);
  assert.equal(await workbench.locator("#expression").textContent(), "hd");
  await workbench.locator("#back-mathscript").click();
  await inspected(workbench, "hd");
  assert.equal(await workbench.locator("#kernel-type").textContent(), "Divides(add(2,i),succ(factorial(n)))");
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=field_logic&name=FieldExists`);
  await inspected(page, "FieldExists");
  const axiomPopup = page.waitForEvent("popup");
  await page.locator("#open-kernel-expression").click();
  const axiomWorkbench = await axiomPopup;
  await axiomWorkbench.locator("#back-mathscript").waitFor({ state: "visible" });
  assert.match(await axiomWorkbench.locator("#expression").textContent(), /Truncate/);
  assert.equal(await axiomWorkbench.locator("#kernel-context").textContent(), "Empty context");
  await axiomWorkbench.locator('#expression [data-declaration="lib_Trunc"]').click();
  await axiomWorkbench.waitForFunction(() => document.querySelector("#active-name").textContent === "Truncate");
  assert.equal(await axiomWorkbench.locator("#object-kind").textContent(), "explicit axiom");
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=basics`);
  await page.waitForFunction(() => !document.querySelector("#check").disabled && document.querySelector("#check-loader").hidden);
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("def Z = Nat or Nat; def identity = fun (y : Z) => y;");
  await page.locator("#check").click();
  await inspected(page, "identity");
  await page.locator('.source-line [data-name="y"]').first().click();
  await inspected(page, "y");
  const variablePopup = page.waitForEvent("popup");
  await page.locator("#open-kernel-expression").click();
  const variableWorkbench = await variablePopup;
  await variableWorkbench.locator("#back-mathscript").waitFor({ state: "visible" });
  assert.equal(await variableWorkbench.locator("#kernel-context").textContent(), "y : Z");
  await variableWorkbench.locator('#kernel-context [data-declaration="Z"]').click();
  await variableWorkbench.waitForFunction(() => document.querySelector("#active-name").textContent === "Z");
  assert.deepEqual(errors, []);
  console.log("Hypothesis rendering, import/source Back, restored history, and workbench return passed.");
} finally {
  await browser?.close();
  server.kill();
}
