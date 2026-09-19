import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { readFile } from "node:fs/promises";
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
    assert.equal(await page.locator("#kernel-details").evaluate(node => node.open), true);
  };
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=euclid`);
  await idle();
  for (const name of ["nat_le_total", "prime_divisor_exists", "factorial"]) {
    await inspect(name);
    assert.equal(await page.locator("#kernel-type math").count(), 1, name);
    assert.equal(await page.locator("#kernel-expression math").count(), 1, name);
    assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /could not|unavailable/);
    assert.doesNotMatch(await page.locator("#kernel-type").textContent(), /#[0-9]|…/);
    if (name === "nat_le_total") assert.equal(await page.locator('#kernel-type [data-name="le"]').count(), 2);
    if (name === "prime_divisor_exists") assert.equal(await page.locator('#kernel-type [data-name="Divides"]').count(), 1);
    if (name === "factorial") {
      assert.match(await page.locator("#kernel-expression").textContent(), /λn\.nat\.elim\[k,h\]\(1,mul\(succ\(k\),h\),n\)/);
      assert.equal(await page.locator('#kernel-expression [data-name="mul"]').count(), 1);
      await page.locator("#kernel-expression").scrollIntoViewIfNeeded();
      await page.screenshot({ path: "/private/tmp/thth-factorial-folded.png", fullPage: true });
      await page.locator('#kernel-expression [data-name="mul"]').click();
      await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "mul" && !document.querySelector("#kernel-view").disabled);
      // mul uses an unsupported primitive call in its source folding plan;
      // its actual checked kernel AST must still receive mathematical notation.
      assert.equal(await page.locator("#kernel-expression math").count(), 1);
    }
  }
  await inspect("InfinitelyManyPrimes");
  const expression = "forall n : Nat, exists p : Nat, Prime(p) and n < p";
  assert.equal(await page.locator("#kernel-view").inputValue(), "notation");
  assert.equal(await page.locator("#kernel-expression math").count(), 1);
  assert.equal(await page.locator("#kernel-expression msub > mo").allTextContents().then(a => a.join("")), "ΠΣ");
  assert.match(await page.locator("#kernel-expression").textContent(), /Prime\(p\)×isLt\(n,p\)/);
  assert.match(await page.locator("#kernel-view-note").textContent(), /kernel verified its definitional equality/);
  assert.equal(await page.locator('#kernel-expression [data-name="p"]').count(), 0);
  await page.screenshot({ path: "/private/tmp/thth-kernel-folded-math.png", fullPage: true });
  const downloadEvent = page.waitForEvent("download");
  await page.locator("#export-folding").click();
  const download = await downloadEvent;
  const certificate = JSON.parse(await readFile(await download.path(), "utf8"));
  assert.equal(certificate.folding.binding, "InfinitelyManyPrimes");
  assert.ok(certificate.folding.verified.expression.witness);
  assert.ok(certificate.steps.some(step => step.op === "Def"));

  const openWorkbench = async side => {
    const popup = page.waitForEvent("popup");
    await page.locator(`#open-kernel-${side}`).click();
    const workbench = await popup;
    workbench.on("pageerror", error => errors.push(error.message));
    await workbench.waitForURL(/index\.html/);
    await workbench.waitForFunction(() => document.querySelector("#active-name").textContent.includes("_folded_") &&
      document.querySelector("#status").textContent === "WASM ready");
    assert.equal(await workbench.locator("#error").isVisible(), false);
    assert.equal(await workbench.locator("#axioms").isChecked(), false);
    assert.equal(await workbench.locator("#used-axioms").textContent(), "None");
    return workbench;
  };
  const workbench = await openWorkbench("expression");
  assert.equal(await workbench.locator("#active-name").textContent(), "InfinitelyManyPrimes_folded_expression");
  await workbench.locator('#expression [data-declaration="Prime"]').click({ modifiers: ["Shift"] });
  await workbench.locator("#result-name").fill("expanded_prime");
  await workbench.locator("#unfold").click();
  await workbench.locator("#preview:not([hidden])").waitFor();
  assert.match(await workbench.locator("#preview-code").textContent(), /DefReducePointed/);
  await workbench.locator("#accept").click();
  await workbench.waitForFunction(() => document.querySelector("#active-name").textContent === "expanded_prime");
  await workbench.locator('#expression .term[data-path=""]').click({ position: { x: 2, y: 5 } });
  await workbench.locator("#pass").click();
  await workbench.locator("#preview:not([hidden])").waitFor();
  assert.match(await workbench.locator("#preview-code").textContent(), /BetaReduceGrossKnuth/);
  await workbench.locator("#accept").click();
  await workbench.waitForFunction(() => document.querySelector("#active-name").textContent === "expanded_prime_next");
  assert.equal(await workbench.locator("#used-axioms").textContent(), "None");
  await workbench.close();
  const typeWorkbench = await openWorkbench("type");
  assert.equal(await typeWorkbench.locator("#active-name").textContent(), "InfinitelyManyPrimes_folded_type");
  assert.equal(await typeWorkbench.locator("#expression").textContent(), "U0");
  await typeWorkbench.close();

  await page.locator('#kernel-expression [data-name="Prime"]').click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "Prime" && !document.querySelector("#kernel-view").disabled);
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=primes&name=Prime/);
  assert.equal(await page.locator("#kernel-details").evaluate(node => node.open), true);
  assert.equal(await page.locator('#kernel-expression [data-name="Divides"]').count(), 1);
  await page.locator("#view-source").click();
  await idle();
  assert.match(page.url(), /proof=primes&name=Prime/);
  assert.equal(await page.locator("#inspect-name").textContent(), "Prime");
  assert.match(await page.locator(".source-line.active").innerText(), /def Prime/);
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=euclid`);
  await idle();
  await inspect("InfinitelyManyPrimes");
  await page.locator("#kernel-view").selectOption("mathscript");
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
  assert.equal(await page.locator("#kernel-expression math").count(), 1);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.match(await page.locator("#kernel-expression").innerText(), /^fun \(p : Nat\) => .*Divides/);
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("def InfinitelyManyPrimes : Void { exact tt; }");
  await page.locator("#check").click();
  await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), true);
  await inspect("InfinitelyManyPrimes");
  assert.equal(await page.locator("#kernel-expression math").count(), 1);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), expression);

  // Raw mode retains the existing explicit tree-budget expansion.
  const deep = Array.from({ length: 50 }, (_, i) => `forall n${i} : Nat, `).join("") + "Nat";
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`def Deep = ${deep};`);
  await page.locator("#check").click();
  await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await inspect("Deep");
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), deep);
  await page.locator("#kernel-view").selectOption("raw");
  assert.equal(await page.locator("#expand-kernel").isVisible(), true);
  await page.locator("#expand-kernel").click();
  await idle();
  assert.equal(await page.locator("#expand-kernel").isVisible(), false);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), deep);

  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=classical_complex_inverses`);
  await idle();
  await inspect("classical_complex_nonzero_inverse");
  assert.equal(await page.locator("#kernel-type math").count(), 1);
  assert.equal(await page.locator("#kernel-type mtable > mtr").count(), 14);
  assert.equal(await page.locator('#kernel-type [data-name="ComplexUnit"]').count(), 1);
  assert.equal(await page.locator('#kernel-type [data-name="Complex"]').count(), 2);
  assert.equal(await page.locator('#kernel-type [data-name="complex_zero"]').count(), 1);
  assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /could not|unavailable|stored term is shown/);
  assert.doesNotMatch(await page.locator("#kernel-type").textContent(), /#[0-9]|…/);
  await page.locator("#kernel-type").scrollIntoViewIfNeeded();
  await page.screenshot({ path: "/private/tmp/thth-classical-inverse-folded.png", fullPage: true });
  assert.deepEqual(errors, []);
  console.log("Certified mathematical kernel view, definition/source navigation, workbench export/unfold/reduce, source/raw views, checked snapshots, and full expansion passed.");
} finally {
  await browser?.close();
  server.kill();
}
