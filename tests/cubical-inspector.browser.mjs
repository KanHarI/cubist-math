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
  const inspected = name => page.waitForFunction(name =>
    document.querySelector("#inspect-name").textContent === name &&
    !document.querySelector("#kernel-view").disabled, name);
  const openProof = async (proof, name) => {
    await page.goto(`http://127.0.0.1:${port}/proof.html?proof=${proof}&name=${name}`);
    await idle(); await inspected(name);
  };
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
  assert.equal(await page.locator("#kernel-type").textContent(), "Nat");
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
  await workbench.waitForFunction(() => document.querySelector("#status").textContent.startsWith("Cubical C checked"));
  assert.equal(await workbench.locator("#expression").textContent(), "Divides(succ(succ(i)),m)");
  assert.match(await workbench.locator("#context").textContent(), /n :Nat/);
  await workbench.locator("#fold-names").uncheck();
  assert.match(await workbench.locator("#expression").textContent(), /prime_divisor_exists/);
  await workbench.locator("#fold-names").check();
  await workbench.locator('#expression [data-name="i"]').click();
  await workbench.waitForFunction(() => document.querySelector("#name").textContent === "i");
  await workbench.locator("#back").click();
  await workbench.locator("details summary").click();
  // The exported type is itself a U0 term: replace it with Nat and recheck.
  await workbench.locator("#syntax").fill('{"tag":"Nat"}');
  await workbench.locator("#check").click();
  assert.equal(await workbench.locator("#expression").textContent(), "Nat");
  await workbench.locator("#syntax").fill('{"tag":"Var","name":"missing"}');
  await workbench.locator("#check").click();
  assert.equal(await workbench.locator("#diagnostic").isVisible(), true);
  assert.equal(await workbench.locator("#normalize").isDisabled(), true);
  await workbench.close();

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
  const derived = page.locator('#kernel-expression [data-name="ua[U1]"]');
  await derived.click(); await inspected("ua[U1]");
  assert.match(await page.locator("#inspect-description").textContent(), /introduces no axiom/);

  await openProof("field_logic", "FieldExists");
  assert.match(await page.locator("#kernel-expression").textContent(), /‖/);
  await page.locator("#kernel-truncation-sugar").uncheck();
  assert.match(await page.locator("#kernel-expression").textContent(), /Truncate/);
  await page.locator('#kernel-expression [data-name="Truncate(U1)"]').click();
  await inspected("Truncate(U1)");

  await openProof("cubical_paths", "reverse_twice");
  await page.locator('.source-line').filter({ hasText: "fun (i : Interval) => at(p," }).locator('[data-name="p"]').click();
  await inspected("p");
  assert.match(await page.locator("#kernel-context-list").textContent(), /Interval coordinates/);
  await page.setViewportSize({ width: 600, height: 900 });
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
  assert.deepEqual(errors, []);
  console.log("PASS cubical inspector: folding, names, navigation, reading controls, axiom links, and workbench editing");
} finally { await browser?.close(); server.kill(); }
