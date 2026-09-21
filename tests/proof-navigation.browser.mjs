import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium, webkit } from "playwright";
import { proofChoices, proofTopics, proofsInTopic } from "../web/proof-library.mjs";
import { selectProof } from "./proof-navigation.mjs";

const server = spawn("python3", [fileURLToPath(new URL("../tools/serve.py", import.meta.url)), "--port", "0"],
  { stdio: ["ignore", "pipe", "pipe"] });
// Drain request logs: a full stderr pipe can block the local HTTP server.
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
  browser = await (process.env.THTH_BROWSER === "webkit" ? webkit : chromium).launch({ headless: true });
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  const idle = () => page.waitForFunction(() => !document.querySelector("#check").disabled && document.querySelector("#check-loader").hidden);
  const base = `http://127.0.0.1:${port}`;
  await page.goto(`${base}/proof.html?proof=euclid`);
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "arithmetic");
  assert.equal(await page.locator("#proof-picker").inputValue(), "euclid");
  const initialURL = page.url(), source = await page.locator("#editor").inputValue();
  assert.equal(await page.locator("#proof-topic option").count(), proofTopics.length);
  // Inspect every submenu without compiling the library or leaving the current proof.
  for (const topic of proofTopics) {
    await page.locator("#proof-topic").selectOption(topic.id);
    assert.deepEqual(await page.locator("#proof-picker option:not([disabled])").evaluateAll(options => options.map(o => o.value)), proofsInTopic(topic.id).map(p => p.id));
    assert.equal(page.url(), initialURL);
    assert.equal(await page.locator("#editor").inputValue(), source);
  }
  await page.locator("#proof-topic").selectOption("basic-logic");
  assert.equal(await page.locator("#proof-picker").inputValue(), "");
  await page.locator("#proof-picker").selectOption("basics");
  await page.waitForURL("**/proof.html?proof=basics");
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "basic-logic");
  assert.match(await page.locator("#result").textContent(), /copy_of_two/);
  // Browsing topics does not throw away draft edits; selecting a proof saves them.
  await page.locator("#edit-mode").click();
  const draft = (await page.locator("#editor").inputValue()) + "\n// topic navigation draft\n";
  await page.locator("#editor").fill(draft);
  await page.locator("#proof-topic").selectOption("arithmetic");
  assert.equal(await page.locator("#editor").inputValue(), draft);
  await selectProof(page, "euclid");
  await page.waitForURL("**/proof.html?proof=euclid");
  await idle();
  await page.goBack();
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "basic-logic");
  assert.equal(await page.locator("#proof-picker").inputValue(), "basics");
  assert.equal(await page.locator("#editor").inputValue(), draft);
  await page.goForward();
  await idle();
  assert.equal(await page.locator("#proof-picker").inputValue(), "euclid");
  // Imported source navigation still initializes the destination's topic.
  await page.locator('#read-source a[data-name="primes"]').click();
  await page.waitForURL("**/proof.html?proof=primes*");
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "arithmetic");
  assert.equal(await page.locator("#proof-picker").inputValue(), "primes");
  await page.goBack();
  await idle();
  assert.equal(await page.locator("#proof-picker").inputValue(), "euclid");
  // Direct links do not depend on the previously browsed topic.
  await page.goto(`${base}/proof.html?proof=complete_fields`);
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "real-analysis");
  assert.equal(await page.locator("#proof-picker").inputValue(), "complete_fields");
  await selectProof(page, "cubical_paths");
  await page.waitForURL("**/proof.html?proof=cubical_paths");
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "homotopy");
  assert.match(await page.locator("#source-file").textContent(), /cubical_paths\.cubist/);
  await page.setViewportSize({ width: 390, height: 844 });
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth > innerWidth), false);
  assert.equal(await page.locator("#proof-topic").isVisible(), true);
  assert.equal(await page.locator("#proof-picker").isVisible(), true);
  await page.screenshot({ path: "/private/tmp/thth-proof-topics.png", fullPage: false });
  assert.deepEqual(errors, []);
  console.log(`PASS proof topic navigation (${process.env.THTH_BROWSER ?? "chromium"}); ${proofChoices.length} proofs reachable`);
} finally {
  await browser?.close();
  server.kill();
}
