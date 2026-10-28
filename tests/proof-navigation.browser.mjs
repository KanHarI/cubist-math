import { browserTest } from "./browser-test.mjs";
import assert from "node:assert/strict";
import { chromium, webkit } from "playwright";
import { proofCatalog, proofTopics, proofsInTopic } from "../web/proof-library.mjs";
import { selectProof } from "./proof-navigation.mjs";

await browserTest(async ({ browser, base }) => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  const idle = () => page.waitForFunction(() => document.querySelector("#check")?.disabled === false && document.querySelector("#check-loader")?.hidden);
  await page.goto(`${base}/proof.html?proof=signed_integers`);
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "arithmetic");
  assert.equal(await page.locator("#proof-picker").inputValue(), "signed_integers");
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
  await selectProof(page, "signed_integers");
  await page.waitForURL("**/proof.html?proof=signed_integers");
  await idle();
  await page.goBack();
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "basic-logic");
  assert.equal(await page.locator("#proof-picker").inputValue(), "basics");
  assert.equal(await page.locator("#editor").inputValue(), draft);
  await page.goForward();
  await idle();
  assert.equal(await page.locator("#proof-picker").inputValue(), "signed_integers");
  // Imported source navigation still initializes the destination's topic.
  await page.locator('#read-source a[data-name="paths_"]').click();
  await page.waitForURL("**/proof.html?proof=paths_*");
  await idle();
  assert.equal(await page.locator("#proof-topic").inputValue(), "homotopy");
  assert.equal(await page.locator("#proof-picker").inputValue(), "paths_");
  await page.goBack();
  await idle();
  assert.equal(await page.locator("#proof-picker").inputValue(), "signed_integers");
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
  console.log(`PASS proof topic navigation (${process.env.THTH_BROWSER ?? "chromium"}); ${proofCatalog.length} proofs reachable`);
}, { engine: process.env.THTH_BROWSER === "webkit" ? webkit : chromium });
