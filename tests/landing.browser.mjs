import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium, webkit } from "playwright";
import { proofChoices } from "../web/proof-library.mjs";

const server = spawn("python3", [fileURLToPath(new URL("../tools/serve.py", import.meta.url)), "--port", "0"],
  { stdio: ["ignore", "pipe", "pipe"] });
// Drain request logs: a full stderr pipe can block the local HTTP server.
server.stderr.resume();
const groupOnly = process.argv.includes("--group-only");
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
  const response = await page.goto(`${base}/`);
  assert.equal(response.status(), 200);
  assert.match(await page.title(), /Proof highlights/);
  assert.equal(await page.locator("h1").count(), 1);
  const links = await page.locator(".proof-card[href], .proof-card-main").evaluateAll(cards => cards.map(card => card.href));
  assert.equal(links.length, 8);
  // Every card points to a registered source and to a real theorem in that source.
  for (const link of links) {
    const query = new URL(link).searchParams;
    assert.ok(proofChoices.some(p => p.id === query.get("proof")));
    const source = await page.request.get(`${base}/proofs/${query.get("proof")}.cubist`);
    assert.equal(source.status(), 200);
    assert.ok((await source.text()).includes(`def ${query.get("name")}`));
  }
  assert.equal(await page.evaluate(() => performance.getEntriesByType("resource").some(r => /kernel|wasm/.test(r.name))), false);
  for (const width of [1440, 390, 320]) {
    await page.setViewportSize({ width, height: 900 });
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth > innerWidth), false);
    assert.equal(await page.locator(".proof-card").first().isVisible(), true);
  }
  await page.screenshot({ path: "/private/tmp/thth-highlights-mobile.png", fullPage: true });
  await page.setViewportSize({ width: 1440, height: 1000 });
  await page.locator(".proof-card-main").hover();
  assert.equal(await page.locator(".proof-card-main").evaluate(el => getComputedStyle(el).textDecorationLine), "none");
  assert.equal(await page.locator(".related-proof").evaluate(el => getComputedStyle(el).textDecorationLine), "none");
  await page.locator(".related-proof").hover();
  assert.equal(await page.locator(".related-proof").evaluate(el => getComputedStyle(el).textDecorationLine), "underline");
  await page.mouse.move(0, 0);
  await page.screenshot({ path: "/private/tmp/thth-highlights-desktop.png", fullPage: true });
  await page.locator('.related-proof').click();
  await idle();
  assert.equal(new URL(page.url()).searchParams.get("name"), "f4_extension_loops_equal_cyclic_two");
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await page.goto(base);
  // Check representative destinations, including the named final result.
  for (const proof of groupOnly ? ["group_univalence"] : ["euclid", "circle_group_identity", "group_univalence", "f4_galois_group"]) {
    if (proof === "f4_galois_group")
      await page.locator("article.proof-card").click({ position: { x: 8, y: 8 } });
    else await page.locator(`.proof-card[href*="proof=${proof}&"]`).click();
    await idle();
    assert.equal(await page.locator("#proof-picker").inputValue(), proof);
    assert.equal(await page.locator("#inspect-name").textContent(), new URL(page.url()).searchParams.get("name"));
    assert.equal(await page.locator("#example").count(), 0);
    assert.equal(await page.getByRole("button", { name: "Euclid example" }).count(), 0);
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.match(await page.locator("#result").textContent(), proof === "euclid" ? /Verified euclid/ : proof === "circle_group_identity" ? /circle_group_isomorphism/ : proof === "group_univalence" ? /group_structure_identity/ : /f4_extension_fundamental_group_is_cyclic_two/);
    if (proof === "f4_galois_group") {
      assert.equal(new URL(page.url()).searchParams.get("name"), "f4_extension_fundamental_group_is_cyclic_two");
      assert.match(await page.locator("#inspect-type").textContent(), /F4OverF2/);
      assert.match(await page.locator("#inspect-type").textContent(), /CyclicTwo/);
    }
    if (proof === "circle_group_identity") {
      await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
      assert.match(await page.locator("#inspect-type").textContent(), /GroupIso\(CircleLoopGroup, IntegerGroup\)/);
      for (const name of ["GroupIso", "CircleLoopGroup", "IntegerGroup"])
        assert.equal(await page.locator(`#kernel-type [data-name="${name}"]`).count(), 1);
      assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /unavailable/);
      const tuple = page.locator('#read-source .reference.macro[data-name="("][title*="winding, (integer_loop"]').first();
      assert.equal(await tuple.count(), 1);
      assert.match(await tuple.getAttribute("title"), /winding, \(integer_loop, \(integer_loop_winding/);
      await tuple.click();
      assert.equal(await page.locator("#inspect-kind").textContent(), "tuple macro");
      assert.match(await page.locator("#inspect-description").textContent(), /Expands to \(winding, \(integer_loop/);

    }
    await page.getByRole("link", { name: "Proof highlights", exact: true }).click();
    assert.match(await page.title(), /Proof highlights/);
  }
  if (!groupOnly) {
    await page.goto(`${base}/proof.html?proof=group_first_isomorphism&name=group_first_isomorphism`);
    await idle();
    await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.match(await page.locator("#result").textContent(), /Verified group_first_isomorphism/);
    assert.match(await page.locator("#kernel-type").textContent(), /KernelQuotientGroup/);
    assert.match(await page.locator("#kernel-type").textContent(), /ImageGroup/);
    await page.goto(`${base}/proof.html?proof=quotient_group_universal&name=quotient_group_universal`);
    await idle();
    await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.match(await page.locator("#result").textContent(), /Verified quotient_group_universal/);
    assert.match(await page.locator("#kernel-type").textContent(), /QuotientGroup/);
    assert.match(await page.locator("#kernel-type").textContent(), /GroupHomAt/);
    await page.getByRole("link", { name: "Proof highlights", exact: true }).click();
    await page.getByRole("link", { name: "Kernel workbench", exact: true }).click();
    await page.waitForFunction(() => document.querySelector("#status").textContent.startsWith("Cubical C checked"));
    assert.ok(page.url().endsWith("/workbench.html"));
    assert.equal(await page.locator("#name").textContent(), "example");
    await page.getByRole("link", { name: "Proof highlights", exact: true }).click();
    await page.locator('.proof-card[href*="proof=euclid&"]').click();
    await idle();
    await page.locator('#read-source [data-name="InfinitelyManyPrimes"]').first().click();
    await page.waitForFunction(() => !document.querySelector("#open-kernel-type").disabled);
    const popupPromise = page.waitForEvent("popup");
    await page.locator("#open-kernel-type").click();
    const popup = await popupPromise;
    await popup.waitForURL("**/workbench.html?transfer=*");
    await popup.waitForFunction(() => document.querySelector("#status").textContent.startsWith("Cubical C checked"));
    assert.equal(await popup.locator("#diagnostic").isVisible(), false);
    assert.notEqual(await popup.locator("#name").textContent(), "example");
    await popup.close();
  }
  assert.deepEqual(errors, []);
  console.log(`PASS proof landing: root, eight highlights, destinations, ${groupOnly ? "group identity" : "workbench transfer"}, mobile (${process.env.THTH_BROWSER ?? "chromium"})`);
} finally {
  await browser?.close();
  server.kill();
}
