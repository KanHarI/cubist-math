import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium, webkit } from "playwright";
import { assertFreshBuild } from "../tools/build-stamp.mjs";
// The page loads the WASM kernel from web/dist.
assertFreshBuild();
import { proofCatalog } from "../web/proof-library.mjs";
import { libraryModules } from "../web/cubist/modules.mjs";

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
  const idle = () => page.waitForFunction(() => document.querySelector("#check")?.disabled === false && document.querySelector("#check-loader")?.hidden);
  const base = `http://127.0.0.1:${port}`;
  const response = await page.goto(`${base}/`);
  assert.equal(response.status(), 200);
  assert.match(await page.title(), /Proof highlights/);
  assert.equal(await page.locator("h1").count(), 1);
  // The language reference comes first, then the proof library and file browser.
  assert.deepEqual(await page.locator(".introduction .browse-link").evaluateAll(links => links.map(link => link.getAttribute("href"))),
    ["language.html", "proof.html", "files.html"]);
  const links = await page.locator(".proof-card[href], .proof-card-main").evaluateAll(cards => cards.map(card => card.href));
  assert.equal(links.length, 10);
  // Every card points to a registered source, in the library or the archive,
  // and to a real theorem in that source.
  for (const link of links) {
    const query = new URL(link).searchParams, library = libraryModules.includes(query.get("proof"));
    assert.ok(library || proofCatalog.some(p => p.id === query.get("proof")));
    const source = await page.request.get(`${base}/${library ? "library" : "archive/first-library"}/${query.get("proof")}.cubist`);
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
  const f4Card = page.locator("article.proof-card").filter({ has: page.locator('[href*="proof=f4_galois_group&"]') });
  await f4Card.locator(".proof-card-main").hover();
  assert.equal(await f4Card.locator(".proof-card-main").evaluate(el => getComputedStyle(el).textDecorationLine), "none");
  assert.equal(await f4Card.locator(".related-proof").evaluate(el => getComputedStyle(el).textDecorationLine), "none");
  await f4Card.locator(".related-proof").hover();
  assert.equal(await f4Card.locator(".related-proof").evaluate(el => getComputedStyle(el).textDecorationLine), "underline");
  await page.mouse.move(0, 0);
  await page.screenshot({ path: "/private/tmp/thth-highlights-desktop.png", fullPage: true });
  await f4Card.locator('.related-proof').click();
  await idle();
  assert.equal(new URL(page.url()).searchParams.get("name"), "f4_extension_loops_equal_cyclic_two");
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await page.goto(base);
  // Check representative destinations, including the named final result.
  for (const proof of groupOnly ? ["group_univalence"] : ["euclid", "circle_group_identity", "group_univalence", "f4_galois_group"]) {
    if (proof === "f4_galois_group")
      await f4Card.click({ position: { x: 8, y: 8 } });
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
      await page.waitForFunction(() => document.querySelector("#kernel-view")?.disabled === false);
      assert.match(await page.locator("#inspect-type").textContent(), /GroupIso\(CircleLoopGroup, IntegerGroup\)/);
      for (const name of ["GroupIso", "CircleLoopGroup", "IntegerGroup"])
        assert.equal(await page.locator(`#kernel-type [data-name="${name}"]`).count(), 1);
      assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /unavailable/);
      const tuple = page.locator('#read-source .reference.macro[data-name="("][data-tip*="winding, (integer_loop"]').first();
      assert.equal(await tuple.count(), 1);
      // The expansion shows at once on hover, without the browser's title delay.
      await tuple.hover();
      const tip = page.locator(".token-tip");
      assert.equal(await tip.isVisible(), true);
      assert.match(await tip.textContent(), /winding, \(integer_loop, \(integer_loop_winding/);
      await tuple.click();
      assert.equal(await page.locator("#inspect-kind").textContent(), "tuple macro");
      assert.match(await page.locator("#inspect-description").textContent(), /Expands to \(winding, \(integer_loop/);

    }
    await page.getByRole("link", { name: "Proof highlights", exact: true }).click();
    assert.match(await page.title(), /Proof highlights/);
  }
  if (!groupOnly) {
    // Both universe-size results open at their checked theorem.
    for (const name of ["russell", "no_small_universe_family"]) {
      await page.goto(base);
      await page.locator(`.proof-card a[href="proof.html?proof=universe_smallness&name=${name}"]`).first().click();
      await idle();
      assert.equal(await page.locator("#proof-title").textContent(), "Library: universe_smallness");
      assert.equal(await page.locator("#inspect-name").textContent(), name);
      assert.equal(await page.locator("#diagnostic").isVisible(), false);
      if (name === "russell") {
        assert.match(await page.locator("#inspect-type").textContent(), /IsUSmall\(U0, U0\).*Void/);
      } else {
        assert.equal(await page.locator("#inspect-type").textContent(), "Void");
        assert.match(await page.locator("#inspect-parameters-list").textContent(), /covers.*ContrEquiv/s);
      }
    }
    await page.goto(base);
    // The library card opens its module at the named theorem.
    await page.locator('.proof-card[href*="proof=universe_automorphisms&"]').click();
    await idle();
    assert.equal(await page.locator("#proof-title").textContent(), "Library: universe_automorphisms");
    assert.equal(await page.locator("#inspect-name").textContent(), "excluded_middle_iff_universe_swap");
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.match(await page.locator("#inspect-type").textContent(), /ExcludedMiddle/);
    await page.goto(`${base}/proof.html?proof=group_first_isomorphism&name=group_first_isomorphism`);
    await idle();
    await page.waitForFunction(() => document.querySelector("#kernel-view")?.disabled === false);
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.match(await page.locator("#result").textContent(), /Verified group_first_isomorphism/);
    assert.match(await page.locator("#kernel-type").textContent(), /KernelQuotientGroup/);
    assert.match(await page.locator("#kernel-type").textContent(), /ImageGroup/);
    await page.goto(`${base}/proof.html?proof=quotient_group_universal&name=quotient_group_universal`);
    await idle();
    await page.waitForFunction(() => document.querySelector("#kernel-view")?.disabled === false);
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.match(await page.locator("#result").textContent(), /Verified quotient_group_universal/);
    assert.match(await page.locator("#kernel-type").textContent(), /QuotientGroup/);
    assert.match(await page.locator("#kernel-type").textContent(), /GroupHomAt/);
    await page.getByRole("link", { name: "Proof highlights", exact: true }).click();
    await page.getByRole("link", { name: "Kernel workbench", exact: true }).click();
    await page.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
    assert.ok(page.url().endsWith("/workbench.html"));
    assert.equal(await page.locator("#name").textContent(), "example");
    await page.getByRole("link", { name: "Proof highlights", exact: true }).click();
    await page.locator('.proof-card[href*="proof=euclid&"]').click();
    await idle();
    await page.locator('#read-source [data-name="InfinitelyManyPrimes"]').first().click();
    await page.waitForFunction(() => document.querySelector("#open-kernel-type")?.disabled === false);
    const popupPromise = page.waitForEvent("popup");
    await page.locator("#open-kernel-type").click();
    const popup = await popupPromise;
    await popup.waitForURL("**/workbench.html?transfer=*");
    await popup.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
    assert.equal(await popup.locator("#diagnostic").isVisible(), false);
    assert.notEqual(await popup.locator("#name").textContent(), "example");
    await popup.close();
  }
  assert.deepEqual(errors, []);
  console.log(`PASS proof landing: root, ten highlights, destinations, ${groupOnly ? "group identity" : "universe size and workbench transfer"}, mobile (${process.env.THTH_BROWSER ?? "chromium"})`);
} finally {
  await browser?.close();
  server.kill();
}
