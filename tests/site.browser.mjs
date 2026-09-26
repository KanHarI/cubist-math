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
  // A numeral's expansion shows at once on hover.
  await page.locator('#tour-numbers [data-tip*="succ("]').first().hover();
  assert.match(await page.locator(".token-tip:not([hidden])").textContent(), /^\d+ expands to succ\(/);
  assert.match(await page.locator(".drawer-head a").getAttribute("href"), /proof\.html\?example=1#source=/);
  console.log("PASS reference examples: in-browser checking, linked names, embedded kernel inspector, evaluate results, instant macro tips");
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
