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
    server.stdout.on("data", data => {
      output += data;
      const match = output.match(/127\.0\.0\.1:(\d+)\//);
      if (match) { clearTimeout(timer); resolve(match[1]); }
    });
  });
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors = []; page.on("pageerror", error => errors.push(error.stack ?? error.message));
  const base = `http://127.0.0.1:${port}`;
  await page.goto(`${base}/proof.html?proof=complex_deformation&name=complex_deformation_at_one`);
  await page.waitForFunction(() => document.querySelector("#inspect-parameters-label").textContent === "Parameters and hypotheses (12)");
  assert.equal(await page.locator("#inspect-type").textContent(), "complex_linear_deformation(F, addF, mulF, one, z, error) = complex_add(F, addF, z, error)");
  assert.equal(await page.locator("#inspect-parameters").getAttribute("open"), null);
  await page.locator("#inspect-parameters summary").click();
  assert.match(await page.locator("#inspect-parameters-list").textContent(), /order : StrictOrder\(F, lt\)/);
  assert.doesNotMatch(await page.locator("#inspect-parameters-list").textContent(), /Truncate|Π/);
  await page.screenshot({ path: "/tmp/cubist-statement-desktop.png", fullPage: false });
  await page.locator('#inspect-type button[data-name="F"]').first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "F" && document.querySelector("#inspect-parameters").hidden);
  await page.locator("#back").click();
  await page.waitForFunction(() => !document.querySelector("#inspect-parameters").hidden);
  await page.setViewportSize({ width: 390, height: 900 });
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth > innerWidth), false);
  await page.goto(`${base}/proof.html?proof=non_normal_subgroup&name=s3_point_stabilizer_not_normal`);
  await page.waitForFunction(() => document.querySelector("#inspect-type").textContent.includes("IsNormal(S3, S3PointStabilizer) -> Void"));
  assert.equal(await page.locator("#inspect-parameters").isVisible(), false);
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await page.goto(`${base}/proof.html?proof=finite_bases&name=scalar_space_basis`);
  await page.waitForFunction(() => document.querySelector("#inspect-type").textContent === "FiniteBasis(K, ScalarSpace(K), 1)");
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  assert.equal(await page.locator("#kernel-axioms").isVisible(), false);
  assert.deepEqual(errors, []);
  console.log("PASS source statements: conclusion, named hypotheses, binder navigation, mobile, S3 and finite basis");
} finally { await browser?.close(); server.kill(); }
