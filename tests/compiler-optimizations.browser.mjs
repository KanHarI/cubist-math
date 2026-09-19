import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
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
  const page = await browser.newPage();
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  const checked = async () => {
    await page.waitForFunction(() => document.querySelector("#check").disabled === false &&
      document.querySelector("#check-loader").hidden &&
      (!document.querySelector("#result").hidden || !document.querySelector("#diagnostic").hidden));
    assert.equal(await page.locator("#diagnostic").isVisible(), false);
    assert.match(await page.locator("#result").innerText(), /Verified copy_of_two/);
    return Number((await page.locator("#result > small").innerText()).match(/[\d,]+/)[0].replaceAll(",", ""));
  };
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=basics`);
  const both = await checked();
  assert.equal(await page.locator("#reuse-normal-forms").isChecked(), true);
  assert.equal(await page.locator("#memoize-instructions").isChecked(), true);
  assert.equal(await page.locator("#index-fresh-contexts").count(), 0);
  const position = await page.locator("#reuse-normal-forms").boundingBox();
  const sourcePosition = await page.locator("#source-panel").boundingBox();
  assert.ok(position.y < sourcePosition.y, "Optimization controls appear above the proof workspace");
  await page.locator("#memoize-instructions").uncheck();
  const normalForms = await checked();
  await page.locator("#reuse-normal-forms").uncheck();
  const baseline = await checked();
  await page.locator("#memoize-instructions").check();
  const instructions = await checked();
  assert.ok(normalForms < baseline);
  assert.ok(instructions < baseline);
  assert.ok(both < baseline);
  await page.reload();
  assert.equal(await checked(), instructions);
  assert.equal(await page.locator("#reuse-normal-forms").isChecked(), false);
  assert.equal(await page.locator("#memoize-instructions").isChecked(), true);
  await page.locator("#memoize-instructions").uncheck();
  assert.equal(await checked(), baseline);
  await page.reload();
  assert.equal(await checked(), baseline);
  assert.equal(await page.locator("#reuse-normal-forms").isChecked(), false);
  assert.equal(await page.locator("#memoize-instructions").isChecked(), false);
  await page.locator("#reuse-normal-forms").check();
  await checked();
  await page.locator("#memoize-instructions").check();
  assert.equal(await checked(), both);
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("construction example { export unit = unit_value(); }");
  assert.equal(await page.locator("#memoize-instructions").isDisabled(), true);
  await page.locator("#check").click();
  await page.waitForFunction(() => document.querySelector("#check-loader").hidden &&
    document.querySelector("#check").disabled === false);
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  assert.match(await page.locator("#result").innerText(), /Checked unit/);
  assert.deepEqual(errors, []);
  console.log(JSON.stringify({ baseline, normalForms, instructions, both }));
} finally {
  await browser?.close();
  server.kill();
}
