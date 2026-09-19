import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium, webkit } from "playwright";

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
  browser = await (process.env.THTH_BROWSER === "webkit" ? webkit : chromium).launch({ headless: true });
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  const idle = () => page.waitForFunction(() => !document.querySelector("#check").disabled &&
    document.querySelector("#check-loader").hidden);
  const inspect = async name => {
    await page.locator(`#definitions [data-name="${name}"]`).click();
    await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
  };
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=basics`);
  await idle();
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`def Natural = Nat;
def one = 1;
def Same = one =[Natural] one;
theorem local(n : Nat, p : n =[Nat] n) : n =[Nat] n { exact p; }
def Nested = Same =[U0] Same;`);
  await page.locator("#check").click();
  await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await inspect("Same");
  assert.equal(await page.locator("#kernel-identity-sugar").isChecked(), true);
  assert.equal(await page.locator("#kernel-expression").textContent(), "(one=[Natural]one)");
  assert.equal(await page.locator('#kernel-expression [data-identity-sugar="true"]').count(), 1);
  assert.equal(await page.locator('#kernel-expression [data-name="one"]').count(), 2);
  assert.equal(await page.locator('#kernel-expression [data-name="Natural"]').count(), 1);
  const initialJudgement = await page.locator("#kernel-inference").textContent();
  await page.locator("#kernel-identity-sugar").uncheck();
  assert.equal(await page.locator("#kernel-expression").textContent(), "IdNatural(one,one)");
  assert.equal(await page.locator('#kernel-expression [data-identity-sugar="true"]').count(), 0);
  assert.equal(await page.locator("#kernel-inference").textContent(), initialJudgement);
  await page.locator("#kernel-view").selectOption("raw");
  assert.equal(await page.locator("#kernel-identity-options").isVisible(), false);
  const raw = await page.locator("#kernel-expression").textContent();
  await page.locator("#kernel-view").selectOption("notation");
  await page.locator("#kernel-identity-sugar").check();
  await page.locator("#kernel-view").selectOption("raw");
  assert.equal(await page.locator("#kernel-expression").textContent(), raw);
  await page.locator("#kernel-view").selectOption("notation");
  await page.locator('#kernel-expression [data-name="Natural"]').click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "Natural" &&
    !document.querySelector("#kernel-view").disabled);
  assert.equal(await page.locator("#view-source").isVisible(), true);
  await inspect("Same");
  await page.locator('#kernel-expression [data-name="one"]').first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "one" &&
    !document.querySelector("#kernel-view").disabled);
  await inspect("Nested");
  assert.equal(await page.locator("#kernel-expression").textContent(), "(Same=[𝒰0]Same)");
  await page.locator('.source-line[data-line="4"] [data-name="p"]').first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "p" &&
    !document.querySelector("#kernel-view").disabled);
  assert.equal(await page.locator("#kernel-type").textContent(), "(n=[Nat]n)");
  assert.equal(await page.locator('#kernel-context-list [data-identity-sugar="true"]').count(), 1);
  await page.locator("#kernel-identity-sugar").uncheck();
  assert.equal(await page.locator("#kernel-type").textContent(), "IdNat(n,n)");
  assert.equal(await page.locator('#kernel-context-list [data-identity-sugar="true"]').count(), 0);
  assert.match(await page.locator("#kernel-context-list").textContent(), /IdNat\(n,n\)/);
  await page.locator("#kernel-identity-sugar").check();
  for (const width of [1280, 390]) {
    await page.setViewportSize({ width, height: 900 });
    assert.equal(await page.locator("#kernel-type math").count(), 1);
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth), true);
  }
  assert.deepEqual(errors, []);
  console.log("Identity notation: default, toggle, raw preservation, nested types, context, links, and mobile passed.");
} finally {
  await browser?.close();
  server.kill();
}
