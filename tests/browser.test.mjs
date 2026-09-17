import assert from "node:assert/strict";
import { createServer } from "node:http";
import { readFile, mkdir } from "node:fs/promises";
import { resolve, extname, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright";
const root = fileURLToPath(new URL("../web", import.meta.url));
const types = {
  ".html": "text/html",
  ".mjs": "text/javascript",
  ".css": "text/css",
  ".wasm": "application/wasm",
  ".md": "text/plain",
};
const server = createServer(async (req, res) => {
  try {
    const pathname = decodeURIComponent(
      new URL(req.url, "http://localhost").pathname,
    );
    const path = resolve(
      root,
      "." + (pathname === "/" ? "/index.html" : pathname),
    );
    if (!path.startsWith(root + sep)) {
      res.writeHead(403);
      res.end();
      return;
    }
    const data = await readFile(path);
    res.writeHead(200, {
      "Content-Type": types[extname(path)] || "application/octet-stream",
    });
    res.end(data);
  } catch {
    res.writeHead(404);
    res.end();
  }
});
await new Promise((r) => server.listen(0, "127.0.0.1", r));
let browser;
try {
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage({
    viewport: { width: 1440, height: 1050 },
  });
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));
  await page.goto(`http://127.0.0.1:${server.address().port}`);
  await page.waitForFunction(
    () =>
      document.querySelector("#status").textContent === "WASM ready" &&
      document.querySelector("#active-name").textContent === "nested",
  );
  assert.equal(await page.locator("#opcode option").count(), 67);
  await page.locator('#type .term[data-path=""]').click();
  assert.equal(await page.locator("#selection-label").textContent(), "type");
  await page
    .locator('#expression .term[data-path="1"]')
    .click({ position: { x: 2, y: 10 } });
  assert.equal(
    await page.locator("#selection-label").textContent(),
    "expression.1",
  );
  const count = await page.locator(".object").count();
  await page.locator("#reduce").click();
  await page.locator("#preview:not([hidden])").waitFor();
  assert.match(await page.locator("#preview-code").textContent(), /High1/);
  assert.equal(await page.locator(".object").count(), count);
  await page.locator("#accept").click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "reduced",
  );
  assert.equal(await page.locator(".object").count(), count + 1);
  await page.locator("#undo").click();
  await page.waitForFunction(
    () => !document.querySelector('.object[data-name="reduced"]'),
  );
  await page.locator('.object[data-name="nested"]').click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "nested",
  );
  await page
    .getByText("Select by path or parentheses", { exact: true })
    .click();
  await page.locator("#copy-mark").click();
  const expression = await page.locator("#marked").inputValue();
  await page.locator("#marked").fill("(" + expression + ")");
  await page.locator("#select-mark").click();
  assert.equal(
    await page.locator("#selection-label").textContent(),
    "expression",
  );
  await page.locator("#path").fill("expr.argument");
  await page.locator("#select-path").click();
  assert.equal(
    await page.locator("#selection-label").textContent(),
    "expression.1",
  );
  await page.locator("#witness").selectOption("equality");
  await page.locator("#result-name").fill("rewritten");
  await page.locator("#rewrite").click();
  await page.locator("#preview:not([hidden])").waitFor();
  assert.match(await page.locator("#preview-code").textContent(), /HighSubs/);
  await page.locator("#accept").click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "rewritten",
  );
  const accepted = await page.locator(".object").count();
  await page
    .getByText("Instruction log & source input", { exact: true })
    .click();
  await page.locator("#code").fill("wrong = apply(identity, zero)");
  await page.locator("#preview-code-button").click();
  await page.locator("#error:not([hidden])").waitFor();
  assert.match(await page.locator("#error").textContent(), /rejected/);
  assert.equal(await page.locator(".object").count(), accepted);
  const downloadPromise = page.waitForEvent("download");
  await page.locator("#save").click();
  const download = await downloadPromise;
  const document = JSON.parse(await readFile(await download.path(), "utf8"));
  assert.equal(document.format, "thth-workbench");
  assert.equal(document.steps.at(-1).name, "rewritten");
  await page
    .locator("#file")
    .setInputFiles({
      name: "proof.json",
      mimeType: "application/json",
      buffer: Buffer.from(JSON.stringify(document)),
    });
  await page.waitForFunction(() =>
    document.querySelector("#history").textContent.includes("Imported proof"),
  );
  await page.locator('.object[data-name="nested"]').click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "nested",
  );
  await page.locator("#path").fill("expr.argument");
  await page.locator("#select-path").click();
  await mkdir(new URL("../.tools", import.meta.url), { recursive: true });
  await page.screenshot({
    path: fileURLToPath(new URL("../.tools/workbench.png", import.meta.url)),
    fullPage: true,
  });
  assert.deepEqual(errors, []);
  console.log(
    "Browser: selection, reduction, rewrite, preview isolation, undo, save/import, and WASM worker passed",
  );
} finally {
  if (browser) await browser.close();
  await new Promise((r) => server.close(r));
}
