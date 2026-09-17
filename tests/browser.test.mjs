import assert from "node:assert/strict";
import { createServer } from "node:http";
import { readFile, mkdir } from "node:fs/promises";
import { resolve, extname, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright";
import proofs from "../web/proofs/catalogue.mjs";
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
  assert.equal(await page.locator('.object[data-name="LEM"]').count(), 1);
  assert.equal(await page.locator('.object[data-name="AOC"]').count(), 1);
  assert.equal(await page.locator("#axioms").isChecked(), true);
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
  await page.locator("#file").setInputFiles({
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
  for (const entry of proofs) {
    await page.locator("#bundled-proof").selectOption(entry.id);
    await page.locator("#open-bundled").click();
    await page.waitForFunction(
      (name) => document.querySelector("#active-name").textContent === name,
      entry.exports.at(-1),
    );
    assert.equal(await page.locator("#axioms").isChecked(), entry.allowAxioms);
    assert.equal(await page.locator("#error").isVisible(), false, entry.id);
    if (entry.id === "wnat_equiv") {
      assert.equal(
        await page.locator("#object-count").textContent(),
        "9 / 1,910",
      );
      assert.equal(
        await page.locator("#loaded-steps").textContent(),
        "All 1,910 steps loaded. 1,901 intermediate steps hidden.",
      );
      await page.locator("#show-intermediate").check();
      assert.equal(await page.locator(".object").count(), 1910);
      assert.equal(
        await page.locator("#object-count").textContent(),
        "1,910 / 1,910",
      );
      await page.locator("#show-intermediate").uncheck();
      assert.match(
        await page.locator("#checked-judgement").textContent(),
        /Verified closed judgement: wnat_to_nat_isEquiv : WNatToNat_isEquiv/,
      );
      assert.match(
        await page.locator("#inference").textContent(),
        /Inferred by DefEqExtR from/,
      );
      assert.match(
        await page.locator("#expression-limit").textContent(),
        /7,335 nodes/,
      );
      const beforeExpandHistory = await page.locator(".history-item").count();
      await page.locator("#active-name").scrollIntoViewIfNeeded();
      await page.screenshot({
        path: fileURLToPath(
          new URL("../.tools/wnat-judgement.png", import.meta.url),
        ),
      });
      await page.locator("#expression .truncated").first().click();
      await page.waitForFunction(
        () =>
          document.querySelector("#expand-expression").textContent ===
          "Collapse expression",
      );
      assert.equal(await page.locator("#expression .truncated").count(), 0);
      assert.equal(await page.locator("#expression .term").count(), 7335);
      await page.locator("#checked-judgement button").click();
      await page.waitForFunction(
        () =>
          document.querySelector("#active-name").textContent ===
          "WNatToNat_isEquiv",
      );
      assert.match(await page.locator("#expression").textContent(), /^\(Σ/);
      await page.locator("#back-reference").click();
      await page.waitForFunction(
        () =>
          document.querySelector("#active-name").textContent ===
          "wnat_to_nat_isEquiv",
      );
      assert.equal(await page.locator("#expression .term").count(), 7335);
      await page.locator("#expand-expression").click();
      await page.waitForFunction(
        () =>
          document.querySelector("#expand-expression").textContent ===
          "Show full expression",
      );
      assert.ok((await page.locator("#expression .truncated").count()) > 0);
      await page.locator("#inference button").first().click();
      await page.waitForFunction(() =>
        document
          .querySelector("#inference")
          .textContent.startsWith("Inferred by DefEqRefl"),
      );
      await page.locator("#back-reference").click();
      await page.waitForFunction(
        () =>
          document.querySelector("#active-name").textContent ===
          "wnat_to_nat_isEquiv",
      );
      assert.equal(
        await page.locator(".history-item").count(),
        beforeExpandHistory,
      );
    }
    if (entry.verify)
      assert.equal(
        await page.locator("#verification").textContent(),
        "Verified closed proof.",
      );
  }
  await page.locator("#bundled-proof").selectOption("prelude_library");
  await page.locator("#open-bundled").click();
  await page.locator('.object[data-name="LEM"]').waitFor();
  await page.locator("#filter").fill("LEM");
  await page.locator('.object[data-name="LEM"]').click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "LEM",
  );
  await page.locator('#type .term[data-path=""]').click();
  assert.equal(await page.locator("#selection-label").textContent(), "type");
  const axiomLink = page.locator('#type [data-declaration="lib_Trunc"]');
  assert.equal(await axiomLink.textContent(), "axiom28");
  const historyCount = await page.locator(".history-item").count();
  await axiomLink.click({ modifiers: ["Shift"] });
  assert.equal(await page.locator("#active-name").textContent(), "LEM");
  const selectedAxiom = await page.locator("#selection-label").textContent();
  assert.equal(selectedAxiom, "type.1.1.1.0.0");
  await axiomLink.click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "lib_Trunc",
  );
  assert.equal(await page.locator("#expression").textContent(), "axiom28");
  assert.equal(
    await page.locator("#object-kind").textContent(),
    "explicit axiom",
  );
  assert.equal(
    await page.locator(".object.active").textContent(),
    "lib_TruncAXIOM",
  );
  assert.equal(await page.locator("#filter").inputValue(), "LEM");
  await page.locator("#back-reference").click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "LEM",
  );
  assert.equal(
    await page.locator("#selection-label").textContent(),
    selectedAxiom,
  );
  assert.equal(await page.locator(".history-item").count(), historyCount);
  await axiomLink.focus();
  await axiomLink.press("Enter");
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "lib_Trunc",
  );

  await page.locator("#filter").fill("lib_inv_refl");
  await page.locator('.object[data-name="lib_inv_refl"]').click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "lib_inv_refl",
  );
  const definitionLink = page
    .locator("#expression .reference")
    .filter({ hasText: /^def702$/ });
  const definitionTarget =
    await definitionLink.getAttribute("data-declaration");
  assert.equal(definitionTarget, "s2368_PiIntro");
  await definitionLink.click();
  await page.waitForFunction(
    (name) => document.querySelector("#active-name").textContent === name,
    definitionTarget,
  );
  assert.match(await page.locator("#expression").textContent(), /^\(λ/);
  assert.equal(await page.locator("#show-intermediate").isChecked(), false);
  await page.locator("#back-reference").click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "lib_inv_refl",
  );

  // A declaration is navigable even when it is hidden and filtered out.
  await page.locator("#file").setInputFiles({
    name: "hidden-axiom.json",
    mimeType: "application/json",
    buffer: Buffer.from(
      JSON.stringify({
        format: "thth-workbench",
        version: 1,
        policy: { allowAxioms: true },
        steps: [
          { name: "U", op: "UnitForm", args: [] },
          { name: "secret", op: "Axiom", args: ["U"], hidden: true },
          { name: "result", op: "EqIntro", args: ["secret"] },
        ],
      }),
    ),
  });
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "result",
  );
  assert.equal(await page.locator("#back-reference").isVisible(), false);
  const hiddenLink = page.locator('#expression [data-declaration="secret"]');
  await hiddenLink.press("Shift+Enter");
  assert.equal(await page.locator("#active-name").textContent(), "result");
  assert.equal(
    await page.locator("#selection-label").textContent(),
    "expression.0",
  );
  await hiddenLink.press("Space");
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "secret",
  );
  assert.equal(await page.locator("#type").textContent(), "Unit");
  assert.equal(await page.locator("#show-intermediate").isChecked(), false);
  assert.equal(
    await page.locator(".object.active").textContent(),
    "secretAXIOM",
  );
  await page.locator("#back-reference").click();
  await page.waitForFunction(
    () => document.querySelector("#active-name").textContent === "result",
  );
  assert.equal(
    await page.locator("#selection-label").textContent(),
    "expression.0",
  );
  assert.deepEqual(errors, []);
  console.log(
    "Browser: axiom navigation, selection, reduction, rewrite, preview isolation, undo, save/import, and WASM worker passed",
  );
} finally {
  if (browser) await browser.close();
  await new Promise((r) => server.close(r));
}
