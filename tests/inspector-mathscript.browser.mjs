import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { readFile } from "node:fs/promises";
import { chromium, webkit } from "playwright";

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
  browser = await (process.env.THTH_BROWSER === "webkit" ? webkit : chromium).launch({ headless: true });
  const page = await browser.newPage({ viewport: { width: 1440, height: 1050 } });
  const errors = [];
  page.on("pageerror", error => errors.push(error.message));
  const idle = () => page.waitForFunction(() => !document.querySelector("#check").disabled &&
    document.querySelector("#check-loader").hidden);
  const inspect = async name => {
    await page.locator(`#definitions [data-name="${name}"]`).click();
    await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
    assert.equal(await page.locator("#kernel-details").evaluate(node => node.open), true);
  };
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=euclid`);
  await idle();
  await page.locator('.source-line[data-line="16"] [data-name="bounded"]').click();
  await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
  await page.locator("#kernel-type").scrollIntoViewIfNeeded();
  assert.equal(await page.locator("#kernel-expression").textContent(), "bounded");
  assert.equal(await page.locator("#kernel-type").textContent(), "le(succ(succ(i)),n)");
  assert.equal(await page.locator('#kernel-type [data-name="le"]').count(), 1);
  assert.match(await page.locator("#kernel-inference").textContent(), /3 open assumptions/);
  assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /unavailable/);
  const checkMathBounds = async selector => {
    const bounds = await page.locator(selector).evaluate(el => {
      const math = el.querySelector("math"), box = el.getBoundingClientRect(), rect = math.getBoundingClientRect();
      const ends = [...math.querySelectorAll("mi, mn, mo, mtext")].map(n => n.getBoundingClientRect());
      return { startsInside: rect.left >= box.left, glyphsInside:
        ends.every(n => n.left >= rect.left - 1 && n.right <= rect.right + 1),
        scrollReachesEnd: el.scrollWidth >= rect.right - box.left };
    });
    assert.deepEqual(bounds, { startsInside: true, glyphsInside: true, scrollReachesEnd: true });
  };
  await checkMathBounds("#kernel-type");
  assert.deepEqual(await page.locator("#kernel-context-list > li").evaluateAll(rows => rows.map(row => row.dataset.name)), ["n", "i", "bounded"]);
  assert.deepEqual(await page.locator("#kernel-context-list .kernel-context-type").allTextContents(), ["Nat", "Nat", "le(succ(succ(i)),n)"]);
  await page.locator("#kernel-premises button").first().click();
  await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
  assert.deepEqual(await page.locator("#kernel-context-list > li").evaluateAll(rows => rows.map(row => row.dataset.name)), ["n", "i"]);
  assert.equal(await page.locator("#kernel-expression").textContent(), "Context assumption");
  await page.locator('.source-line[data-line="16"] [data-name="bounded"]').click();
  await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
  await page.locator('#kernel-type [data-name="i"]').click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "i" && !document.querySelector("#kernel-view").disabled);
  await page.locator("#view-source").click();
  assert.equal(await page.locator('.source-line[data-line="10"]').evaluate(row => row.classList.contains("active")), true);
  await page.locator('.source-line[data-line="16"] [data-name="bounded"]').click();
  await page.waitForFunction(() => !document.querySelector("#kernel-view").disabled);
  await page.screenshot({path:"/private/tmp/thth-bounded-folded.png",fullPage:true});
  for (const name of ["nat_le_total", "prime_divisor_exists", "factorial"]) {
    await inspect(name);
    assert.equal(await page.locator("#kernel-type math").count(), 1, name);
    assert.equal(await page.locator("#kernel-expression math").count(), 1, name);
    assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /could not|unavailable/);
    assert.doesNotMatch(await page.locator("#kernel-type").textContent(), /#[0-9]|…/);
    if (name === "nat_le_total") {
      assert.equal(await page.locator('#kernel-type [data-name="le"]').count(), 2);
      assert.match(await page.locator("#kernel-type").textContent(), /le\(a,c\)\+le\(succ\(c\),a\)/);
    }
    if (name === "prime_divisor_exists") assert.equal(await page.locator('#kernel-type [data-name="Divides"]').count(), 1);
    if (name === "factorial") {
      assert.match(await page.locator("#kernel-expression").textContent(), /λn\.nat\.elim\[k,h\]\(1,mul\(succ\(k\),h\),n\)/);
      assert.equal(await page.locator('#kernel-expression [data-name="mul"]').count(), 1);
      await page.locator("#kernel-expression").scrollIntoViewIfNeeded();
      await page.screenshot({ path: "/private/tmp/thth-factorial-folded.png", fullPage: true });
      await page.locator('#kernel-expression [data-name="mul"]').click();
      await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "mul" && !document.querySelector("#kernel-view").disabled);
      // mul uses an unsupported primitive call in its source folding plan;
      // its actual checked kernel AST must still receive mathematical notation.
      assert.equal(await page.locator("#kernel-expression math").count(), 1);
      await checkMathBounds("#kernel-expression");
      await page.setViewportSize({ width: 1100, height: 900 });
      await checkMathBounds("#kernel-expression");
      await page.setViewportSize({ width: 1440, height: 1050 });
    }
  }
  await inspect("InfinitelyManyPrimes");
  const expression = "forall n : Nat, exists p : Nat, Prime(p) and n < p";
  assert.equal(await page.locator("#kernel-view").inputValue(), "notation");
  assert.equal(await page.locator("#kernel-expression math").count(), 1);
  assert.equal(await page.locator("#kernel-expression msub > mo").allTextContents().then(a => a.join("")), "ΠΣ");
  assert.match(await page.locator("#kernel-expression").textContent(), /Prime\(p\)×isLt\(n,p\)/);
  assert.match(await page.locator("#kernel-view-note").textContent(), /kernel verified its definitional equality/);
  assert.equal(await page.locator('#kernel-expression [data-name="p"]').count(), 0);
  assert.equal(await page.locator("#kernel-context-list > li").count(), 0);
  assert.match(await page.locator("#kernel-context-note").textContent(), /Empty context/);
  await page.screenshot({ path: "/private/tmp/thth-kernel-folded-math.png", fullPage: true });
  const downloadEvent = page.waitForEvent("download");
  await page.locator("#export-folding").click();
  const download = await downloadEvent;
  const certificate = JSON.parse(await readFile(await download.path(), "utf8"));
  assert.equal(certificate.folding.binding, "InfinitelyManyPrimes");
  assert.ok(certificate.folding.verified.expression.witness);
  assert.ok(certificate.steps.some(step => step.op === "Def"));

  const openWorkbench = async side => {
    const popup = page.waitForEvent("popup");
    await page.locator(`#open-kernel-${side}`).click();
    const workbench = await popup;
    workbench.on("pageerror", error => errors.push(error.message));
    await workbench.waitForURL(/index\.html/);
    await workbench.waitForFunction(() => document.querySelector("#active-name").textContent.includes("_folded_") &&
      document.querySelector("#status").textContent === "WASM ready");
    assert.equal(await workbench.locator("#error").isVisible(), false);
    assert.equal(await workbench.locator("#axioms").isChecked(), false);
    assert.equal(await workbench.locator("#used-axioms").textContent(), "None");
    return workbench;
  };
  const workbench = await openWorkbench("expression");
  assert.equal(await workbench.locator("#active-name").textContent(), "InfinitelyManyPrimes_folded_expression");
  await workbench.locator('#expression [data-declaration="Prime"]').click({ modifiers: ["Shift"] });
  await workbench.locator("#result-name").fill("expanded_prime");
  await workbench.locator("#unfold").click();
  await workbench.locator("#preview:not([hidden])").waitFor();
  assert.match(await workbench.locator("#preview-code").textContent(), /DefReducePointed/);
  await workbench.locator("#accept").click();
  await workbench.waitForFunction(() => document.querySelector("#active-name").textContent === "expanded_prime");
  await workbench.locator('#expression .term[data-path=""]').click({ position: { x: 2, y: 5 } });
  await workbench.locator("#pass").click();
  await workbench.locator("#preview:not([hidden])").waitFor();
  assert.match(await workbench.locator("#preview-code").textContent(), /BetaReduceGrossKnuth/);
  await workbench.locator("#accept").click();
  await workbench.waitForFunction(() => document.querySelector("#active-name").textContent === "expanded_prime_next");
  assert.equal(await workbench.locator("#used-axioms").textContent(), "None");
  await workbench.close();
  const typeWorkbench = await openWorkbench("type");
  assert.equal(await typeWorkbench.locator("#active-name").textContent(), "InfinitelyManyPrimes_folded_type");
  assert.equal(await typeWorkbench.locator("#expression").textContent(), "U0");
  await typeWorkbench.close();

  await page.locator('#kernel-expression [data-name="Prime"]').click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "Prime" && !document.querySelector("#kernel-view").disabled);
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=primes&name=Prime/);
  assert.equal(await page.locator("#kernel-details").evaluate(node => node.open), true);
  assert.equal(await page.locator('#kernel-expression [data-name="Divides"]').count(), 1);
  await page.locator("#view-source").click();
  await idle();
  assert.match(page.url(), /proof=primes&name=Prime/);
  assert.equal(await page.locator("#inspect-name").textContent(), "Prime");
  assert.match(await page.locator(".source-line.active").innerText(), /def Prime/);
  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=euclid`);
  await idle();
  await inspect("InfinitelyManyPrimes");
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), expression);
  await page.locator("#kernel-view").selectOption("raw");
  assert.notEqual(await page.locator("#kernel-expression").innerText(), expression);
  assert.match(await page.locator("#kernel-view-note").innerText(), /Raw checked kernel/);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), expression);
  await inspect("euclid");
  assert.equal(await page.locator("#kernel-type").innerText(), "InfinitelyManyPrimes");
  assert.equal(await page.locator("#kernel-expression").innerText(), "euclid");
  await inspect("Prime");
  assert.equal(await page.locator("#kernel-expression math").count(), 1);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.match(await page.locator("#kernel-expression").innerText(), /^fun \(p : Nat\) => .*Divides/);
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("def InfinitelyManyPrimes : Void { exact tt; }");
  await page.locator("#check").click();
  await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), true);
  await inspect("InfinitelyManyPrimes");
  assert.equal(await page.locator("#kernel-expression math").count(), 1);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), expression);

  // Raw mode retains the existing explicit tree-budget expansion.
  const deep = Array.from({ length: 50 }, (_, i) => `forall n${i} : Nat, `).join("") + "Nat";
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`def Deep = ${deep};`);
  await page.locator("#check").click();
  await idle();
  assert.equal(await page.locator("#diagnostic").isVisible(), false);
  await inspect("Deep");
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), deep);
  await page.locator("#kernel-view").selectOption("raw");
  assert.equal(await page.locator("#expand-kernel").isVisible(), true);
  await page.locator("#expand-kernel").click();
  await idle();
  assert.equal(await page.locator("#expand-kernel").isVisible(), false);
  await page.locator("#kernel-view").selectOption("mathscript");
  assert.equal(await page.locator("#kernel-expression").innerText(), deep);

  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=classical_complex_inverses`);
  await idle();
  await inspect("classical_complex_nonzero_inverse");
  assert.equal(await page.locator("#kernel-type math").count(), 1);
  assert.equal(await page.locator("#kernel-type mtable > mtr").count(), 14);
  assert.equal(await page.locator('#kernel-type [data-name="ComplexUnit"]').count(), 1);
  assert.equal(await page.locator('#kernel-type [data-name="Complex"]').count(), 2);
  assert.equal(await page.locator('#kernel-type [data-name="complex_zero"]').count(), 1);
  assert.doesNotMatch(await page.locator("#kernel-view-note").textContent(), /could not|unavailable|stored term is shown/);
  assert.doesNotMatch(await page.locator("#kernel-type").textContent(), /#[0-9]|…/);
  await page.locator("#kernel-type").scrollIntoViewIfNeeded();
  await page.screenshot({ path: "/private/tmp/thth-classical-inverse-folded.png", fullPage: true });

  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=sample_join_conditions`);
  await idle();
  await page.locator('.source-line[data-line="6"] [data-name="condition"]').first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "condition" && !document.querySelector("#kernel-view").disabled);
  assert.deepEqual(await page.locator("#kernel-context-list > li").evaluateAll(rows => rows.map(row => row.dataset.name)), ["C", "condition"]);
  assert.deepEqual(await page.locator("#kernel-context-list .kernel-context-type").allTextContents(), ["𝒰1", "C→C→C→𝒰0"]);
  assert.equal(await page.locator('#kernel-type [data-name="C"][data-context-id]').count(), 3);
  assert.match(await page.locator("#kernel-inference").textContent(), /2 open assumptions/);
  await page.locator("#kernel-context").scrollIntoViewIfNeeded();
  await page.screenshot({path:"/private/tmp/thth-kernel-context.png", fullPage:true});
  await page.locator('#kernel-context-list > li[data-name="C"] > span > button').click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "C" && !document.querySelector("#kernel-view").disabled);
  assert.equal(await page.locator("#kernel-type").textContent(), "𝒰1");
  await page.locator("#view-source").click();
  assert.equal(await page.locator('.source-line[data-line="6"]').evaluate(row => row.classList.contains("active")), true);
  await page.locator("#back").click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "condition" && !document.querySelector("#kernel-view").disabled);
  await page.locator('#kernel-type [data-name="C"]').first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "C" && !document.querySelector("#kernel-view").disabled);
  assert.equal(await page.locator("#kernel-context-list > li").count(), 1);

  await page.goto(`http://127.0.0.1:${port}/proof.html?proof=complete_fields`);
  await idle();
  await inspect("FieldExists");
  assert.equal(await page.locator("#kernel-truncation-sugar").isChecked(), true);
  assert.equal(await page.locator("#kernel-expression").textContent(), "λx0.‖x0‖");
  const checkedResult = await page.locator("#result").textContent();
  await page.locator("#kernel-truncation-sugar").uncheck();
  assert.match(await page.locator("#kernel-expression").textContent(), /λx0\.TruncateAtAxiom [0-9]+\(𝒰1,x0\)/);
  assert.doesNotMatch(await page.locator("#kernel-expression").textContent(), /Axiom\(\)/);
  const truncation = page.locator('#kernel-expression [data-axiom="lib_Trunc"]');
  assert.equal(await truncation.count(), 1);
  assert.match(await truncation.getAttribute("title"), /Axiom [0-9]+: lib_Trunc/);
  await page.locator("#kernel-expression").scrollIntoViewIfNeeded();
  await page.screenshot({path:"/private/tmp/thth-fieldexists-axiom.png", fullPage:true});
  await truncation.click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "lib_Trunc" && !document.querySelector("#kernel-view").disabled);
  assert.match(await page.locator("#view-source").getAttribute("href"), /prelude_library_construction&name=lib_Trunc/);
  assert.equal(await page.locator("#kernel-type math").count(), 1);
  await page.locator("#back").click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "FieldExists" && !document.querySelector("#kernel-view").disabled);
  assert.equal(await page.locator("#kernel-truncation-sugar").isChecked(), false);
  await page.locator("#kernel-truncation-sugar").check();
  assert.equal(await page.locator("#kernel-expression").textContent(), "λx0.‖x0‖");
  assert.equal(await page.locator("#result").textContent(), checkedResult);
  await page.locator('#kernel-expression [data-axiom="lib_Trunc"]').first().click();
  await page.waitForFunction(() => document.querySelector("#inspect-name").textContent === "lib_Trunc" && !document.querySelector("#kernel-view").disabled);

  assert.deepEqual(errors, []);
  console.log("Certified mathematical kernel view, definition/source navigation, workbench export/unfold/reduce, source/raw views, checked snapshots, and full expansion passed.");
} finally {
  await browser?.close();
  server.kill();
}
