import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { readFile, mkdir } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright";
import proofs from "../web/proofs/catalogue.mjs";
import { selectProof } from "./proof-navigation.mjs";
const child = spawn(
  "python3",
  [fileURLToPath(new URL("../tools/serve.py", import.meta.url)), "--port", "0"],
  { stdio: ["ignore", "pipe", "ignore"] },
);
const port = await new Promise((resolve, reject) => {
  let output = "";
  const timer = setTimeout(
    () => reject(new Error("Browser test server did not start")),
    10000,
  );
  child.on("error", reject);
  child.stdout.on("data", (data) => {
    output += data.toString();
    const match = output.match(/127\.0\.0\.1:(\d+)\//);
    if (match) {
      clearTimeout(timer);
      resolve(Number(match[1]));
    }
  });
  child.once("exit", (code) => {
    clearTimeout(timer);
    reject(new Error("Browser test server exited: " + code));
  });
});
const server = {
  address: () => ({ port }),
  close: (callback) => {
    child.once("exit", callback);
    child.kill();
  },
};
let browser;
try {
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage({
    viewport: { width: 1440, height: 1050 },
  });
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));
  await page.goto(`http://127.0.0.1:${server.address().port}/workbench.html`);
  await page.waitForFunction(
    () =>
      document.querySelector("#status").textContent === "WASM ready" &&
      document.querySelector("#active-name").textContent === "nested",
  );
  assert.equal(await page.locator("#opcode option").count(), 75);
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
    .locator('#expression .reference[data-declaration="s2368_PiIntro"]');
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
  // A cached worker advertising the previous instruction cap must be rejected.
  const staleWorker = /\/mathscript\/worker\.mjs(?:\?.*)?$/;
  await page.route(staleWorker, route => route.fulfill({
    contentType: "text/javascript",
    body: "self.postMessage({ ready: true, maxSteps: 1048576 });",
  }));
  await page.goto(`http://127.0.0.1:${server.address().port}/proof.html?proof=primes`);
  await page.locator("#diagnostic:not([hidden])").waitFor();
  assert.match(await page.locator("#diagnostic").textContent(), /outdated compiler/);
  assert.equal(await page.locator("#result").isVisible(), false);
  await page.unroute(staleWorker);

  // Deliberately stale canonical module responses must not enter the new
  // worker's versioned module graph (the live-browser regression).
  const limitRequests = [];
  page.on("request", (request) => {
    if (request.url().includes("/language.mjs"))
      limitRequests.push(request.url());
  });
  await page.route("**/language.mjs", async (route) => {
    const response = await route.fetch();
    await route.fulfill({
      response,
      body: (await response.text()).replace(
        /MAX_STEPS = \d+/,
        "MAX_STEPS = 8192",
      ),
    });
  });
  // Mathematical authoring, definition navigation, notation, and edit isolation.
  await page.evaluate(() =>
    sessionStorage.setItem(
      "mathscript:primes",
      "// Old saved editor state\nconstruction primes { export old = natural_type(); }",
    ),
  );
  await page.goto(
    `http://127.0.0.1:${server.address().port}/proof.html?proof=primes`,
  );
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(
    await page.locator("#editor").inputValue(),
    /theorem factorial_positive/,
  );
  assert.doesNotMatch(
    await page.locator("#editor").inputValue(),
    /construction primes/,
  );
  assert.equal(await page.locator("#previous-draft").isVisible(), true);
  assert.match(await page.locator("#source-notice").textContent(), /preserved/);
  await page.goto(`http://127.0.0.1:${server.address().port}/proof.html`);
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(await page.locator("#result").textContent(), /Verified euclid/);
  await page.locator('#read-source [data-name="factorial_positive"]').click();
  assert.match(
    await page.locator("#view-source").getAttribute("href"),
    /proof=primes&name=factorial_positive/,
  );
  await page.locator("#view-source").click();
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(
    await page.locator("#read-source .active").textContent(),
    /theorem factorial_positive/,
  );
  assert.match(await page.locator("#editor").inputValue(), /induction/);
  assert.doesNotMatch(
    await page.locator("#editor").inputValue(),
    /construction primes/,
  );
  await page.goBack();
  await page.locator("#result:not([hidden])").waitFor();
  await page
    .locator('#read-source [data-name="InfinitelyManyPrimes"]')
    .last()
    .click();
  await page.locator("#view-source").click();
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(
    await page.locator("#read-source .active").textContent(),
    /def InfinitelyManyPrimes/,
  );
  assert.match(
    await page.locator("#editor").inputValue(),
    /forall n : Nat, exists p : Nat, Prime\(p\) and n < p/,
  );
  assert.match(
    await page.locator("#editor").inputValue(),
    /theorem euclid : InfinitelyManyPrimes/,
  );
  await page.locator('#read-source [data-name="2"]').click();
  assert.match(
    await page.locator("#inspect-description").textContent(),
    /succ\(succ\(0\)\)/,
  );
  await page.locator('#read-source [data-name="<"]').first().click();
  assert.match(
    await page.locator("#inspect-description").textContent(),
    /isLt/,
  );
  await page.locator("#view-source").click();
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(
    await page.locator("#read-source .active").textContent(),
    /def isLt/,
  );
  await page.goBack();
  await page.locator("#result:not([hidden])").waitFor();
  await page.locator('#read-source a[data-name="primes"]').click();
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(
    await page.locator("#proof-title").textContent(),
    /mathematical foundations/,
  );
  await selectProof(page, "basics");
  await page.waitForFunction(() =>
    document.querySelector("#result").textContent.includes("copy_of_two"),
  );
  const checkedSource = await page.locator("#editor").inputValue();
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill("theorem wrong : Void { exact 0; }");
  await page.locator("#check").click();
  await page.locator("#diagnostic:not([hidden])").waitFor();
  assert.match(
    await page.locator("#diagnostic").textContent(),
    /Expected Void/,
  );
  assert.equal(await page.locator("#check-loader").isVisible(), false);
  assert.match(await page.locator("#result").textContent(), /copy_of_two/);
  await page.locator("#editor").fill(checkedSource);
  await page.locator("#check").click();
  await page.locator("#read-source:not([hidden])").waitFor();
  await page.setViewportSize({ width: 390, height: 844 });
  assert.equal(
    await page.evaluate(
      () => document.documentElement.scrollWidth > innerWidth,
    ),
    false,
  );
  await page.screenshot({
    path: fileURLToPath(
      new URL("../.tools/mathscript-mobile.png", import.meta.url),
    ),
    fullPage: true,
  });
  await page.setViewportSize({ width: 1440, height: 1000 });
  await selectProof(page, "surjections");
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(await page.locator("#result").textContent(), /Verified every_surjection_has_right_inverse/);
  const surjectionResult = page.locator("#result > div").filter({
    has: page.getByRole("button", { name: "every_surjection_has_right_inverse", exact: true }),
  });
  await surjectionResult.locator('[data-axiom="AOC"]').click();
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=prelude_library_construction&name=AOC/);
  await page.locator('#read-source [data-name="set_choice"]').click();
  assert.match(await page.locator("#view-source").getAttribute("href"), /name=AOC/);
  await page.locator('#read-source [data-name="setA"]').first().click();
  assert.match(await page.locator("#inspect-type").textContent(), /IsSet\(A\)/);
  assert.match(await page.locator("#language-guide").textContent(), /intro name;/);
  await selectProof(page, "schroeder_bernstein");
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(await page.locator("#result").textContent(), /Verified cantor_schroeder_bernstein/);
  const csbResult = page.locator("#result > div").filter({
    has: page.getByRole("button", { name: "cantor_schroeder_bernstein", exact: true }),
  });
  assert.equal(await csbResult.locator('[data-axiom="AOC"]').count(), 0);
  assert.equal(await csbResult.locator('[data-axiom="s0121_Axiom"]').count(), 0);
  assert.equal(await csbResult.locator('[data-axiom="lib_Trunc"]').count(), 1);
  await csbResult.locator('[data-axiom="LEM"]').click();
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=prelude_library_construction&name=LEM/);
  for (const [proof, theorem] of [
    ["homotopy_limits", "homotopy_limit_period"],
    ["complex_limit_periods", "complex_cauchy_approximation_period_laws"],
    ["limit_periods", "cauchy_approximation_period_laws"],
    ["puncture_periods", "puncture_period_formula"],
    ["complex_periods", "complex_puncture_period_formula"],
    ["puncture_period_examples", "nontrivial_loop_with_zero_period"],
    ["bouquet_generation", "every_puncture_loop_generated"],
    ["bouquet_invariants", "bouquet_maps_determined_by_generators"],
    ["puncture_winding", "puncture_generators_distinct"],
    ["puncture_noncommutative", "winding_vector_does_not_classify_loops"],
  ]) {
    await selectProof(page, proof);
    await page.locator("#result:not([hidden])").waitFor({ timeout: 120000 });
    assert.match(await page.locator("#result").textContent(), new RegExp(`Verified ${theorem}`));
    assert.equal(await page.locator("#puncture-note").isVisible(), true);
    assert.match(await page.locator("#puncture-note").textContent(), /comparison with continuous paths/);
    assert.equal(await page.locator('#result [data-axiom="LEM"]').count(), 0);
    assert.equal(await page.locator('#result [data-axiom="AOC"]').count(), 0);
  }
  const commutatorResult = page.locator("#result > div").filter({
    has: page.getByRole("button", { name: "puncture_commutator_nontrivial", exact: true }),
  });
  await commutatorResult.locator('[data-axiom="lib_univalence"]').click();
  assert.match(await page.locator("#view-source").getAttribute("href"), /name=lib_univalence/);
  for (const [proof, theorem] of [
    ["complex_contour_sums", "complex_identity_backtrack_nonzero"],
    ["complex_curves", "complex_straight_curve_endpoints"],
    ["complex_curve_variation", "complex_interval_deformation_variation"],
    ["curve_contour_limits", "affine_curve_contour_tag_independent_limit"],
    ["curve_tag_stability", "affine_contour_endpoint_sums_close"],
    ["affine_refinement", "affine_refinement_uniform_estimate"],
    ["sample_subdivisions", "sample_subdivisions_flatten"],
    ["sample_subdivision_conditions", "subdivision_tagged_map"],
    ["complex_perturbations", "complex_perturbation_add"],
    ["complex_subdivision_estimates", "complex_subdivision_flat_estimate"],
    ["interval_subdivisions", "interval_refinement_radius_sum"],
    ["interval_bisection", "ordered_interval_bisection"],
    ["sample_join_conditions", "subdivision_tagged_valid_join"],
    ["sample_condition_maps", "sample_tagged_map"],
    ["dyadic_sampling", "dyadic_interval_samples"],
    ["dyadic_mesh", "dyadic_interval_samples_fine"],
    ["dyadic_width_bounds", "dyadic_width_growth_bound"],
    ["dyadic_decay", "dyadic_width_arbitrarily_small"],
    ["fine_interval_samples", "archimedean_interval_fine_samples"],
    ["dyadic_tails", "dyadic_width_eventually_small"],
    ["dyadic_convergence", "dyadic_width_converges_from_bounds"],
    ["fine_interval_tails", "archimedean_interval_fine_tail"],
    ["subdivision_transport", "subdivision_condition_move_end"],
    ["subdivision_join", "subdivision_total_join"],
    ["subdivision_join_conditions", "subdivision_tagged_join"],
    ["subdivision_refinement", "subdivision_refinement_sum_join"],

    ["affine_partition_refinement", "affine_partition_uniform_estimate"],

    ["complex_affine", "complex_linear_deformation_uniform"],
    ["complex_contour_tag_limits", "complex_contour_tag_independent_limit"],
    ["field_scale_limits", "field_nonnegative_scale_zero_converges"],
    ["contour_tag_limits", "contour_tag_errors_converge"],
    ["complex_magnitude", "complex_box_mul_rectangle"],
    ["sample_magnitude_bounds", "sample_weighted_sum_bound"],
    ["contour_refinement", "contour_sum_change_tags"],
    ["sample_error_bounds", "sample_sum_error_bound"],
    ["complex_limits", "complex_cauchy_complete"],
    ["complex_algebra", "complex_commutative_ring"],
    ["circle_degree", "positive_degree_no_contractible_extension"],
    ["complex_deformation", "complex_linear_deformation_nonzero"],
    ["homotopy_paths", "null_homotopy_kills_loops"],
    ["complex_inverses", "complex_ordered_field_inverses"],
    ["classical_complex_inverses", "classical_complex_nonzero_inverse"],
    ["ordered_squares", "ordered_square_nonnegative"],
    ["complex_norm_coordinates", "complex_coordinate_norm_product"],
    ["complex_polynomials", "monic_linear_root_unique"],
    ["polynomial_difference", "monic_factor_at_root"],
  ]) {
    await selectProof(page, proof);
    await page.locator("#result:not([hidden]), #diagnostic:not([hidden])").waitFor({ timeout: ["curve_contour_limits", "curve_tag_stability"].includes(proof) ? 900000 : 300000 });
    assert.equal(await page.locator("#diagnostic").isVisible(), false, await page.locator("#diagnostic").textContent());
    assert.match(await page.locator("#result").textContent(), new RegExp(`Verified ${theorem}`));
    assert.equal(await page.locator("#complex-note").isVisible(), true);
    assert.match(await page.locator("#complex-note").textContent(), /Great Picard remain to be proved/);
    assert.equal(await page.locator("#puncture-note").isVisible(), false);
    if (proof === "classical_complex_inverses") {
      assert.ok(await page.locator('#result [data-axiom="LEM"]').count() > 0);
    } else {
      assert.equal(await page.locator('#result [data-axiom="LEM"]').count(), 0);
    }
    assert.equal(await page.locator('#result [data-axiom="AOC"]').count(), 0);
  }
  for (const [proof, theorem] of [
    ["complete_fields", "field_constant_converges"],
    ["dedekind_cuts", "principal_cut_injective"],
    ["boolean_cuts", "classical_upper_membership"],
    ["cauchy_quotient", "cauchy_sequence_representatives"],
  ]) {
    await selectProof(page, proof);
    await page.locator("#result:not([hidden])").waitFor();
    assert.match(await page.locator("#result").textContent(), new RegExp(`Verified ${theorem}`));
    assert.equal(await page.locator("#development-note").isVisible(), true);
    assert.match(await page.locator("#development-note").textContent(), /instances are not yet proved/);
    assert.equal(await page.locator('#result [data-axiom="AOC"]').count(), 0);
    if (proof !== "boolean_cuts") assert.equal(await page.locator('#result [data-axiom="LEM"]').count(), 0);
    else assert.ok(await page.locator('#result [data-axiom="LEM"]').count() > 0);
  }
  await selectProof(page, "field_logic");
  await page.locator("#result:not([hidden])").waitFor();
  await page.locator('#read-source [data-name="truncation_at"]').first().click();
  assert.match(await page.locator("#view-source").getAttribute("href"), /name=lib_Trunc/);
  assert.match(await page.locator("#language-guide").textContent(), /Type1/);
  await selectProof(page, "circle");
  await page.locator("#result:not([hidden])").waitFor();
  assert.equal(await page.locator("#development-note").isVisible(), false);
  assert.equal(await page.locator("#puncture-note").isVisible(), false);
  assert.equal(await page.locator("#complex-note").isVisible(), false);
  assert.match(
    await page.locator("#result").textContent(),
    /Verified fundamental_group_of_circle/,
  );
  assert.match(
    await page.locator("#result").textContent(),
    /3 explicit axioms/,
  );
  const finalResult = page
    .locator("#result > div")
    .filter({
      has: page.getByRole("button", {
        name: "fundamental_group_of_circle",
        exact: true,
      }),
    });
  assert.deepEqual(
    (
      await finalResult
        .locator("[data-axiom]")
        .evaluateAll((nodes) => nodes.map((n) => n.dataset.axiom))
    ).sort(),
    ["lib_funext", "lib_ua_elim", "lib_univalence"],
  );
  await finalResult.locator('[data-axiom="lib_funext"]').click();
  assert.equal(await page.locator("#inspect-name").textContent(), "lib_funext");
  assert.match(
    await page.locator("#view-source").getAttribute("href"),
    /prelude_library_construction&name=lib_funext/,
  );
  await page
    .locator('#read-source [data-name="FundamentalGroupS1IsZ"]')
    .last()
    .click();
  await page.locator("#view-source").click();
  assert.match(
    await page.locator("#read-source .active").textContent(),
    /def FundamentalGroupS1IsZ/,
  );
  await page.locator('#read-source [data-name="IsSet"]').first().click();
  await page.locator("#view-source").click();
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(
    await page.locator("#read-source .active").textContent(),
    /def IsSet/,
  );
  await page.goBack();
  await page.locator("#result:not([hidden])").waitFor();
  await page.locator('#read-source [data-name="univalence"]').first().click();
  assert.match(
    await page.locator("#view-source").getAttribute("href"),
    /prelude_library_construction&name=lib_univalence/,
  );
  await page.screenshot({
    path: fileURLToPath(new URL("../.tools/circle-proof.png", import.meta.url)),
    fullPage: true,
  });
  for (const [proof, result, expected] of [
    ["function_counting", "finite_function_equivalence", ["lib_funext"]],
    ["permutations", "finite_permutation_equivalence", ["lib_funext"]],
    ["binomial_counting", "finite_binomial_equivalence", ["lib_funext", "lib_Trunc", "lib_trunc_intro", "lib_trunc_is_trunc", "lib_trunc_elim"]],
  ]) {
    // Hold worker startup so the initial loader can be inspected reliably.
    let releaseWorker;
    const workerGate = new Promise(resolve => { releaseWorker = resolve; });
    await page.route("**/mathscript/worker.mjs*", async route => {
      await workerGate;
      await route.continue();
    }, { times: 1 });
    await selectProof(page, proof);
    await page.locator("#check-loader:not([hidden])").waitFor();
    assert.equal(await page.locator("#source-panel").getAttribute("aria-busy"), "true");
    assert.equal(await page.locator("#check-progress").getAttribute("value"), null);
    assert.match(await page.locator("#check-detail").textContent(), /^0 kernel steps · 0 definitions checked ·/);
    assert.match(await page.locator("#check-detail").evaluate(node => getComputedStyle(node).fontFamily), /monospace/);
    releaseWorker();
    await page.locator("#check-progress[value]").waitFor({ state: "attached" });
    await page.locator("#result:not([hidden])").waitFor();
    await page.locator("#check-loader").waitFor({ state: "hidden" });
    assert.match(await page.locator("#check-detail").textContent(), /^[\d,]+ kernel steps · [\d,]+ of [\d,]+ definitions checked(?: ·.*)?$/);
    assert.equal(await page.locator("#source-panel").getAttribute("aria-busy"), "false");
    const row = page.locator("#result > div").filter({has: page.getByRole("button", {name: result, exact: true})});
    assert.deepEqual((await row.locator("[data-axiom]").evaluateAll(nodes => nodes.map(n => n.dataset.axiom))).sort(), [...expected].sort());
    await row.getByRole("button", {name: result, exact: true}).click();
    assert.equal(await page.locator("#inspect-name").textContent(), result);
    await page.locator("#view-source").click();
    assert.match(await page.locator("#read-source .active").textContent(), new RegExp("theorem " + result));
  }
  await page.locator('#inspect-axioms [data-axiom="lib_trunc_elim"]').click();
  assert.equal(await page.locator("#inspect-name").textContent(), "lib_trunc_elim");
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=prelude_library_construction&name=lib_trunc_elim/);
  await page.locator("#view-source").click();
  await page.locator("#result:not([hidden])").waitFor();
  assert.match(await page.locator("#read-source .active").textContent(), /lib_trunc_elim = postulate/);
  await selectProof(page, "truncation");
  await page.locator("#result:not([hidden])").waitFor();
  await page.locator('#read-source [data-name="truncation_elim"]').click();
  assert.equal(await page.locator("#inspect-name").textContent(), "truncation_elim");
  assert.match(await page.locator("#view-source").getAttribute("href"), /prelude_library_construction&name=lib_trunc_elim/);
  assert.ok(limitRequests.length > 0);
  assert.ok(limitRequests.every((url) => url.includes("?version=")));
  assert.deepEqual(errors, []);
  console.log(
    "Browser: axiom navigation, selection, reduction, rewrite, preview isolation, undo, save/import, and WASM worker passed",
  );
} finally {
  if (browser) await browser.close();
  await new Promise((r) => server.close(r));
}
