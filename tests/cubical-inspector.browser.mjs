import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { chromium } from "playwright";
import { assertFreshBuild } from "../tools/build-stamp.mjs";
// The page loads the WASM kernel and the translator from web/dist.
assertFreshBuild();
const server = spawn("python3", ["tools/serve.py", "--port", "0"], { stdio: ["ignore", "pipe", "pipe"] });
server.stderr.resume();
let browser;
try {
  const port = await new Promise((resolve, reject) => {
    let output = "";
    const timer = setTimeout(() => reject(new Error("Server did not start")), 10000);
    server.once("error", reject);
    server.once("exit", code => { clearTimeout(timer); reject(new Error(`Server exited ${code}`)); });
    server.stdout.on("data", data => {
      output += data;
      const match = output.match(/127\.0\.0\.1:(\d+)\//);
      if (match) { clearTimeout(timer); resolve(match[1]); }
    });
  });
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors = []; page.on("pageerror", error => errors.push(error.message));
  const idle = async () => {
    try {
      await page.waitForFunction(() => !document.querySelector("#check").disabled && document.querySelector("#check-loader").hidden);
    } catch (error) {
      console.error(await page.locator("#diagnostic").textContent(), errors); throw error;
    }
  };
  const inspected = name => page.waitForFunction(name =>
    document.querySelector("#inspect-name").textContent === name &&
    !document.querySelector("#kernel-view").disabled, name);
  const openProof = async (proof, name) => {
    await page.goto(`http://127.0.0.1:${port}/proof.html?proof=${proof}&name=${name}`);
    await idle(); await inspected(name);
  };
  // An example opened in the workspace keeps its source in #source=… while the
  // quick reference's links scroll and move focus, so a reload reopens it.
  const example = Buffer.from("def kept_after_reload : Nat := 7;").toString("base64")
    .replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  await page.goto(`http://127.0.0.1:${port}/proof.html?example=1#source=${example}`); await idle();
  await page.locator("#guide-link").click();
  assert.equal(await page.locator("#language-guide").getAttribute("open"), "");
  await page.locator('.quick-topics a[href="#quick-paths"]').click();
  assert.equal(new URL(page.url()).hash, `#source=${example}`, "a topic link keeps the example's source");
  assert.equal(await page.evaluate(() => document.activeElement?.id), "quick-paths");
  assert.ok(await page.locator("#quick-paths").evaluate(heading => heading.getBoundingClientRect().top < innerHeight));
  await page.locator('.quick-topics a[href="#quick-universes"]').focus();
  await page.keyboard.press("Enter");
  assert.equal(await page.evaluate(() => document.activeElement?.id), "quick-universes", "Enter moves focus to the topic");
  assert.equal(new URL(page.url()).hash, `#source=${example}`);
  await page.reload(); await idle();
  assert.match(await page.locator("#editor").inputValue(), /kept_after_reload/);
  // An inductive header wrapped over lines keeps its h-level keyword, which
  // the highlighter finds in the whole source, not the line alone (H1).
  const wrapped = Buffer.from("inductive Wrapped(\n  A : U0\n) : prop {\n  point(a : A);\n}\n").toString("base64")
    .replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  await page.goto(`http://127.0.0.1:${port}/proof.html?example=1&experimental=h1#source=${wrapped}`); await idle();
  await page.locator("#read-mode").click();
  const modifier = page.locator("#read-source .source-line").nth(2).locator("span, button").filter({ hasText: /^prop$/ });
  assert.equal(await modifier.count(), 1, "the modifier is a token of its own");
  assert.match(await modifier.getAttribute("class"), /keyword/);
  await openProof("suspension", "S1");
  for (const name of ["Suspension", "north", "south", "meridian", "suspension_induction", "suspension_meridian_beta"]) {
    const link = page.locator(`#read-source button[data-name="${name}"]`).first();
    assert.ok(await link.count(), `${name} has a source reference`);
    assert.doesNotMatch(await link.getAttribute("class"), /keyword|macro/);
    await link.click(); await inspected(name);
    assert.ok((await page.locator("#kernel-expression").textContent()).length > 0);
    assert.equal(await page.locator("#view-source").isVisible(), true);
  }
  await openProof("circle_group_identity", "circle_group_isomorphism");
  await page.locator('#read-source button[data-name="refl"]').first().click(); await inspected("refl");
  assert.match(await page.locator("#kernel-type").textContent(), /base/);
  await page.locator('#read-source button[data-name="="]').first().click(); await inspected("=");
  assert.match(await page.locator("#kernel-expression").textContent(), /CircleLoopGroup/);
  await page.locator('#read-source button[data-name="winding"]').first().click(); await inspected("winding");
  assert.match(await page.locator("#view-source").getAttribute("href"), /proof=circle/);
  await openProof("euclid", "euclid");
  assert.equal(await page.locator(".library").count(), 0);
  const sourceBounds = await page.locator("#source-panel").boundingBox();
  const resultsBounds = await page.locator("#result").boundingBox();
  assert.ok(resultsBounds.y >= sourceBounds.y + sourceBounds.height);
  assert.equal(await page.locator("#kernel-expression").textContent(), "euclid");
  await page.locator("#toggle-kernel-body").click();
  assert.match(await page.locator("#kernel-expression").textContent(), /λ.*n/);
  await page.locator("#toggle-kernel-body").click();
  const width = (await page.locator(".inspector").boundingBox()).width;
  await page.locator("#widen-inspector").click();
  assert.ok((await page.locator(".inspector").boundingBox()).width > width);
  await page.locator('.source-line [data-name="hd"]').first().click(); await inspected("hd");
  assert.equal(await page.locator("#kernel-type").textContent(), "Divides(succ(succ(i)),m)");
  assert.equal(await page.locator("#kernel-expression").textContent(), "hd");
  assert.equal(await page.locator("#kernel-context-list button").first().textContent(), "n");
  await page.locator('#kernel-type [data-name="i"]').click(); await inspected("i");
  assert.equal(await page.locator("#kernel-type").textContent(), "Nat");
  await page.locator("#back").click(); await inspected("hd");
  await page.locator('#kernel-context-list button').first().click(); await inspected("n");
  await page.locator("#back").click(); await inspected("hd");
  await page.locator("#kernel-view").selectOption("raw");
  assert.match(await page.locator("#kernel-type").textContent(), /"Fst"/);
  await page.locator("#kernel-view").selectOption("expanded");
  assert.match(await page.locator("#kernel-type").textContent(), /prime_divisor_exists/);
  await page.locator("#kernel-view").selectOption("notation");
  assert.equal(await page.locator("#kernel-type").textContent(), "Divides(succ(succ(i)),m)");
  const popup = page.waitForEvent("popup");
  await page.locator("#open-kernel-type").click();
  const workbench = await popup;
  workbench.on("pageerror", error => errors.push(error.message));
  await workbench.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  // It opens on the kernel graph, the instruction kernel's derivation.
  assert.equal(await workbench.locator("#workbench-view").inputValue(), "graph");
  await workbench.locator("#graph-listing .graph-row").first().waitFor();
  await workbench.locator("#workbench-view").selectOption("math");
  assert.equal(await workbench.locator("#expression").textContent(), "Divides(succ(succ(i)),m)");
  assert.match(await workbench.locator("#context").textContent(), /n :Nat/);
  await workbench.locator("#fold-names").uncheck();
  assert.match(await workbench.locator("#expression").textContent(), /prime_divisor_exists/);
  await workbench.locator("#fold-names").check();
  await workbench.locator('#expression [data-name="i"]').click();
  await workbench.waitForFunction(() => document.querySelector("#name").textContent === "i");
  await workbench.locator("#back").click();
  await workbench.locator("details summary").click();
  // The exported type is itself a U0 term: replace it with Nat and recheck.
  await workbench.locator("#syntax").fill('{"tag":"Nat"}');
  await workbench.locator("#check").click();
  assert.equal(await workbench.locator("#expression").textContent(), "Nat");
  await workbench.locator("#syntax").fill('{"tag":"Var","name":"missing"}');
  await workbench.locator("#check").click();
  assert.equal(await workbench.locator("#diagnostic").isVisible(), true);
  assert.equal(await workbench.locator("#normalize").isDisabled(), true);
  await workbench.close();

  const assemblyPopup = page.waitForEvent("popup");
  await page.locator("#open-kernel-assembly").click();
  const assemblyBench = await assemblyPopup;
  assemblyBench.on("pageerror", error => errors.push(error.message));
  await assemblyBench.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  assert.equal(await assemblyBench.locator("#workbench-view").inputValue(), "assembly");
  assert.equal(await assemblyBench.locator("#mathematical-view").isVisible(), false);
  assert.ok(await assemblyBench.locator(".assembly-table tbody tr").count() > 0);
  assert.match(await assemblyBench.locator(".assembly-roots").textContent(), /Context/);
  const reference = assemblyBench.locator('.assembly-table tr[data-opcode="CC_DEFREF"]').first();
  await reference.locator("[data-expand-definition]").click();
  assert.equal(await assemblyBench.locator(".assembly-table tr.selected").count(), 1);
  const operand = assemblyBench.locator(".assembly-table .assembly-reference").first();
  const handle = await operand.getAttribute("data-handle"); await operand.click();
  assert.equal(await assemblyBench.locator(".assembly-table tr.selected").getAttribute("id"), `assembly-node-${handle}`);
  // The kernel graph derives the view again in instruction mode, and its
  // node links lead back into the assembly's syntax graph.
  await assemblyBench.locator("#workbench-view").selectOption("graph");
  assert.match(await assemblyBench.locator("#graph-status").textContent(), /^\d+ judgements?, \d+ highlighted steps?; #\d+ is the conclusion\.$/);
  // hd is a local definition over n : Nat, derived with its context entry.
  assert.match(await assemblyBench.locator(".graph-row.graph-root .graph-statement").textContent(),
    /^\{n : Nat\} ⊢ prime_divisor_exists\(.*\)\.2\.2 : Divides\(/);
  // A lookup's definition is derived on request, as the lookup's premise, or
  // says which rule it still needs.
  const rows = await assemblyBench.locator(".graph-row").count();
  const expand = assemblyBench.locator(".graph-expand").first();
  const name = (await expand.textContent()).replace("Derive the body of ", "");
  await expand.click();
  const outcome = assemblyBench.locator(".graph-definition", { hasText: new RegExp(`^(${name} is defined by #\\d+|The body of ${name} is not in instruction mode yet)`) });
  assert.equal(await outcome.count(), 1);
  assert.ok(await assemblyBench.locator(".graph-row").count() >= rows);
  await assemblyBench.locator(".graph-row.graph-root .graph-node").first().click();
  assert.equal(await assemblyBench.locator("#workbench-view").inputValue(), "assembly");
  assert.equal(await assemblyBench.locator(".assembly-table tr.selected").count(), 1);
  const downloaded = assemblyBench.waitForEvent("download");
  await assemblyBench.locator("#assembly-download").click();
  assert.match((await downloaded).suggestedFilename(), /\.ast\.txt$/);
  await assemblyBench.locator("#workbench-view").selectOption("math");
  assert.equal(await assemblyBench.locator("#mathematical-view").isVisible(), true);
  assert.equal(await assemblyBench.locator("#type").textContent(), "Divides(succ(succ(i)),m)");
  assert.ok((await assemblyBench.locator("#syntax").inputValue()).length > 0);
  await assemblyBench.locator("#workbench-view").selectOption("assembly");
  await assemblyBench.locator("#source-back").click();
  await assemblyBench.waitForFunction(() => document.querySelector("#inspect-name").textContent === "hd" && !document.querySelector("#kernel-view").disabled);
  await assemblyBench.close();

  await page.locator('.source-line [data-name="prime_divisor_exists"]').first().click();
  await inspected("prime_divisor_exists"); await page.locator("#view-source").click(); await idle();
  assert.match(page.url(), /proof=primes/);
  await page.locator("#back").click(); await inspected("prime_divisor_exists");
  assert.match(page.url(), /proof=euclid/);

  await openProof("group_univalence", "group_isomorphism_is_equality");
  const groupType = await page.locator("#kernel-type").textContent();
  assert.match(groupType, /GroupIso/);
  assert.doesNotMatch(groupType, /G\d|H\d/);
  await page.locator("#toggle-kernel-body").click();
  const derived = page.locator('#kernel-expression [data-name="ua"]').first();
  await derived.click(); await inspected("ua");
  assert.match(await page.locator("#inspect-description").textContent(), /introduces no axiom/);

  await openProof("field_logic", "FieldExists");
  assert.match(await page.locator("#kernel-expression").textContent(), /‖/);
  await page.locator("#kernel-truncation-sugar").uncheck();
  assert.match(await page.locator("#kernel-expression").textContent(), /Truncate/);
  await page.locator('#kernel-expression [data-name="Truncate"]').first().click();
  await inspected("Truncate");

  await openProof("cubical_paths", "reverse_twice");
  await page.locator('.source-line').filter({ hasText: "fun (i : Interval) => p @ flip(i)" }).locator('[data-name="p"]').click();
  await inspected("p");
  assert.match(await page.locator("#kernel-context-list").textContent(), /Interval coordinates/);
  await page.setViewportSize({ width: 600, height: 900 });
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
  await page.setViewportSize({ width: 1440, height: 1000 });
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`def N := Nat;
    def IdentityType(A : U0) := A;
    def Alias := IdentityType(N);
    def id(n : Nat) := n;
    def value := typed(Alias, id(0));`);
  await page.locator("#check").click(); await idle(); await inspected("value");
  const reductionPopup = page.waitForEvent("popup");
  await page.locator("#open-kernel-expression").click();
  const reductionBench = await reductionPopup;
  reductionBench.on("pageerror", error => errors.push(error.message));
  await reductionBench.waitForFunction(() => document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  await reductionBench.locator("#workbench-view").selectOption("math");
  const chooseReduction = async (side, kind, path = []) => {
    const before = await reductionBench.locator("#syntax").inputValue();
    await reductionBench.locator(`#${kind}-${side}`).click();
    assert.equal(await reductionBench.locator("#syntax").inputValue(), before, "highlighting must not reduce");
    const site = reductionBench.locator(`#${side} [data-reduction-path='${JSON.stringify(path)}']`);
    if (kind === "beta") await site.press("Enter"); else await site.click();
  };
  assert.equal(await reductionBench.locator("#type").textContent(), "Alias");
  await chooseReduction("type", "delta");
  assert.equal(await reductionBench.locator("#type").textContent(), "IdentityType(N)");
  await chooseReduction("type", "delta", ["fn"]);
  assert.match(await reductionBench.locator("#type").textContent(), /λ/);
  await chooseReduction("type", "beta");
  assert.equal(await reductionBench.locator("#type").textContent(), "N");
  await chooseReduction("type", "delta");
  assert.equal(await reductionBench.locator("#type").textContent(), "Nat");
  await reductionBench.locator("#back").click();
  assert.equal(await reductionBench.locator("#type").textContent(), "N");
  await reductionBench.locator("#normalize-type").click();
  assert.equal(await reductionBench.locator("#type").textContent(), "Nat");
  await chooseReduction("expression", "delta", ["arg", "fn"]);
  assert.match(await reductionBench.locator("#reduction-status").textContent(), /δ expression: id/);
  await chooseReduction("expression", "beta");
  await chooseReduction("expression", "beta");
  assert.equal(await reductionBench.locator("#expression").textContent(), "0");
  await reductionBench.locator("#beta-expression").click();
  assert.match(await reductionBench.locator("#reduction-status").textContent(), /No β sites/);
  await reductionBench.locator("#back").click();
  assert.match(await reductionBench.locator("#expression").textContent(), /λ/);
  await reductionBench.locator("#normalize").click();
  assert.equal(await reductionBench.locator("#expression").textContent(), "0");
  await reductionBench.locator("details summary").click();
  const ref = { tag: "DefRef", name: "cubical_paths__id" };
  const repeated = { tag: "App", fn: ref, arg: { tag: "App", fn: ref, arg: { tag: "Zero" } } };
  await reductionBench.locator("#syntax").fill(JSON.stringify(repeated));
  await reductionBench.locator("#check").click();
  await reductionBench.locator("#delta-expression").click();
  assert.equal(await reductionBench.locator("#expression .reduction-site").count(), 2);
  assert.equal(await reductionBench.locator("#type .reduction-site").count(), 0);
  await reductionBench.keyboard.press("Escape");
  assert.equal(await reductionBench.locator(".reduction-site").count(), 0);
  assert.deepEqual(JSON.parse(await reductionBench.locator("#syntax").inputValue()), repeated);
  await chooseReduction("expression", "delta", ["arg", "fn"]);
  assert.equal(await reductionBench.locator("#name").textContent(), "value", "reducing a name must not navigate to it");
  const reducedOccurrence = JSON.parse(await reductionBench.locator("#syntax").inputValue());
  assert.equal(reducedOccurrence.fn.tag, "DefRef");
  assert.equal(reducedOccurrence.arg.fn.tag, "Lam");
  await chooseReduction("expression", "beta", ["arg"]);
  const identity = { tag: "Lam", name: "x", domain: { tag: "Nat" }, body: { tag: "Var", name: "x" } };
  const nestedBeta = { tag: "App", fn: identity, arg: { tag: "App", fn: identity, arg: { tag: "Zero" } } };
  await reductionBench.locator("#syntax").fill(JSON.stringify(nestedBeta));
  await reductionBench.locator("#check").click();
  await reductionBench.locator("#beta-expression").click();
  assert.equal(await reductionBench.locator("#expression .reduction-site").count(), 2);
  await reductionBench.locator('#expression [data-reduction-path=\'["arg"]\']').click();
  const chosenInner = JSON.parse(await reductionBench.locator("#syntax").inputValue());
  assert.equal(chosenInner.fn.tag, "Lam");
  assert.equal(chosenInner.arg.tag, "Zero");
  await reductionBench.locator("#back").click();
  assert.deepEqual(JSON.parse(await reductionBench.locator("#syntax").inputValue()), nestedBeta);
  await reductionBench.locator("#syntax").fill(JSON.stringify(repeated));
  await reductionBench.locator("#check").click();
  await reductionBench.locator("#delta-expression").click();
  await reductionBench.locator("#unhighlight").click();
  assert.equal(await reductionBench.locator(".reduction-site").count(), 0);
  await reductionBench.locator("#delta-expression").click();
  await reductionBench.locator("#syntax").fill('{"tag":"Succ","value":{"tag":"Zero"}}');
  assert.equal(await reductionBench.locator(".reduction-site").count(), 0);
  await reductionBench.locator("#unhighlight").click();
  assert.equal(await reductionBench.locator("#syntax").inputValue(), '{"tag":"Succ","value":{"tag":"Zero"}}');
  assert.equal(await reductionBench.locator("[data-reduction]:enabled").count(), 0);
  await reductionBench.close();
  await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`import primes;
    simp_rule nat_add_zero;
    def frozen(n : Nat) : n + 0 = n { simp; }
  `);
  await page.locator("#check").click(); await idle();
  await page.locator('#read-source button[data-name="simp"]').click(); await inspected("simp");
  assert.equal(await page.locator("#rewrite-trace button").count(),1);
  await page.locator("#rewrite-trace button").click(); await inspected("simp step 1");
  await page.locator("#back").click(); await inspected("simp");
  assert.equal(await page.locator("#freeze-simp").isVisible(),true);
  await page.locator("#freeze-simp").click(); await idle();
  assert.match(await page.locator("#editor").inputValue(),/simp only \[nat_add_zero\];/);
  assert.equal(await page.locator("#diagnostic").isVisible(),false);
  if(!await page.locator("#editor").isVisible()) await page.locator("#edit-mode").click();
  await page.locator("#editor").fill(`def generic_calc(U < UU0, x : Nat) : x = x {
      calc { x = x by refl(x); }
    }
    def generic_simp(U < UU0, f : Nat -> Nat, n : Nat, h : f(n) = n) : f(n) = n {
      simp [h];
    }`);
  await page.locator("#check").click(); await idle();
  await page.locator('#read-source button[data-name="calc"]').click(); await inspected("calc");
  assert.match(await page.locator("#kernel-type").textContent(),/=/);
  await page.locator('#read-source button[data-name="by"]').click(); await inspected("calc step 1");
  await page.locator('#read-source button[data-name="simp"]').click(); await inspected("simp");
  assert.equal(await page.locator("#rewrite-trace button").count(),1);
  // One check covers every level, so a generic proof is offered the edit too.
  assert.equal(await page.locator("#freeze-simp").isVisible(),true);
  const genericTransfer=await page.evaluate(async()=>{
    const [{default:createCubical},{CubicalProgram},{saveWorkbenchTransfer}]=await Promise.all([
      import("/dist/cubical.mjs"),import("/cubical-program.mjs"),import("/workbench-transfer.mjs")]);
    const source=`import primes;
      def generic(U < UU0, n : Nat) : n + 0 = n {
        calc { n + 0 = n by nat_add_zero(n); }
      }`;
    const program=new CubicalProgram(await createCubical(),async name=>
      (await fetch(`/archive/first-library/${name}.cubist`)).text());
    try {
      const result=await program.check(source,"browser_generic_calc");
      const offset=source.indexOf("by nat_add_zero");
      const step=result.links.find(link=>link.start===offset&&link.role==="calculation step");
      return saveWorkbenchTransfer(program.export(step.binding));
    } finally {program.dispose();}
  });
  await page.goto(`http://127.0.0.1:${port}/workbench.html?transfer=${genericTransfer}`);
  await page.waitForFunction(()=>document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  assert.equal(await page.locator("#name").textContent(),"calc step 1");
  assert.match(await page.locator("#type").textContent(),/=/);
  const sharedTransfer=await page.evaluate(async()=>{
    const [{default:createCubical},{CubicalProgram},{saveWorkbenchTransfer}]=await Promise.all([
      import("/dist/cubical.mjs"),import("/cubical-program.mjs"),import("/workbench-transfer.mjs")]);
    let source="def shared(F : U0 -> U0 -> U0, A : U0) : 0 = 0 { let T0 := A;";
    for(let i=1;i<=28;i++)source+=`let T${i} := F(T${i-1},T${i-1});`;
    source+="have h : forall x : T28. x = x { intro x; exact path i => x; } rfl; }";
    const program=new CubicalProgram(await createCubical(),()=>{throw Error("No imports");});
    try {
      const result=await program.check(source,"browser_shared_inspection");
      const h=result.links.find(link=>link.name==="h");
      return saveWorkbenchTransfer(program.export(h.binding));
    } finally {program.dispose();}
  });
  await page.goto(`http://127.0.0.1:${port}/workbench.html?transfer=${sharedTransfer}`);
  await page.waitForFunction(()=>document.querySelector("#status")?.textContent.startsWith("Cubical C checked"));
  assert.match(await page.locator("#syntax").inputValue(),/Raw syntax exceeds the display limit/);
  assert.equal(await page.locator("#check").isDisabled(),true);
  assert.ok((await page.locator("#expression").textContent()).length>0);
  // An archive proof imports only from the archive, as the CLI checks it: in
  // the default Euclid page, importing the rebuilt library leaves the check
  // incomplete, while the library's own page imports it.
  // The page keeps an edited draft across visits, so each edit starts from
  // the repository's source.
  const statusAfterImport = async (proof, root, header) => {
    const original = await (await page.request.get(`http://127.0.0.1:${port}/${root}/${proof}.cubist`)).text();
    await page.goto(`http://127.0.0.1:${port}/proof.html?proof=${proof}`); await idle();
    if (!await page.locator("#editor").isVisible()) await page.locator("#edit-mode").click();
    await page.locator("#editor").fill(`${header}\n${original}`);
    await page.locator("#check").click(); await idle();
    return page.locator("#status").textContent();
  };
  assert.match(await statusAfterImport("euclid", "archive/first-library", "import classical_axioms;"), /check incomplete/);
  assert.match(await statusAfterImport("euclid", "archive/first-library", "import classical;"), /· checked/);
  assert.match(await statusAfterImport("universe_automorphisms", "library", "import naturals;"), /· checked/);
  assert.deepEqual(errors, []);
  console.log("PASS cubical inspector: folding, navigation, simp trace/freeze, generic transfer, bounded raw syntax, workbench editing, and archive-isolated imports");
} finally { await browser?.close(); server.kill(); }
