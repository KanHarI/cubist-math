// Deterministic fuel and residual goals (HoTT roadmap A4 and A6; work plan
// L1.3): tactic searches spend counted fuel, the same in a fresh session and
// a reused one; fuel, the kernel's steps and the time limit fail apart; and an
// unfinished rw, simp, simpa or calc says where it stopped.
import test from "node:test";
import assert from "node:assert/strict";
import { readFile, mkdtemp, writeFile, rm } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { SEARCH_FUEL, DECLARATION_FUEL, SearchFuel, SearchFuelExhausted } from "../lib/cubical/fuel.mjs";

const read = path => readFile(new URL(`../${path}`, import.meta.url), "utf8");
// Modules resolve as in the CLI: the rebuilt library first, then the archive.
const readLibrary = name => read(`library/${name}.cubist`)
  .catch(error => { if (error.code !== "ENOENT") throw error; return read(`archive/first-library/${name}.cubist`); });

async function check(t, source, options = {}, warmup = []) {
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false, ...options });
  t.after(() => program.dispose());
  for (const [name, text] of warmup) await program.check(text, name);
  const result = await program.check(source, "fuel_example");
  return Object.fromEntries(result.outputs.filter(output => output.binding.startsWith("fuel_example__"))
    .map(output => [output.name, output]));
}

const tactics = `import naturals;

def add_zero_twice(n : Nat) : (n + 0) + 0 = n {
  simp only [nat_add_zero];
}
def rewritten(n, m : Nat, h : n = m) : n + 0 = m {
  rw [nat_add_zero(n)];
  exact h;
}
def through(n, m : Nat, h : n + 0 = m) : n = m {
  simpa only [nat_add_zero] using h;
}
def chain(n : Nat) : (n + 0) + 0 = n {
  calc {
    (n + 0) + 0 = n + 0 by nat_add_zero(n + 0);
    _ = n by nat_add_zero(n);
  }
}
def commuted(a, b : Nat) : a + b = b + a {
  simp only [nat_add_comm];
}
def growing(n, m : Nat, h : n = m) : n = m + 0 {
  simp only [<- nat_add_zero];
  exact h;
}
`;
const fuelOf = outputs => Object.fromEntries(Object.entries(outputs).map(([name, output]) =>
  [name, { status: output.status, reason: output.reason ?? null, failure: output.failure, fuel: output.searchFuel }]));

test("the default fuel is the recorded baseline's, several times what any measured search spent", async () => {
  const fixture = JSON.parse(await read("tests/fixtures/search-fuel.json"));
  assert.deepEqual({ ...SEARCH_FUEL }, fixture.defaults.search);
  assert.deepEqual({ ...DECLARATION_FUEL }, fixture.defaults.declaration);
  for (const [kind, { spent }] of Object.entries(fixture.most))
    assert.ok(SEARCH_FUEL[kind] >= 4 * Math.max(spent, fixture.floors[kind] ?? 0), kind);
  assert.ok(DECLARATION_FUEL.queries >= 4 * fixture.declarationQueries.spent);
  // What was measured, and how.
  assert.ok(fixture.revision && fixture.method && fixture.machine.node);
  assert.ok(fixture.workloads.some(workload => workload.name === "archive" && workload.gaps === 0));
});

test("fuel counts questions, not time: a fresh session and a reused one spend the same", async t => {
  const fresh = fuelOf(await check(t, tactics));
  // The reused session has checked other proofs first: the kernel's caches
  // are warm, and its step budget has been used.
  const warmup = [["warm_arithmetic", await read("docs/examples/proof-ergonomics/implemented/arithmetic.cubist")],
    ["warm_registered", await read("docs/examples/proof-ergonomics/implemented/registered-simp.cubist")]];
  const reused = fuelOf(await check(t, tactics, {}, warmup));
  assert.deepEqual(reused, fresh);
  // The inspector's records, and the replays behind its freeze suggestions,
  // spend fuel of their own: every view spends the same.
  assert.deepEqual(fuelOf(await check(t, tactics, { collectReferences: true })), fresh);
  // Every tactic spent fuel, and the checked ones were within it.
  for (const name of ["add_zero_twice", "rewritten", "through", "chain"]) assert.equal(fresh[name].status, "checked-native-cubical", name);
  assert.ok(fresh.add_zero_twice.fuel.searches >= 1 && fresh.add_zero_twice.fuel.most.candidates > 0);
  assert.ok(fresh.chain.fuel.queries > 0, "calc asks the kernel, and the declaration counts it");
});

test("a search out of fuel stops the same way in every session, with the fuel it ran out of and where", async t => {
  const limits = { searchFuel: { ...SEARCH_FUEL, candidates: 3 } };
  const fresh = fuelOf(await check(t, tactics, limits));
  const reused = fuelOf(await check(t, tactics, limits,
    [["warm_arithmetic", await read("docs/examples/proof-ergonomics/implemented/arithmetic.cubist")]]));
  assert.deepEqual(reused, fresh);
  assert.equal(fresh.growing.failure, "fuel");
  assert.match(fresh.growing.reason, /^simp ran out of search fuel: 3 candidate rules tried\. Remaining goal: n \+ 0 \+ 0 = m \+ 0\. 2 rewrites changed the left side, using nat_add_zero\./);
  // A search that needs less still checks.
  assert.equal(fresh.rewritten.status, "checked-native-cubical");
});

test("a declaration's fuel bounds every kernel question it asks, its searches' included", async t => {
  const outputs = await check(t, "def reflexive(n : Nat) : n = n {\n  rfl;\n}\n", { declarationFuel: { queries: 1 } });
  assert.equal(outputs.reflexive.failure, "fuel");
  assert.match(outputs.reflexive.reason, /^The declaration's elaboration ran out of search fuel: 1 kernel queries\./);
  const roomy = await check(t, "def reflexive(n : Nat) : n = n {\n  rfl;\n}\n");
  assert.equal(roomy.reflexive.status, "checked-native-cubical");
});

test("fuel, the kernel's steps and the time limit are three kinds of failure", async t => {
  const source = "import naturals;\n\ndef twice(n : Nat) : (n + 0) + 0 = n {\n  simp only [nat_add_zero];\n}\n";
  const fuel = await check(t, source, { searchFuel: { ...SEARCH_FUEL, queries: 1 } });
  assert.equal(fuel.twice.failure, "fuel");
  // The kernel's own budget per operation: every instruction of this
  // declaration may take one step.
  let program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false,
    onDeclarationStart(module) { if (module === "fuel_example") { program.kernel.stepBudget = 1n; program.kernel.module._cb_step_budget(program.kernel.handle, 1, 0); } } });
  t.after(() => program.dispose());
  const steps = (await program.check(source, "fuel_example")).outputs[0];
  assert.equal(steps.failure, "budget");
  assert.match(steps.reason, /budget exhausted/);
  // The safety timeout.
  const timed = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false,
    onDeclarationStart(module) { if (module === "fuel_example") timed.kernel.setDeadline(0.000001); } });
  t.after(() => timed.dispose());
  const late = (await timed.check(source, "fuel_example")).outputs[0];
  assert.equal(late.failure, "deadline");
  assert.match(late.reason, /Declaration time limit exceeded/);
});

test("unfinished rw, simp, simpa and calc show the remaining goal, the side that changed and the rules that fired", async t => {
  const outputs = await check(t, `import naturals;

def simp_unfinished(n, m : Nat) : n + 0 = m {
  simp only [nat_add_zero];
}
def simp_nothing(n, m : Nat) : n = m {
  simp only [nat_add_zero];
}
def rw_unfinished(n, m : Nat) : n + 0 = m {
  rw [nat_add_zero(n)];
}
def rw_missing(n : Nat) : (n + 0) + (n + 0) = (n + 0) + n {
  rw [nat_add_zero(n)] at lhs occurrence 3;
}
def simpa_mismatch(n, m : Nat, h : n + 0 = m) : m = n {
  simpa only [nat_add_zero] using h;
}
def calc_end(n : Nat) : n + 0 = succ(n) {
  calc {
    n + 0 = n by nat_add_zero(n);
  }
}
def calc_step(n, m : Nat) : n + 0 = n {
  calc {
    n + 0 = n by nat_add_zero(n);
    m = n by nat_add_zero(n);
  }
}
def commuted(a, b : Nat) : a + b = b + a {
  simp only [nat_add_comm];
}
def growing(n, m : Nat, h : n = m) : n = m + 0 {
  simp only [<- nat_add_zero];
  exact h;
}
`);
  const reason = name => outputs[name].reason;
  assert.match(reason("simp_unfinished"), /unresolved equality goal; add a following proof statement\. Remaining goal: n = m\. 1 rewrite changed the left side, using nat_add_zero\./);
  assert.match(reason("simp_nothing"), /Remaining goal: n = m\. No rule fired\./);
  assert.match(reason("rw_unfinished"), /^rw left an unresolved equality goal; add a following proof statement\. Remaining goal: n = m\. 1 rewrite changed the left side, using nat_add_zero\(n\)\./);
  assert.match(reason("rw_missing"), /^Rewrite occurrence 3 was not found \(2 eligible matches\)\. Remaining goal: n \+ 0 \+ \(n \+ 0\) = n \+ 0 \+ n\./);
  assert.match(reason("simpa_mismatch"), /Simplifying the supplied type: 1 rewrite changed the left side, using nat_add_zero\. Simplifying the goal: No rule fired\./);
  assert.match(reason("calc_end"), /^calc final endpoint does not match the goal\. The chain ends at n; the goal's right side is succ\(n\)\./);
  assert.match(reason("calc_step"), /^calc step left endpoint does not match the preceding endpoint\. The step starts at m; the chain so far ends at n\./);
  // A cycle names the rules that make it.
  assert.match(reason("commuted"), /^Simplification cycle detected in the selected rules\. nat_add_comm returned the goal to where it was 2 rewrites earlier\. Remaining goal: a \+ b = b \+ a\./);
  // A bound says where the search stopped; a long goal is cut short.
  assert.match(reason("growing"), /^Simplification rewrite budget exceeded\. Remaining goal: n \+ 0 \+ 0 .*… 64 rewrites changed the left side, using nat_add_zero\./);
});

test("fuel: a closed search's spending counts toward its declaration, and only an open one's limits apply", () => {
  const declaration = new SearchFuel("The declaration's elaboration", { queries: 3 }, { declaration: true });
  const search = new SearchFuel("simp", { ...SEARCH_FUEL, queries: 2 }, { parent: declaration });
  search.spend("queries"); search.spend("queries");
  // The search's third query is over its limit: it is refused before it
  // reaches the declaration's count.
  assert.throws(() => search.spend("queries"), error => error instanceof SearchFuelExhausted && error.kind === "fuel" && error.fuel === "queries");
  assert.deepEqual([search.used.queries, declaration.used.queries], [3, 2]);
  search.close();
  // Rebuilding the proof after the search: no longer the search's, still the declaration's.
  search.spend("queries");
  assert.deepEqual([search.used.queries, declaration.used.queries], [3, 3]);
  assert.throws(() => search.spend("queries"), /declaration's elaboration ran out of search fuel: 3 kernel queries/);
});

test("the CLI reports the same residual goals as the checker the browser runs", async t => {
  const source = `import naturals;

def simp_unfinished(n, m : Nat) : n + 0 = m {
  simp only [nat_add_zero];
}

def rw_unfinished(n, m : Nat) : n + 0 = m {
  rw [nat_add_zero(n)];
}

def commuted(a, b : Nat) : a + b = b + a {
  simp only [nat_add_comm];
}
`;
  const directory = await mkdtemp(join(tmpdir(), "cubist-fuel-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "residual.cubist"), source);
  const cli = fileURLToPath(new URL("../cli/repl.mjs", import.meta.url));
  const run = spawnSync(process.execPath, [cli, "check", "residual.cubist"], { cwd: directory, encoding: "utf8", timeout: 120000 });
  assert.equal(run.status, 1, run.stderr);
  // A failed check lists its gaps on stderr.
  const reported = Object.fromEntries(JSON.parse(run.stderr.slice(run.stderr.indexOf("["))).map(gap => [gap.name, gap.reason]));
  // The browser's worker runs CubicalProgram on the same runtime modules.
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  t.after(() => program.dispose());
  const checked = Object.fromEntries((await program.check(source, "residual")).outputs.map(output => [output.name, output.reason]));
  assert.deepEqual(reported, checked);
  for (const reason of Object.values(reported)) assert.match(reason, /Remaining goal: /);
});

test("a declaration's closing check and admission, and an evaluation, are on fuel", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check("def x := 0;\nevaluate x expecting 0;\n", "fuel_example");
  assert.ok(result.outputs[0].searchFuel.queries >= 2, JSON.stringify(result.outputs[0].searchFuel));
  const evaluation = result.directiveFuel.find(directive => directive.kind === "evaluate");
  assert.ok(evaluation.searchFuel.queries >= 2, JSON.stringify(evaluation));
  // A declaration whose fuel cannot cover its admission fails as fuel.
  const tight = await check(t, "def x := 0;\n", { declarationFuel: { queries: 1 } });
  assert.equal(tight.x.failure, "fuel");
});

test("a search's own questions and rewrites are on its fuel", async t => {
  const outputs = await check(t, `import naturals;

def nothing(n : Nat) : n = n {
  simp only [];
}
def rewritten(n, m : Nat, h : n = m) : n + 0 = m {
  rw [nat_add_zero(n)];
  exact h;
}
def targeted(n, m : Nat, h : n = m) : n + 0 = m {
  rw [nat_add_zero(n)] at lhs;
  exact h;
}
`);
  // Reading the goal's endpoints is the search's question.
  assert.ok(outputs.nothing.searchFuel.most.queries > 0, JSON.stringify(outputs.nothing.searchFuel));
  for (const name of ["rewritten", "targeted"]) {
    assert.equal(outputs[name].status, "checked-native-cubical", name);
    assert.equal(outputs[name].searchFuel.most.rewrites, 1, name);
  }
});

test("registering simplification rules is a search, recorded on its directive", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check("import naturals;\n\nsimp_rule nat_add_zero priority 10;\nsimp_set units := [nat_add_zero, nat_add_succ];\n", "fuel_example");
  const rule = result.directiveFuel.find(directive => directive.kind === "simp_rule");
  const set = result.directiveFuel.find(directive => directive.kind === "simp_set");
  assert.equal(rule.searchFuel.searches, 1);
  assert.equal(set.searchFuel.searches, 2);
  assert.ok(rule.searchFuel.most.nodes > 0 && set.searchFuel.most.queries > 0);
  // The baseline includes these records.
  const fixture = JSON.parse(await read("tests/fixtures/search-fuel.json"));
  assert.match(fixture.method, /simp_rule/);
});

test("simpa out of fuel names the phase that stopped, where it stopped, and how far the supplied type got", async t => {
  const source = `import naturals;

def stopped(n, m : Nat, h : n + 0 = m) : m + 0 = n {
  simpa only [nat_add_zero] using h;
}
`;
  // The supplied type simplifies within the fuel; the goal's search runs out.
  const late = await check(t, source, { searchFuel: { ...SEARCH_FUEL, candidates: 7 } });
  assert.equal(late.stopped.failure, "fuel");
  assert.match(late.stopped.reason, /^simpa ran out of search fuel: 7 candidate rules tried\. Simplifying the goal stopped at m \+ 0 = n\. .* The supplied type had simplified to n = m\. 1 rewrite changed the left side, using nat_add_zero\./);
  // The fourth review of #74: the two goals are named together. A variable
  // introduced as add is named apart from the add that + prints in the
  // goal, and so in the supplied type too, where neither it nor the context
  // prints an add of its own.
  const named = await check(t, `import naturals;

def stopped : forall n : Nat. forall m : Nat. n = m -> m + 0 = n {
  intro add;
  intro m;
  intro h;
  simpa only [nat_add_zero] using h;
}
`, { searchFuel: { ...SEARCH_FUEL, candidates: 3 } });
  assert.match(named.stopped.reason, /Simplifying the goal stopped at m \+ 0 = (\w+)\. .* The supplied type had simplified to \1 = m\./);
  assert.doesNotMatch(named.stopped.reason, /simplified to add = m/);
  // The supplied type's search runs out first.
  const early = await check(t, source, { searchFuel: { ...SEARCH_FUEL, candidates: 1 } });
  assert.match(early.stopped.reason, /^simpa ran out of search fuel: 1 candidate rules tried\. Simplifying the supplied type stopped at n \+ 0 = m\./);
  assert.doesNotMatch(early.stopped.reason, /Remaining goal/);
});

test("a freeze suggestion's replay spends fuel of its own", async t => {
  // Not `only`, with a selected rule the proof does not use: the inspector
  // replays the simplification without it before suggesting `simp only`.
  const source = `import naturals;

def frozen(n : Nat) : (n + 0) + 0 = n {
  simp [nat_add_zero, nat_add_succ];
}
`;
  const run = async collectReferences => {
    const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences });
    t.after(() => program.dispose());
    return program.check(source, "fuel_example");
  };
  const inspected = await run(true), plain = await run(false);
  assert.equal(inspected.outputs[0].status, "checked-native-cubical");
  const suggestion = inspected.links.find(link => link.freeze);
  assert.equal(suggestion?.freeze.text, "simp only [nat_add_zero];");
  assert.deepEqual(inspected.outputs[0].searchFuel, plain.outputs[0].searchFuel);
});

test("preparing the rules is part of the tactic's search: out of fuel, it shows the unchanged goal", async t => {
  const outputs = await check(t, `def stopped(n, m : Nat, h : n = m) : n = m {
  simp only [h];
}
`, { searchFuel: { ...SEARCH_FUEL, queries: 1 } });
  assert.equal(outputs.stopped.failure, "fuel");
  assert.match(outputs.stopped.reason, /^Preparing the simplification rules ran out of search fuel: 1 kernel queries\. Remaining goal: n = m\. No rule fired\. at \d+:\d+$/);
});

test("asking for univalence is a question every time, cached or not", async t => {
  const source = "def u := ua(U0, Unit, Unit);\n";
  const cold = await check(t, source);
  const warm = await check(t, source, {}, [["warm_ua", "def v := ua(U0, Unit, Unit);\n"]]);
  assert.equal(cold.u.status, "checked-native-cubical");
  // Checking A and B, the request for the generic definition (which the cold
  // session also checks and admits), the closing check and admission.
  assert.equal(cold.u.searchFuel.queries, 5);
  assert.deepEqual(warm.u.searchFuel, cold.u.searchFuel);
});

test("the kernel's step budget is a safety bound outside the determinism guarantee", async t => {
  // Warm caches make a question cheaper, so near its budget the same query
  // can fail cold and pass warm. That is reported as the kernel's exhaustion,
  // never as fuel; the default budget (MAX_QUERY_STEPS) is far above what
  // checked proofs use, and there both sessions answer.
  const { CubicalKernel } = await import("../web/cubical-kernel.mjs");
  const { CubicalSyntax } = await import("../web/cubical-syntax.mjs");
  const session = async () => {
    const kernel = new CubicalKernel(await createCubical());
    t.after(() => kernel.dispose());
    kernel.stepBudget = 1n; kernel.module._cb_step_budget(kernel.handle, 1, 0);
    kernel.maxQuerySteps = 16n;
    return { kernel, syntax: new CubicalSyntax(kernel) };
  };
  const nat = { tag: "Nat" }, id = { tag: "Lam", name: "x", domain: nat, body: { tag: "Var", name: "x" } };
  const nest = depth => { let term = { tag: "Zero" }; for (let i = 0; i < depth; i++) term = { tag: "App", fn: id, arg: term }; return term; };
  const cold = await session();
  assert.throws(() => cold.kernel.head(cold.syntax.encode(nest(8))), error => error.kind === "budget");
  const warm = await session();
  warm.kernel.head(warm.syntax.encode(nest(4)));
  assert.ok(warm.kernel.head(warm.syntax.encode(nest(8))), "the warm session answers what the cold one could not");
  for (const roomy of [await session(), await session()]) {
    roomy.kernel.maxQuerySteps = 1280000000n;
    assert.ok(roomy.kernel.head(roomy.syntax.encode(nest(8))));
  }
});
