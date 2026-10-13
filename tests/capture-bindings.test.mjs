import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import create from "../web/dist/cubical.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";
import { assertStage } from "./known-defect.mjs";
import { bindingCases } from "./fixtures/capture-bindings.mjs";

const module = await create(), library = sourceReader();
const baseline = JSON.parse(await readFile(new URL("./fixtures/capture-bindings-baseline.json", import.meta.url), "utf8"));

for (const c of bindingCases) test(`CB0: [${c.id}] ${c.contract}`, async t => {
  const { program, result, get } = await checkProgram(t, c.source, {
    module, reader: (name, importer) => c.fixtures?.[name] ?? library(name, importer),
  });
  // Imports and source ownership are active invariants even for a known
  // semantic defect. In particular, an imported binder's offset must never
  // be interpreted against the caller source, as happened in #219.
  assert.deepEqual(result.gaps.filter(gap => gap.module !== "main"), [], "all imported fixtures must check");
  for (const gap of result.gaps) {
    const source = program.sources[gap.module];
    assert.equal(typeof source, "string");
    if (gap.start != null) assert.ok(Number.isInteger(gap.start) && gap.start >= 0 && gap.start <= source.length,
      `${c.id}: primary start belongs to ${gap.module}`);
    if (gap.end != null) assert.ok(Number.isInteger(gap.end) && gap.end >= gap.start && gap.end <= source.length,
      `${c.id}: primary end belongs to ${gap.module}`);
  }
  const observed = {
    gaps: result.gaps.map(gap => [gap.module, gap.name, gap.code]),
    clients: Object.fromEntries(c.clients.map(name => [name, get(name).verified])),
    assumes: result.outputs.filter(output => output.verified && output.axioms?.length).map(output => output.name),
  };
  if (c.publication) observed.published = Object.values(program.symbols)
    .filter(output => output.verified && c.publication.some(name => output.name === name || output.name.startsWith(`${name}.`)))
    .map(output => output.name);
  assertStage(t, { observed, desired: c.desired, known: baseline.cases[c.id], id: c.id });
});

test("capture witness IDs are unique and known-defect records still name executable cases", () => {
  const ids = bindingCases.map(c => c.id);
  assert.equal(new Set(ids).size, ids.length);
  for (const id of Object.keys(baseline.cases)) assert.ok(ids.includes(id), id);
});

const ruleModel = `import hlevels; import nat;
theory Rules(U < UU0) { M : set U; rule : Nat; }
def selected : Rules(U0) := Rules.make(Nat, nat_is_set, zero);`;
for (const kind of ["simp_rule", "simp_set", "hlevel_rule"]) for (const imported of [false, true]) {
  test(`CB0: ${kind} ignores opened labels (${imported ? "imported" : "local"} registration)`, async t => {
    const hlevel = kind === "hlevel_rule";
    const definition = hlevel ? "def rule : IsSet(U0, Nat) := nat_is_set;"
      : "def rule(n : Nat) : add(n, zero) = n := nat_add_zero(n);";
    const directive = kind === "simp_set" ? "simp_set named_rules := [rule];" : `${kind} rule;`;
    const source = `${ruleModel}\n${definition}\nuse selected;\n${directive}`;
    const client = hlevel ? "def checked : IsSet(U0, Nat) { hlevel; }"
      : `def checked(n : Nat) : add(n, zero) = n { ${kind === "simp_set" ? "simp only [named_rules]" : "simp"}; }`;
    const { program, result, get } = await checkProgram(t, `${imported ? "import registered;" : source}\n${client}`, {
      module, reader: (name, importer) => name === "registered" ? source : library(name, importer),
    });
    assert.deepEqual(result.gaps, []);
    assert.ok(get("checked").verified);
    const registry = program.simpRegistries.get(imported ? "registered" : "main");
    const rules = kind === "simp_set" ? registry.sets.get("named_rules").rules
      : [...(hlevel ? registry.hlevel : registry.defaults).values()];
    assert.equal(rules.length, 1);
    const identity = `${imported ? "registered" : "main"}__rule`;
    assert.equal(rules[0].identity, hlevel ? identity : JSON.stringify({ tag: "DefRef", name: identity }));

    const missing = await checkProgram(t, `${ruleModel}\nuse selected;\n${directive}`, { module });
    assert.deepEqual(missing.result.gaps.map(gap => gap.code), ["E343"], "an opened-only rule stays missing");
  });
}
