import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { checkTestModule, checkProgram } from "./check-program.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { numeral } from "../web/translator/numerals.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

test("default Nat uses binary arithmetic and readable mixed-carrier displays", async t => {
  const { program, result, get } = await checkTestModule(t, "default_naturals");
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output => output.verified && !output.axioms.length));
  assert.ok(program.kernel.signatures.has("bnat__BNat"));
  assert.ok(program.kernel.signatures.has("unat__UNat"));
  assert.ok(!program.kernel.signatures.has("nat__Nat"), "the public name is a binary alias, not another unary declaration");
  assert.deepEqual(result.prints.map(item => item.text), [
    "340282366920938463426481119284349108225", "unat.(10) = unat.(10)",
    "0b101 = 0b101", "10 = 10", "bnat.(1000)",
  ]);
  const type = get("default_wide_product").type;
  assert.match(type, /18446744073709551615/);
  assert.match(type, /340282366920938463426481119284349108225/);
  assert.doesNotMatch(type, /parsed_value|cons\(|digit\(/);
});

test("mathematical displays show computed binary magnitudes and retained rational literals", async t => {
  const { program, result, get } = await checkProgram(t, `import nat; import rationals;
    def large : Nat := nat.(18446744073709551615 + 1);
    def half : Q := rationals.(1/2);
  `, { name: "default_display" });
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.equal(program.inspect("default_display__large", { normalize: true }).expressionText, "18446744073709551616");
  assert.match(program.inspect("default_display__half").expressionText, /1\/2/);
  assert.equal(get("half").verified, true);
});

test("a same-named non-identity view cannot turn unary values into bare numerals", () => {
  const symbols = { unat__UNat: { printing: [{ notation: "view", identity: "original", identityNumeral: true }] } };
  assert.equal(sourceText(numeral(10), symbols, 4000, { selection: "view", selectionIdentity: "original" }), "10");
  assert.equal(sourceText(numeral(10), symbols, 4000, { selection: "view", selectionIdentity: "shadow" }), "unat.(10)");
});

test("public natural notation stays binary under transitive unary imports", async t => {
  for (const [imports, shortType] of [
    ["import nat; import hlevels;", "UNat"],
    ["import hlevels; import nat;", "Nat"],
  ]) {
    const { result } = await checkProgram(t, `${imports}
      def short_zero : ${shortType} := zero;
      def wide : Nat := nat.(18446744073709551616);
      def dependent(U < UU0, P : Nat -> U, z : P(b_zero),
        step : forall n : Nat. P(n) -> P(bnat_succ(n))) := nat_peano(U, P, z, step, b_zero);
    `);
    assert.ok(result.complete, JSON.stringify(result.gaps));
  }
});

test("unary constructor patterns on default Nat explain its numerical induction view", async t => {
  const { result } = await checkProgram(t, `import nat; use nat;
    def wrong(n : Nat) : Nat := match n { zero => 0; succ(k) => k; };
  `);
  assert.equal(result.complete, false);
  assert.match(result.outputs.find(output => output.name === "wrong").reason, /Use nat_peano/);
});

test("mismatch and goal diagnostics preserve a shadowed notation's identity", async t => {
  const fallback = sourceReader();
  const { result, get } = await checkProgram(t, `import identity_reader;
    notation view { numeral(n : UNat) := succ(n); }
    use view;
    def mismatch : unat.(1) = unat.(2) := refl(unat.(1));
    def unfinished : unat.(1) = unat.(2) { simp only []; }
  `, { reader: async (name, importer) => name === "identity_reader"
    ? "import unat; notation view { numeral(n : UNat) := n; }"
    : fallback(name, importer) });
  assert.equal(result.complete, false);
  for (const name of ["mismatch", "unfinished"]) {
    assert.equal(get(name).verified, false);
    assert.match(get(name).reason, /unat\.\(1\) = unat\.\(2\)/, name);
  }
});
