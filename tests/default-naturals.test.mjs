import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { checkTestModule, checkProgram } from "./check-program.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { numeral } from "../web/translator/numerals.mjs";

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
