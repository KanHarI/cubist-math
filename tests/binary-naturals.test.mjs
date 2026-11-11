import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const literal = n => `0b${n.toString(2)}`;

test("decimal binary-natural input and computed printing preserve arbitrary precision", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const values = [0n, 1n, 9n, 10n, 99n, 100n, 1000n];
  for (const bits of [31n, 32n, 53n, 63n, 64n, 65n, 127n, 128n])
    values.push((1n << bits) - 1n, 1n << bits, (1n << bits) + 1n);
  const source = values.map((n, i) => `
    def decimal_${i} : ${n} = ${literal(n)} { rfl; }
    print(evaluate(bnat_succ(${n})));
  `).join("\n");
  const result = await program.check(`import bnat_notation; use bnat;\n${source}`, "decimal_binary");
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output => output.verified && !output.axioms.length));
  const printed = result.prints;
  assert.deepEqual(printed.map(d => d.text), values.map(n => String(n + 1n)));
  assert.ok(!program.kernel.definitions.has("bnat_unary__bnat_to_unat"), "decimal magnitudes need no unary conversion module");

  // Re-read the actual computed output through the checked source parser.
  const roundtrip = await program.check(`import bnat_notation; use bnat;\n${printed.map((d, i) =>
    `def roundtrip_${i} : ${d.text} = ${literal(values[i] + 1n)} { rfl; }`).join("\n")}`, "decimal_roundtrip");
  assert.ok(roundtrip.complete, JSON.stringify(roundtrip.gaps));
});

test("computed binary-natural printing follows the parser's declared notation", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader());
  t.after(() => program.dispose());
  const result = await program.check(`import bnat_notation;
    def probe : BNat := b_zero;
    notation decimal { literal(s : Lexeme) := bnat_literal(s); }
    print(evaluate(bnat.(0b0)));
    use decimal;
    print(evaluate(bnat.(0b101)));
    print(typeof(refl(0b101)));
    print(typeof(refl(1_000)));
    use unat;
    print(evaluate(bnat.(0b101)));
  `, "binary_printing_views");
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.deepEqual(result.prints.map(d => d.text),
    ["bnat.(0)", "5", "0b101 = 0b101", "1_000 = 1_000", "bnat.(5)"]);
});

test("binary arithmetic and comparison agree with independent integer results", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const pairs = [];
  for (let a = 0n; a < 8n; a++) for (let b = 0n; b < 8n; b++) pairs.push([a, b]);
  for (const bits of [31n, 32n, 63n, 64n, 65n]) {
    const n = 1n << bits;
    pairs.push([n - 1n, 1n], [n, n + 1n], [n + 1n, n - 1n],
      [n - 1n, n - 1n], [n + n / 2n, n + n / 2n - 1n]);
  }
  const proofs = [];
  for (const [i, [a, b]] of pairs.entries()) {
    const x = literal(a), y = literal(b);
    const equations = {
      add: `${x} + ${y} = ${literal(a + b)}`,
      mul: `${x} * ${y} = ${literal(a * b)}`,
      order: `bnat_compare(${x}, ${y}) = ${a < b ? "b_less" : a === b ? "b_equal" : "b_greater"}`,
      equal: `bnat_equal(${x}, ${y}) = ${a === b ? "Unit" : "Void"}`,
      le: `bnat_le(${x}, ${y}) = ${a <= b ? "Unit" : "Void"}`,
      lt: `bnat_lt(${x}, ${y}) = ${a < b ? "Unit" : "Void"}`,
      pred: `bnat_pred(${x}) = ${literal(a ? a - 1n : 0n)}`,
      succ: `bnat_succ(${x}) = ${literal(a + 1n)}`,
    };
    for (const [operation, equation] of Object.entries(equations))
      proofs.push(`def case_${i}_${operation} : ${equation} { rfl; }`);
  }
  const result = await program.check(`import bnat_notation; use bnat;\n${proofs.join("\n")}`, "binary_differential");
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.equal(result.outputs.length, proofs.length);
  assert.ok(result.outputs.every(output => output.verified && !output.axioms.length));
});

// Multiplication recurses on its first operand and adds its second, a term
// still to be computed when it is a recursive value, as factorial's step
// multiplies n by the factorial below it. Each addition substitutes the
// operand's parts under binders. On ABI 3 the kernel checked each binder's
// name against them, searching the operand's syntax for it, so a product
// nested to the right cost its term's size at every substitution:
// factorial(60) took 137,752,410 ticks, factorial(100) passed 10,000,000 in
// one query (K338), and 7^60 nested to the right 45,712,445, against 770,518
// nested to the left. A binder binds an index now, and instantiation visits
// only the nodes whose loose indices reach the one it replaces, so a closed
// operand is never searched (section 3.3 of
// docs/roadmaps/kernel/locally-nameless-kernel.md). The bounds are the
// stopgap's (branch kernel-fast-multiplication), unchanged. On the kernel's
// path alone, as the value form computes once the runtime is gone.
test("a product with a large operand still to be computed costs its arithmetic on the kernel's path", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false, runtimeEvaluation: false });
  t.after(() => program.dispose());
  const session = new ReplSession(program);
  const prepared = await session.run("import nat; use nat;");
  assert.deepEqual(prepared.filter(result => result.kind === "error").map(result => result.text), []);
  program.kernel.maxQuerySteps = 10000000n;
  const evaluated = async entry => {
    const before = program.kernel.work().querySteps;
    const [answer] = await session.run(`evaluate ${entry};`);
    assert.equal(answer.kind, "value", `${entry}: ${answer.text}`);
    return { text: answer.text, ticks: Number(program.kernel.work().querySteps - before) };
  };
  const factorial = n => { let f = 1n; for (let i = 2n; i <= n; i++) f *= i; return f; };
  const sixty = await evaluated("factorial(60)");
  assert.equal(sixty.text, String(factorial(60n)));
  assert.ok(sixty.ticks < 4000000, `factorial(60) took ${sixty.ticks} ticks`);
  // 100! has 525 bits, past the value form's display, which shows its low
  // bits: 2^97 divides it, and 2^98 does not.
  const hundred = await evaluated("factorial(100)");
  assert.ok(hundred.text.startsWith(`b_positive(${"bp_even(".repeat(97)}bp_odd(`), hundred.text.slice(0, 120));
  assert.ok(hundred.ticks < 12000000, `factorial(100) took ${hundred.ticks} ticks`);
  const nested = order => { let s = "1"; for (let i = 0; i < 60; i++) s = order === "right" ? `7 * (${s})` : `(${s}) * 7`; return s; };
  const right = await evaluated(nested("right")), left = await evaluated(nested("left"));
  assert.equal(right.text, String(7n ** 60n));
  assert.equal(left.text, String(7n ** 60n));
  assert.ok(right.ticks < 3 * left.ticks, `7^60 took ${right.ticks} ticks nested to the right, ${left.ticks} to the left`);
});

test("the complete binary core loads without unary naturals", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check("import bnat; def probe := bnat_add;", "binary_dependencies");
  assert.ok(result.complete, JSON.stringify(result.gaps));
  assert.ok(program.kernel.signatures.has("bnat__BNat"), "the binary carrier was loaded");
  assert.ok(!program.kernel.signatures.has("unat__UNat"), "the binary core must not import unary naturals");
  const equality = await program.check("import bnat_equality; def probe := bnat_decide;", "binary_equality_dependencies");
  assert.ok(equality.complete, JSON.stringify(equality.gaps));
  assert.ok(!program.kernel.definitions.has("bnat_unary__bnat_to_unat"), "bitwise equality and setness must not load unary conversion");
  // The explicit conversion module supplies a positive control for the
  // forbidden magnitude conversion, even though hlevels uses unary levels.
  const conversions = await program.check("import bnat_unary; def probe := bnat_to_unat;", "binary_conversions");
  assert.ok(conversions.complete, JSON.stringify(conversions.gaps));
  assert.ok(program.kernel.definitions.has("bnat_unary__bnat_to_unat"), "explicit conversion import is observed");
});
