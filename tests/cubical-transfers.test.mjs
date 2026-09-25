import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { Translator } from "../lib/cubical/translate.mjs";
import { T } from "../lib/cubical/core.mjs";
import { numberEquivalence, transportNumberEquality, factorialThroughUnivalence } from "../lib/cubical/number-transport.mjs";

const module = await createCubical();

test("actual binary and radix factorial proofs transport through native Glue in all four directions", async t => {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  const checker = new NativeCubicalElaborator(kernel);
  const translator = new Translator({ normalize: false, checker });
  let env = new Map();
  for (const name of ["primes", "binary_naturals", "binary_arithmetic", "binary_induction", "binary_equivalence", "binary_arithmetic_correct"]) {
    const source = await readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");
    const result = translator.translate(source, env);
    env = result.env;
    for (const declaration of result.declarations) {
      // The production half-adjoint Equiv API has not yet been translated.
      // Build the cubical contractible-fiber equivalence below from its laws.
      if (["binary_nat_equiv", "nat_binary_equiv"].includes(declaration.name)) {
        assert.equal(declaration.status, "not-translated");
      } else assert.equal(declaration.status, "checked-native-cubical", `${declaration.name}: ${declaration.reason}`);
    }
  }
  const named = name => {
    const term = env.get(name);
    assert.equal(term?.tag, "DefRef", name);
    return term;
  };
  const binary = named("BinaryNat");
  const equivalence = numberEquivalence(checker, "cubical_binary_nat",
    binary, T.nat, named("binary_to_nat"), named("binary_of_nat"),
    named("binary_roundtrip"), named("binary_nat_roundtrip"),
  );
  const transported = transportNumberEquality(checker, "binary_factorial_through_glue", equivalence, named("binary_factorial_ten"));
  const checked = checker.syntax.check(transported);
  assert.ok(checked.arenaNodes < 2000000, JSON.stringify(checked));
  assert.ok(checked.arenaBytes < 128 * 1024 * 1024, JSON.stringify(checked));
  assert.equal(checked.normal, 0, "checking must not require normalizing the unary value");
  t.diagnostic(`Actual binary factorial through Glue: ${checked.arenaNodes} nodes, ${checked.arenaBytes} bytes`);
  let ten = T.zero;
  for (let n = 0; n < 10; n++) ten = T.succ(ten);
  const natFactorial = factorialThroughUnivalence(checker, "cubical_factorial_ten_via_univalence",
    equivalence, named("binary_factorial_ten"), T.app(named("binary_factorial_correct"), ten));
  checker.syntax.check(natFactorial, T.path("i", T.nat, T.app(named("factorial"), ten), named("nat_3628800")));
  env.set("cubical_factorial_ten_via_univalence", natFactorial);

  for (const name of ["equivalences", "radix_naturals", "radix_arithmetic", "radix_factorial", "radix_induction", "radix_digit_laws", "radix_decode", "radix_uniqueness", "radix_equivalence", "radix_arithmetic_correct", "radix_binary_equivalence", "radix_univalence_transfer"]) {
    const source = await readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");
    const result = translator.translate(source, env);
    env = result.env;
    for (const declaration of result.declarations) {
      if (name === "radix_univalence_transfer" && declaration.name.startsWith("factorial_ten_")) {
        assert.equal(declaration.status, "not-translated");
        continue;
      }
      // The elementary bijections, pair eliminations and half-adjoint laws also
      // check. These eight declarations depend on the still-untranslated
      // generic Equiv API.
      if (name === "equivalences" && ["equivalence_function", "equivalence_inverse_data",
        "equivalence_inverse", "equivalence_laws", "equivalence_left", "equivalence_right", "bijection_equiv", "equiv_bijection"].includes(declaration.name)) {
        assert.equal(declaration.status, "not-translated");
        continue;
      }
      if (["radix_nat_equiv", "nat_radix_equiv", "radix_binary_equiv", "binary_radix_equiv"].includes(declaration.name)) {
        assert.equal(declaration.status, "not-translated");
      } else assert.equal(declaration.status, "checked-native-cubical", `${declaration.name}: ${declaration.reason}`);
    }
  }
  for (const [base, extra, manual] of [[2, 0, "radix_factorial_ten_base_two"], [10, 8, "radix_factorial_ten_base_ten"]]) {
    let n = T.zero;
    for (let i = 0; i < extra; i++) n = T.succ(n);
    const specialized = name => T.app(named(name), n);
    const radix = specialized("RadixNat");
    for (const [direction, A, B, forward, inverse, eta, epsilon, proof] of [
      ["binary_radix", binary, radix, specialized("binary_to_radix"), specialized("radix_to_binary"), specialized("binary_radix_roundtrip"), specialized("radix_binary_roundtrip"), named("binary_factorial_ten")],
      ["radix_binary", radix, binary, specialized("radix_to_binary"), specialized("binary_to_radix"), specialized("radix_binary_roundtrip"), specialized("binary_radix_roundtrip"), named(manual)],
      ["radix_nat", radix, T.nat, specialized("radix_to_nat"), specialized("radix_of_nat"), specialized("radix_roundtrip"), specialized("radix_nat_roundtrip"), named(manual)],
    ]) {
      const label = `cubical_${direction}_base_${base}`;
      const equivalence = numberEquivalence(checker, label, A, B, forward, inverse, eta, epsilon);
      const result = transportNumberEquality(checker, `${label}_factorial`, equivalence, proof);
      const checked = checker.syntax.check(result);
      assert.equal(checked.normal, 0);
      assert.ok(checked.arenaNodes < 2500000, `${label}: ${checked.arenaNodes} nodes`);
      assert.ok(checked.arenaBytes < 128 * 1024 * 1024, `${label}: ${checked.arenaBytes} bytes`);
      t.diagnostic(`${label}: ${checked.arenaNodes} nodes, ${checked.arenaBytes} bytes`);
      const compatibilityName = direction === "binary_radix" ? "binary_to_radix_factorial"
        : direction === "radix_binary" ? "radix_to_binary_factorial" : "radix_factorial_correct";
      const final = factorialThroughUnivalence(checker, `${label}_original_factorial`, equivalence,
        proof, T.app(specialized(compatibilityName), ten));
      env.set(`${label}_original_factorial`, final);
      const original = checker.nf(checker.infer(proof).type);
      const target = direction === "radix_nat" ? T.app(named("factorial"), ten)
        : direction === "radix_binary" ? T.app(named("binary_factorial"), ten)
        : T.app(specialized("radix_factorial"), ten);
      checker.syntax.check(final, T.path("i", B, target, T.app(forward, original.right)));
    }
  }
  const concrete = translator.translate(await readFile(new URL(
    "../lib/cubical/factorial-transfer.cubist", import.meta.url), "utf8"), env);
  assert.equal(concrete.declarations.length, 7);
  for (const declaration of concrete.declarations)
    assert.equal(declaration.status, "checked-native-cubical", `${declaration.name}: ${declaration.reason}`);
  const dependencies = name => {
    const names = new Set(), kinds = new Set(), seen = new Set();
    const pending = [kernel.definitions.get(name)];
    while (pending.length) {
      const id = pending.pop();
      if (!id || seen.has(id)) continue;
      seen.add(id);
      const node = kernel.node(id);
      kinds.add(node.kind);
      pending.push(...node.children);
      if (node.kind === "DefRef") {
        const definition = kernel.definition(id);
        names.add(definition.name);
        pending.push(definition.value, definition.type);
      }
    }
    assert.ok(kinds.has("Glue") && kinds.has("Comp"), `${name} must use actual cubical transport`);
    return names;
  };
  for (const [suffix, manual] of [["two", "radix_factorial_ten_base_two"], ["ten", "radix_factorial_ten_base_ten"]]) {
    const fromBinary = dependencies(`factorial_ten_binary_to_base_${suffix}`);
    assert.ok(fromBinary.has("binary_factorial_ten"));
    assert.equal(fromBinary.has(manual), false, "target manual factorial must not prove its own transfer");
    for (const target of ["binary", "nat"]) {
      const fromRadix = dependencies(`factorial_ten_base_${suffix}_to_${target}`);
      assert.ok(fromRadix.has(manual));
      assert.equal(fromRadix.has("binary_factorial_ten"), false, "radix input must suffice independently");
    }
  }
  assert.ok(dependencies("factorial_ten_binary_to_nat").has("binary_factorial_ten"));
  const last = checker.syntax.check(named("binary_factorial_ten"));
  t.diagnostic(`All concrete endpoints: ${last.arenaNodes} nodes, ${last.arenaBytes} bytes`);
  assert.ok(last.arenaNodes < 2500000);
  assert.ok(last.arenaBytes < 128 * 1024 * 1024);
  const lengths = new Map();
  let maximum = 0;
  for (let id = 1; id <= last.arenaNodes; id++) {
    const node = kernel.node(id);
    if (node.kind === "Zero") lengths.set(id, 0);
    if (node.kind === "Succ" && lengths.has(node.children[0])) {
      const length = lengths.get(node.children[0]) + 1;
      lengths.set(id, length);
      maximum = Math.max(maximum, length);
    }
  }
  assert.equal(maximum, 10, "no transfer may materialize the large unary numeral");
});
