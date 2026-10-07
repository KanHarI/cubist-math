import "./fresh-build.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {naturalSort,numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { Translator } from "../web/translator/translate.mjs";
import { T } from "../web/translator/core.mjs";
import { numberEquivalence, transportNumberEquality, factorialThroughUnivalence } from "./translator/number-transport.mjs";

const module = await createCubical();

test("actual binary and radix factorial proofs transport through native Glue in all four directions", async t => {
  const program=new CubicalProgram(module,sourceReader(),{collectReferences:false});
  t.after(()=>program.dispose());
  const result=await program.check("import binary_arithmetic_correct; import radix_univalence_transfer; def retained : Unit := tt;", "transfers");
  assert.equal(result.complete,true,JSON.stringify(result.gaps));
  const kernel=program.kernel, checker=program.checker;
  const translator=new Translator({normalize:false,checker});
  let env=program.modules.get("transfers");
  const named = name => {
    const term = env.get(name);
    assert.equal(term?.tag, "DefRef", name);
    return term;
  };
  // BinaryNat and RadixNat(extra) are declared types: their signatures' sorts.
  const declared = (name, ...parameters) => {
    const value = env.get(name);
    assert.equal(value?.tag, "Inductive", name);
    return T.sort(value.binding, parameters);
  };
  const binary = declared("BinaryNat");
  const equivalence = numberEquivalence(checker, "cubical_binary_nat",
    binary, naturalSort, named("binary_to_nat"), named("binary_of_nat"),
    named("binary_roundtrip"), named("binary_nat_roundtrip"),
  );
  const transported = transportNumberEquality(checker, "binary_factorial_through_glue", equivalence, named("binary_factorial_ten"));
  const checked = checker.checkView(transported);
  assert.ok(checked.arenaNodes < 2000000, JSON.stringify(checked));
  assert.ok(checked.arenaBytes < 128 * 1024 * 1024, JSON.stringify(checked));
  assert.equal(checked.normal, undefined, "checking must not require normalizing the unary value");
  t.diagnostic(`Actual binary factorial through Glue: ${checked.arenaNodes} nodes, ${checked.arenaBytes} bytes`);
  const ten = numeral(10);
  const natFactorial = factorialThroughUnivalence(checker, "cubical_factorial_ten_via_univalence",
    equivalence, named("binary_factorial_ten"), T.app(named("binary_factorial_correct"), ten));
  checker.checkView(natFactorial, T.path("i", naturalSort, T.app(named("factorial"), ten), named("nat_3628800")));
  env.set("cubical_factorial_ten_via_univalence", natFactorial);

  for (const [base, extra, manual] of [[2, 0, "radix_factorial_ten_base_two"], [10, 8, "radix_factorial_ten_base_ten"]]) {
    const n = numeral(extra);
    const specialized = name => T.app(named(name), n);
    const radix = declared("RadixNat", n);
    for (const [direction, A, B, forward, inverse, eta, epsilon, proof] of [
      ["binary_radix", binary, radix, specialized("binary_to_radix"), specialized("radix_to_binary"), specialized("binary_radix_roundtrip"), specialized("radix_binary_roundtrip"), named("binary_factorial_ten")],
      ["radix_binary", radix, binary, specialized("radix_to_binary"), specialized("binary_to_radix"), specialized("radix_binary_roundtrip"), specialized("binary_radix_roundtrip"), named(manual)],
      ["radix_nat", radix, naturalSort, specialized("radix_to_nat"), specialized("radix_of_nat"), specialized("radix_roundtrip"), specialized("radix_nat_roundtrip"), named(manual)],
    ]) {
      const label = `cubical_${direction}_base_${base}`;
      const equivalence = numberEquivalence(checker, label, A, B, forward, inverse, eta, epsilon);
      const result = transportNumberEquality(checker, `${label}_factorial`, equivalence, proof);
      const checked = checker.checkView(result);
      assert.equal(checked.normal, undefined);
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
      checker.checkView(final, T.path("i", B, target, T.app(forward, original.right)));
    }
  }
  const concrete = translator.translate(await readFile(new URL(
    "./fixtures/factorial-transfer.cubist", import.meta.url), "utf8"), env);
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
        names.add(definition.name.split("__").at(-1));
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
  const last = checker.checkView(named("binary_factorial_ten"));
  t.diagnostic(`All concrete endpoints: ${last.arenaNodes} nodes, ${last.arenaBytes} bytes`);
  assert.ok(last.arenaNodes < 2500000);
  assert.ok(last.arenaBytes < 128 * 1024 * 1024);
  const lengths = new Map();
  let maximum = 0;
  for (let id = 1; id <= last.arenaNodes; id++) {
    const node = kernel.node(id);
    if (node.kind === "Con" && node.payload === 0 && kernel.node(node.children[0]).payload === kernel.signatures.get("nat__Nat").index) lengths.set(id, 0);
    if (node.kind === "App" && kernel.node(node.children[0]).kind === "Con" && kernel.node(node.children[0]).payload === 1 && lengths.has(node.children[1])) {
      const length = lengths.get(node.children[1]) + 1;
      lengths.set(id, length);
      maximum = Math.max(maximum, length);
    }
  }
  // The largest is a binary literal's character count, 24 for
  // 0b1101110101111100000000, which its parser counts in Nat (L2.10j).
  assert.equal(maximum, 24, "no transfer may materialize the large unary numeral");
});
