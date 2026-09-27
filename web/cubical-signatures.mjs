// Admission of declared types (H1; docs/roadmaps/h1-signature-specification.md,
// section 6.1). A signature in normal form, as the `inductive` declaration
// lowers it (section 9), is derived one instruction at a time: its universe
// parameters and parameters as context entries, its former, the sort as an
// entry, and each constructor's type in a context holding the sort and the
// constructors before it. The kernel checks the normal form, positivity and
// universes; this module only issues the instructions and records the
// result under the declaration's name, for the syntax codec and inspection.
import { InstructionDriver } from "./cubical-instruction-driver.mjs";
import { CubicalSyntax } from "./cubical-syntax.mjs";

// The modifier the kernel takes: 0 untruncated, n + 2 for trunc(n), for
// n from -1 up to the kernel's bound, CC_TRUNCATION_MAX.
export const TRUNCATION_MAX = 14;
export function modifierCode(modifier) {
  if (modifier === undefined || modifier === "type") return 0;
  if (modifier === "prop") return 1;
  if (modifier === "set") return 2;
  const n = modifier?.trunc;
  if (Number.isInteger(n) && n >= -1 && n <= TRUNCATION_MAX) return n + 2;
  if (Number.isInteger(n) && n > TRUNCATION_MAX) throw new Error(`trunc(n) is supported up to n = ${TRUNCATION_MAX}.`);
  throw new Error("A sort is type, set, prop or trunc(n) for an integer n ≥ -1.");
}

// A signature in normal form, over cubical syntax (web/cubical-syntax.mjs):
//   name          the name the signature is registered under
//   sort          the variable naming the sort in constructor types; the
//                 name by default
//   levels        its universe parameters, [{ name, recorded }], in order; a
//                 recorded one is carried by instances, an erased one read
//                 from their parameters (section 1.1)
//   parameters    [{ name, type }], each type over the levels and the
//                 parameters before it
//   level         the sort's universe level, over the levels
//   modifier      "type" (the default), "set", "prop" or { trunc: n }
//   constructors  [{ name, type, display }], each type over the levels, the
//                 parameters, the sort's variable and the constructors before
//                 it; `display` is the name shown, the name by default
// Returns the registered record: { name, index, constructors, spec }, with
// the generated squash constructor last when the sort is truncated.
export function admitSignature(kernel, spec, { syntax = new CubicalSyntax(kernel),
                                              driver = kernel.instructionDriver ??= new InstructionDriver(kernel) } = {}) {
  if (kernel.signatures.has(spec.name)) throw new Error(`The declared type ${spec.name} already exists.`);
  const g = driver.graph, levels = spec.levels ?? [], parameters = spec.parameters ?? [];
  if (levels.length > 24 || parameters.length > 64) throw new Error("A signature has too many parameters.");
  // Level entries first, then each parameter bound at its derived type.
  let scope = new Map([["dims", 0n]]);
  const levelEntries = levels.map(({ name }) => {
    const entry = g.level(name);
    scope = new Map(scope).set(kernel.symbol(name), entry);
    return entry;
  });
  const parameterEntries = parameters.map(({ name, type }) => {
    const entry = driver.bind(kernel.symbol(name), driver.asType(driver.derive(syntax.encode(type), scope)));
    scope = new Map(scope).set(kernel.symbol(name), entry);
    return entry;
  });
  const universe = g.universe(syntax.encodeLevel(spec.level ?? 0));
  let former = universe;
  for (const entry of [...parameterEntries].reverse()) former = g.pi(entry, former);
  for (const entry of [...levelEntries].reverse()) former = g.levelPi(entry, former);
  const recorded = levels.reduce((mask, level, j) => mask | (level.recorded ? 1 << j : 0), 0);
  // The sort's entry names it; a variant name when another entry has it.
  const sortSymbol = kernel.symbol(spec.sort ?? spec.name);
  const sort = driver.bind(sortSymbol, universe);
  scope = new Map(scope).set(sortSymbol, sort);
  let signature = g.signatureBegin(former, modifierCode(spec.modifier), g.entry(sort).name, recorded);
  for (const { name, type } of spec.constructors ?? []) {
    // A constructor's type lives in the sort's universe; one derived lower
    // is lifted to it.
    const derived = driver.convertTo(driver.derive(syntax.encode(type), scope), universe);
    const entry = driver.bind(kernel.symbol(name), derived);
    signature = g.signatureConstructor(signature, derived, g.entry(entry).name);
    scope = new Map(scope).set(kernel.symbol(name), entry);
  }
  const index = g.signatureClose(signature);
  const constructors = (spec.constructors ?? []).map(c => c.display ?? c.name);
  if (kernel.signature(index).constructors.length > constructors.length) constructors.push("squash");
  const record = Object.freeze({ name: spec.name, index, constructors: Object.freeze(constructors), spec });
  kernel.signatures.set(spec.name, record);
  return record;
}
