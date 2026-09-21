// Workbench transformations propose syntax; only the C checker accepts it.
import { substituteTerm, substituteDimension } from "./dist/cubical-runtime/core.mjs";

export function reductionRule(term, kind) {
  if (kind === "delta" && term?.tag === "DefRef") return { rule: "δ", name: term.name };
  if (kind !== "beta") return null;
  if (term?.tag === "App" && term.fn.tag === "Lam") return { rule: "β", name: "function application" };
  if (term?.tag === "PApp" && term.path.tag === "PLam") return { rule: "β", name: "path application" };
  if (["Fst", "Snd"].includes(term?.tag) && term.pair.tag === "Pair") return { rule: "β", name: "pair projection" };
  return null;
}

export function termAtPath(term, path) {
  for (const key of path) {
    if (!term || typeof term !== "object" || !Object.hasOwn(term, key)) throw new Error("Invalid reduction location.");
    term = term[key];
  }
  return term;
}

// A path identifies an occurrence, not an object: shared subtrees can appear
// several times, and selecting one must not change its siblings.
export function reductionAt(term, kind, path, definition) {
  const target = termAtPath(term, path);
  if (!reductionRule(target, kind)) throw new Error("This location does not support the selected reduction.");
  const reduced = reductionStep(target, kind, definition);
  const replace = (value, depth) => {
    if (depth === path.length) return reduced.term;
    const copy = Array.isArray(value) ? [...value] : { ...value };
    copy[path[depth]] = replace(value[path[depth]], depth + 1);
    return copy;
  };
  return { ...reduced, term: replace(term, 0) };
}

export function reductionStep(term, kind, definition) {
  if (!["beta", "delta"].includes(kind)) throw new Error("Unknown reduction operation.");
  let change = null;
  const visited = new WeakSet();
  const visit = value => {
    if (!value || typeof value !== "object" || change || visited.has(value)) return value;
    visited.add(value);
    if (kind === "delta" && value.tag === "DefRef") {
      const body = definition(value.name);
      change = { rule: "δ", name: value.name }; return body;
    }
    if (kind === "beta") {
      if (value.tag === "App" && value.fn.tag === "Lam") {
        change = { rule: "β", name: "function application" };
        return substituteTerm(value.fn.body, value.fn.name, value.arg);
      }
      if (value.tag === "PApp" && value.path.tag === "PLam") {
        change = { rule: "β", name: "path application" };
        return substituteDimension(value.path.body, value.path.dim, value.arg);
      }
      if (["Fst", "Snd"].includes(value.tag) && value.pair.tag === "Pair") {
        change = { rule: "β", name: "pair projection" };
        return value.pair[value.tag === "Fst" ? "first" : "second"];
      }
    }
    // Prefer visible bodies/components before their type annotations.
    const identityWrapper = value.tag === "App" && value.fn.tag === "Lam"
      && value.fn.body.tag === "Var" && value.fn.body.name === value.fn.name;
    const preferred = { Lam: ["body", "domain"], Pair: ["first", "second", "as"],
      PLam: ["body", "family"], App: identityWrapper ? ["arg", "fn"] : ["fn", "arg"] }[value.tag] ?? [];
    for (const key of [...preferred, ...Object.keys(value).filter(key => !preferred.includes(key))]) {
      const child = visit(value[key]);
      if (change) {
        const result = Array.isArray(value) ? [...value] : { ...value };
        result[key] = child; return result;
      }
    }
    return value;
  };
  const result = visit(term);
  return { term: result, change };
}

// A constant path between the old and proposed terms can type-check only if
// their endpoints are definitionally equal. Merely sharing a type is not enough.
export function checkReduction(program, view, side, term) {
  if (!["expression", "type"].includes(side)) throw new Error("Unknown reduction target.");
  const { syntax } = program.checker, context = view.context.map(x => [x.name, x.type]);
  const dimensions = new Map(view.dimensions ?? []);
  return program.kernel.withUnfoldingHints(view.unfoldingHints ?? [], () => {
    const original = syntax.check(view[side], null, context, dimensions);
    const used = new Set(dimensions.keys()), seen = new WeakSet();
    const collect = value => {
      if (!value || typeof value !== "object" || seen.has(value)) return;
      seen.add(value); if (value.dim) used.add(value.dim);
      Object.values(value).forEach(collect);
    };
    collect(view[side]); collect(term); collect(original.type);
    let dim = "workbenchReduction"; while (used.has(dim)) dim += "_";
    syntax.check({ tag: "PLam", dim, family: original.type, body: view[side] },
      { tag: "Path", dim, family: original.type, left: view[side], right: term }, context, dimensions);
    const candidate = { ...view, [side]: term };
    const checked = syntax.check(candidate.expression, candidate.type, context, dimensions);
    // C may report the inferred type using its earlier alias. The explicitly
    // supplied candidate type was checked too; retain the user's reduced form.
    return { view: { ...candidate, expression: checked.term }, checked };
  });
}

export function reduceView(program, view, side, kind, path = null) {
  if (!["expression", "type"].includes(side)) throw new Error("Unknown reduction target.");
  const definition = name => {
    const reference = program.kernel.definitions.get(name);
    if (!reference) throw new Error(`No checked definition for ${name}.`);
    // Read the kernel's closed body, including explicit assumption parameters.
    return program.checker.syntax.decode(program.kernel.definition(reference).value, new Map(view.dimensions ?? []));
  };
  const proposal = path === null ? reductionStep(view[side], kind, definition)
    : reductionAt(view[side], kind, path, definition);
  if (!proposal.change) return { view, change: null };
  return { ...checkReduction(program, view, side, proposal.term), change: proposal.change };
}
