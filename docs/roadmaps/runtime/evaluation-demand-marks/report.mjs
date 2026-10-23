// The acceptance measurements of the evaluation demand marks (DM5 of the note
// beside this directory). Each case runs in a fresh program, through the REPL
// as the CLI runs it (web/repl-session.mjs), with the probe's fixed query
// budget. For each it records the entry's first result and its SHA-256, the
// query ticks and queries the entry alone spent, and, where the entry
// normalized a term, how many times, and for the last normalization, the
// whole value's under `!!_` after any its elaboration asked for, its ticks
// alone, the normal form's distinct nodes and its digest (normalDigest
// below).
// Usage: node report.mjs [--root=CHECKOUT] [budget] [case ...]. --root
// measures another checkout, as main, with the spelling each case had there
// before the marks (`expecting _` for `expecting !!_`); a case with no such
// spelling is skipped. Named cases run alone. Results are JSON lines.
import { createHash } from "node:crypto";
import { pathToFileURL } from "node:url";
import { sources } from "./probe-sources.mjs";

const option = process.argv.find(arg => arg.startsWith("--root="));
const root = option ? pathToFileURL(`${option.slice("--root=".length).replace(/\/$/, "")}/`) : new URL("../../../../", import.meta.url);
const args = process.argv.slice(2).filter(arg => !arg.startsWith("--"));
const budget = BigInt(args.find(arg => /^\d+$/.test(arg)) ?? "100000000"), named = args.filter(arg => !/^\d+$/.test(arg));
const { default: createCubical } = await import(new URL("web/dist/cubical.mjs", root));
const { CubicalProgram } = await import(new URL("web/cubical-program.mjs", root));
const { ReplSession } = await import(new URL("web/repl-session.mjs", root));
const { sourceReader } = await import(new URL("tools/module-sources.mjs", root));
const { assertFreshBuild, sourceHash } = await import(new URL("tools/build-stamp.mjs", root));
assertFreshBuild();

const unat = "import unat;\nuse unat;\n", euclid = "import euclid;\nuse unat;\n";
const rationals = "import rationals;\nuse unat;\n", integers = "import integers;\nuse unat;\n";
// Each acceptance case: its setup, its entry, and the entry main had for it.
const cases = [
  { id: "small-inverse-value", setup: sources.rational, entry: "evaluate small_inverse;", main: "evaluate small_inverse;" },
  { id: "small-inverse-normal", setup: sources.rational, entry: "evaluate small_inverse expecting !!_;", main: "evaluate small_inverse expecting _;" },
  { id: "euclid-3-pattern", setup: euclid, entry: "evaluate euclid(3) expecting (7, _);", main: "evaluate euclid(3) expecting (7, _);" },
  { id: "euclid-4-head", setup: euclid, entry: "evaluate !euclid(4);" },
  { id: "euclid-4-pattern", setup: euclid, entry: "evaluate euclid(4) expecting (5, _);", main: "evaluate euclid(4) expecting (5, _);" },
  { id: "bare-hole", setup: euclid, entry: "evaluate euclid(3) expecting _;", main: "evaluate euclid(3) expecting _;" },
  { id: "eta-successor-head", setup: unat, entry: "print(evaluate(!(fun (n : UNat) => succ(n))));" },
  // The constructs whose full normal forms the corpus test leaves out.
  ...[["rational-literal-normal", rationals, "rationals.(2/3)"], ["decimal-literal-normal", rationals, "rationals.(0.5)"],
    ["theory-parent-normal", integers, "integers.additive_"]].map(([id, setup, term]) =>
    ({ id, setup, entry: `evaluate ${term} expecting !!_;`, main: `evaluate ${term} expecting _;` })),
];

const sha256 = text => createHash("sha256").update(text).digest("hex");
// A kernel term's digest up to the names of bound variables, as
// tools/evaluation-baseline.mjs's normalDigest gives of its decoding, taken
// over the kernel's shared nodes: a normal form shares most of its nodes,
// and as a tree can be too large to walk. Each node is digested once for
// each way its free variables and dimensions are bound around it, from its
// kind, its payload as named (a constructor's index, a definition's or
// signature's name), its formulas, and the parts the decoding reads.
function normalDigest(program, handle) {
  const { kernel, checker: { syntax } } = program, node = id => kernel.node(id);
  const binders = new Set(["Lam", "Pi", "Sigma", "LLam", "LPi"]);
  const chain = (id, next) => { const cells = []; for (let cell = id; cell; cell = node(cell).children[next]) cells.push(node(cell)); return cells; };
  // The parts the decoding reads, each with what it binds, and the formulas.
  const structure = new Map();
  const shape = id => {
    if (structure.has(id)) return structure.get(id);
    const { kind, payload, children: [c0, c1, c2, c3] } = node(id), part = (child, bound = {}) => ({ id: child, ...bound });
    const dim = { dim: payload };
    let parts, faces = [];
    if (binders.has(kind)) parts = [part(c0), part(c1, { name: kernel.symbolName(payload) })];
    else if (kind === "Path") parts = [part(c0, dim), part(c1), part(c2)];
    else if (kind === "PLam") parts = [part(c0, dim), part(c1, dim)];
    else if (kind === "PApp") { parts = [part(c0)]; faces = [payload]; }
    else if (kind === "Trans") { parts = [part(c0, dim), part(c2)]; faces = [node(c1).payload]; }
    else if (kind === "Comp" || kind === "HComp") {
      const tubes = chain(c1, 1);
      parts = [part(c0, kind === "Comp" ? dim : {}), ...tubes.map(tube => part(tube.children[0], dim)), part(c2)];
      faces = tubes.map(tube => tube.payload);
    } else if (kind === "Glue") {
      const system = chain(c1, 2);
      parts = [part(c0), ...system.flatMap(cell => [part(cell.children[0]), part(cell.children[1])])];
      faces = system.map(cell => cell.payload);
    } else if (kind === "GlueTerm") {
      const tubes = chain(c2, 1);
      parts = [part(c0), part(c1), ...tubes.map(tube => part(tube.children[0]))];
      faces = tubes.map(tube => tube.payload);
    } else if (kind === "DefRef" || kind === "Var" || kind === "LBound") parts = [];
    else parts = [c0, c1, c2, c3].filter(Boolean).map(child => part(child));
    // A binder's name or dimension, and a formula's payload, are read above.
    const label = kind === "Var" ? null : binders.has(kind) || ["Path", "PLam", "Trans", "Comp", "HComp", "PApp", "Glue", "GlueTerm"].includes(kind) ? kind
      : kind === "DefRef" ? `${kind} ${kernel.definition(id).name}`
      : kind === "Sort" || kind === "Elim" ? `${kind} ${syntax.signatureRecord(payload).name}` : `${kind} ${payload}`;
    const result = { kind, label, parts, faces: faces.map(face => kernel.inspectFormula(face).clauses), name: kind === "Var" ? kernel.symbolName(payload) : null };
    structure.set(id, result);
    return result;
  };
  const dimsOf = clauses => clauses.flatMap(([positive, negative]) =>
    Array.from({ length: 64 }, (_, at) => (BigInt(positive) | BigInt(negative)) >> BigInt(at) & 1n ? at : -1).filter(at => at >= 0));
  // Each node's free variables and dimensions, by a walk over the shared nodes.
  const free = new Map(), pending = [handle];
  while (pending.length) {
    const id = pending.at(-1);
    if (free.has(id)) { pending.pop(); continue; }
    const { parts, faces, name } = shape(id), missing = parts.filter(part => part.id && !free.has(part.id)).map(part => part.id);
    if (missing.length) { pending.push(...missing); continue; }
    pending.pop();
    const names = new Set(name === null ? [] : [name]), dims = new Set(faces.flatMap(dimsOf));
    for (const part of parts) {
      if (!part.id) continue;
      const inner = free.get(part.id);
      for (const each of inner.names) if (each !== part.name) names.add(each);
      for (const each of inner.dims) if (part.dim === undefined || each !== part.dim) dims.add(each);
    }
    free.set(id, { names: [...names].sort(), dims: [...dims].sort((a, b) => a - b) });
  }
  // The binders around a node, innermost first, and each one's depth.
  const term = (scope, name) => { for (let at = scope.binders; at; at = at.next) if (at.name === name) return `#${scope.names - at.depth - 1}`; return `free ${JSON.stringify(name)}`; };
  const dimension = (scope, index) => { for (let at = scope.binders; at; at = at.next) if (at.dim === index) return `#${scope.dims - at.depth - 1}`; return `free ${index}`; };
  const bind = (scope, part) => part.name !== undefined
    ? { binders: { name: part.name, depth: scope.names, next: scope.binders }, names: scope.names + 1, dims: scope.dims }
    : part.dim !== undefined ? { binders: { dim: part.dim, depth: scope.dims, next: scope.binders }, names: scope.names, dims: scope.dims + 1 } : scope;
  const formula = (scope, clauses) => `formula ${clauses.map(([positive, negative]) => [...dimsOf([[positive, 0n]]).map(at => `${dimension(scope, at)}:1`),
    ...dimsOf([[0n, negative]]).map(at => `${dimension(scope, at)}:0`)].sort().join("&")).sort().join("|")}`;
  const digests = new Map(), stack = [{ id: handle, scope: { binders: null, names: 0, dims: 0 } }];
  let result = null;
  const deliver = digest => { if (stack.length) stack.at(-1).done.push(digest); else result = digest; };
  while (stack.length) {
    const frame = stack.at(-1);
    if (frame.key === undefined) {
      const { names, dims } = free.get(frame.id);
      frame.key = `${frame.id}|${names.map(name => term(frame.scope, name)).join(",")}|${dims.map(at => dimension(frame.scope, at)).join(",")}`;
      if (digests.has(frame.key)) { stack.pop(); deliver(digests.get(frame.key)); continue; }
      frame.shape = shape(frame.id);
      frame.done = [];
    }
    const { parts, faces, label, name } = frame.shape;
    if (frame.done.length < parts.length) {
      const part = parts[frame.done.length];
      if (part.id) stack.push({ id: part.id, scope: bind(frame.scope, part) }); else frame.done.push("-");
      continue;
    }
    const digest = sha256([name === null ? label : `Var ${term(frame.scope, name)}`, ...faces.map(clauses => formula(frame.scope, clauses)), ...frame.done].join(" "));
    digests.set(frame.key, digest);
    stack.pop();
    deliver(digest);
  }
  return { normalNodes: free.size, normalDigest: result };
}
const module = await createCubical();
const kernelSources = sourceHash("kernel");
for (const item of cases) {
  const entry = option ? item.main : item.entry;
  if (!entry || named.length && !named.includes(item.id)) continue;
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  try {
    const session = new ReplSession(program), kernel = program.kernel;
    const setup = await session.run(item.setup);
    const refused = setup.find(result => result.kind === "error");
    if (refused) throw new Error(`${item.id}: the setup is refused: ${refused.text}`);
    kernel.stepBudget = budget;
    kernel.maxQuerySteps = budget;
    kernel.setStepBudget(budget);
    // The entry's whole-term normalizations, each digested while its handle
    // holds: a committed or abandoned entry moves its nodes.
    let normalizations = 0, normal = null;
    const { normalize } = kernel, work = () => kernel.work();
    kernel.normalize = function (handle) {
      const before = work(), result = normalize.call(this, handle), after = work();
      normalizations++;
      normal = { normalTicks: Number(after.querySteps - before.querySteps), ...normalDigest(program, result) };
      return result;
    };
    const before = work();
    const [result] = await session.run(entry);
    const after = work();
    const record = { case: item.id, entry, queryBudget: String(budget), kernelSources,
      outcome: result.kind, text: result.text.length > 160 ? `${result.text.slice(0, 159)}…` : result.text,
      length: result.text.length, sha256: sha256(result.text),
      queryTicks: Number(after.querySteps - before.querySteps), queries: Number(after.queries - before.queries),
      normalizations, ...normal };
    console.log(JSON.stringify(record));
  } finally { program.dispose(); }
}
