// The acceptance report's digest of a normal form (report.mjs).
import { createHash } from "node:crypto";

const sha256 = text => createHash("sha256").update(text).digest("hex");

// A kernel term's digest up to the names of bound variables, equal for two
// terms exactly when tools/evaluation-baseline.mjs's normalDigest of their
// decodings is (tests/evaluation-demand-marks.test.mjs), but taken over the
// kernel's shared nodes: a normal form shares most of its nodes, and as a
// tree can be too large to walk. Each node is digested once for each way
// its free variables and dimensions are bound around it, from its
// kind, its payload as named (a constructor's index, a definition's or
// signature's name), its formulas, and the parts the decoding reads.
export function sharedDigest(program, handle) {
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
  // Each clause in parentheses: no clause is false, and an empty one true.
  const formula = (scope, clauses) => `formula ${clauses.map(([positive, negative]) => `(${[...dimsOf([[positive, 0n]]).map(at => `${dimension(scope, at)}:1`),
    ...dimsOf([[0n, negative]]).map(at => `${dimension(scope, at)}:0`)].sort().join("&")})`).sort().join("|")}`;
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
