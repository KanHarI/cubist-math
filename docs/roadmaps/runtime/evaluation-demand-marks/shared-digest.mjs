// The acceptance report's digest of a normal form (report.mjs).
import { createHash } from "node:crypto";

const sha256 = text => createHash("sha256").update(text).digest("hex");
// Sorted by content, as the baseline sorts a formula's clauses and literals.
const sorted = values => values.map(value => [JSON.stringify(value), value]).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0).map(([, value]) => value);

// A kernel term's digest up to the names of bound variables, equal for two
// terms exactly when tools/evaluation-baseline.mjs's normalDigest of their
// decodings is (tests/evaluation-demand-marks.test.mjs), but taken over the
// kernel's shared nodes: a normal form shares most of its nodes, and as a
// tree can be too large to walk. Each node is digested once for each way
// its free variables and dimensions are bound around it, from what its
// decoding (web/cubical-syntax.mjs) reads: its kind, its fields as named (a
// definition's or signature's name, a constructor's index and name, a
// level's numbers), its formulas, and its parts, each with what it binds.
// A node's digest is the JSON of these, so no field runs into another.
export function sharedDigest(program, handle) {
  const { kernel, checker: { syntax } } = program, node = id => kernel.node(id);
  const chain = (id, next) => { const cells = []; for (let cell = id; cell; cell = node(cell).children[next]) cells.push(node(cell)); return cells; };
  const structure = new Map();
  const shape = id => {
    if (structure.has(id)) return structure.get(id);
    const { kind, payload, children: [c0, c1, c2, c3] } = node(id), part = (child, bound = {}) => ({ id: child, ...bound });
    const dim = { dim: payload }, items = list => chain(list, 1).map(cell => part(cell.children[0]));
    let parts = [], faces = [], fields = [], name = null;
    switch (kind) {
      case "Var": name = kernel.symbolName(payload); break;
      case "DefRef": fields = [kernel.definition(id).name]; break;
      case "U": case "Fst": case "Snd": parts = [part(c0)]; break;
      case "LPi": case "LLam": parts = [part(c1, { name: kernel.symbolName(payload) })]; break;
      case "LBound": case "LConst": fields = [payload]; break;
      case "LSucc": fields = [payload]; parts = [part(c0)]; break;
      case "LApp": case "LMax": case "App": case "Abort": case "Sum": case "Inl": case "Inr": case "Unglue": parts = [part(c0), part(c1)]; break;
      case "Unit": case "Point": case "Void": break;
      case "Pi": case "Lam": case "Sigma": parts = [part(c0), part(c1, { name: kernel.symbolName(payload) })]; break;
      case "Pair": case "UnitRec": parts = [part(c0), part(c1), part(c2)]; break;
      case "SumRec": parts = [part(c0), part(c1), part(c2), part(c3)]; break;
      case "Path": parts = [part(c0, dim), part(c1), part(c2)]; break;
      case "PLam": parts = [part(c0, dim), part(c1, dim)]; break;
      case "PApp": parts = [part(c0)]; faces = [payload]; break;
      case "Trans": parts = [part(c0, dim), part(c2)]; faces = [node(c1).payload]; break;
      case "Comp": case "HComp": {
        const tubes = chain(c1, 1);
        parts = [part(c0, kind === "Comp" ? dim : {}), ...tubes.map(tube => part(tube.children[0], dim)), part(c2)];
        faces = tubes.map(tube => tube.payload);
        break;
      }
      case "Glue": {
        const system = chain(c1, 2);
        parts = [part(c0), ...system.flatMap(cell => [part(cell.children[0]), part(cell.children[1])])];
        faces = system.map(cell => cell.payload);
        break;
      }
      case "GlueTerm": {
        const tubes = chain(c2, 1);
        parts = [part(c0), part(c1), ...tubes.map(tube => part(tube.children[0]))];
        faces = tubes.map(tube => tube.payload);
        break;
      }
      case "Sort": {
        const parameters = items(c0);
        fields = [syntax.signatureRecord(payload).name, parameters.length];
        parts = [...parameters, ...items(c1)];
        break;
      }
      case "Con": {
        const sort = node(c0);
        fields = [payload, sort.kind === "Sort" ? syntax.signatureRecord(sort.payload).constructors[payload] ?? null : null];
        parts = [part(c0)];
        break;
      }
      case "Elim": fields = [syntax.signatureRecord(payload).name]; parts = [part(c0), ...items(c1)]; break;
      default: throw new Error(`Unsupported cubical node: ${kind}`);
    }
    const result = { kind, fields, parts, faces: faces.map(face => kernel.inspectFormula(face).clauses), name };
    structure.set(id, result);
    return result;
  };
  const dimsOf = mask => Array.from({ length: 64 }, (_, at) => BigInt(mask) >> BigInt(at) & 1n ? at : -1).filter(at => at >= 0);
  const formulaDims = clauses => clauses.flatMap(([positive, negative]) => [...dimsOf(positive), ...dimsOf(negative)]);
  // Each node's free variables and dimensions, by a walk over the shared nodes.
  const free = new Map(), pending = [handle];
  while (pending.length) {
    const id = pending.at(-1);
    if (free.has(id)) { pending.pop(); continue; }
    const { parts, faces, name } = shape(id), missing = parts.filter(part => part.id && !free.has(part.id)).map(part => part.id);
    if (missing.length) { pending.push(...missing); continue; }
    pending.pop();
    const names = new Set(name === null ? [] : [name]), dims = new Set(faces.flatMap(formulaDims));
    for (const part of parts) {
      if (!part.id) continue;
      const inner = free.get(part.id);
      for (const each of inner.names) if (each !== part.name) names.add(each);
      for (const each of inner.dims) if (part.dim === undefined || each !== part.dim) dims.add(each);
    }
    free.set(id, { names: [...names].sort(), dims: [...dims].sort((a, b) => a - b) });
  }
  // The binders around a node, innermost first, and each one's depth: a
  // variable or dimension is its binder's distance, or free by its name.
  const term = (scope, name) => {
    for (let at = scope.binders; at; at = at.next) if (at.name === name) return ["bound", scope.names - at.depth - 1];
    return ["free", name];
  };
  const dimension = (scope, index) => {
    for (let at = scope.binders; at; at = at.next) if (at.dim === index) return ["bound", scope.dims - at.depth - 1];
    return ["free", index];
  };
  const bind = (scope, part) => part.name !== undefined
    ? { binders: { name: part.name, depth: scope.names, next: scope.binders }, names: scope.names + 1, dims: scope.dims }
    : part.dim !== undefined ? { binders: { dim: part.dim, depth: scope.dims, next: scope.binders }, names: scope.names, dims: scope.dims + 1 } : scope;
  // A formula's clauses, each its literals: no clause is false, and an empty one true.
  const formula = (scope, clauses) => sorted(clauses.map(([positive, negative]) =>
    sorted([...dimsOf(positive).map(at => [dimension(scope, at), 1]), ...dimsOf(negative).map(at => [dimension(scope, at), 0])])));
  const digests = new Map(), stack = [{ id: handle, scope: { binders: null, names: 0, dims: 0 } }];
  let result = null;
  const deliver = digest => { if (stack.length) stack.at(-1).done.push(digest); else result = digest; };
  while (stack.length) {
    const frame = stack.at(-1);
    if (frame.key === undefined) {
      const { names, dims } = free.get(frame.id);
      frame.key = JSON.stringify([frame.id, names.map(name => term(frame.scope, name)), dims.map(at => dimension(frame.scope, at))]);
      if (digests.has(frame.key)) { stack.pop(); deliver(digests.get(frame.key)); continue; }
      frame.shape = shape(frame.id);
      frame.done = [];
    }
    const { kind, fields, parts, faces, name } = frame.shape;
    if (frame.done.length < parts.length) {
      const part = parts[frame.done.length];
      if (part.id) stack.push({ id: part.id, scope: bind(frame.scope, part) }); else frame.done.push(null);
      continue;
    }
    const digest = sha256(JSON.stringify([kind, name === null ? fields : term(frame.scope, name), faces.map(clauses => formula(frame.scope, clauses)), frame.done]));
    digests.set(frame.key, digest);
    stack.pop();
    deliver(digest);
  }
  return { normalNodes: free.size, normalDigest: result };
}
