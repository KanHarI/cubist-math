import { boundedSyntaxJson } from "./cubical-json.mjs";
import { kernelOccurrence } from "./cubical-kernel-step.mjs";

const clipped = (text, limit) => text.length > limit
  ? { text: text.slice(0, limit), omittedCharacters: text.length - limit }
  : { text, omittedCharacters: 0 };
export const traceError = error => ({
  message: String(error.message ?? error).slice(0, 2000),
  kind: error.kind ?? null, fatal: !!error.fatal,
});
export function traceAttempt(command, args) {
  if (command === "load") return { command, main: args.main, binding: args.binding, side: args.side };
  if (command === "inspect") return { command, binding: args.binding };
  if (command === "step") return { command, state: args.state, side: args.side,
    path: [...args.path], rule: args.rule, budget: args.budget };
  if (command === "reduce") return { command, state: args.state, side: args.side,
    path: args.path, rule: args.kind, pathFormat: "decoded syntax keys" };
  if (command === "check") {
    const syntax = boundedSyntaxJson(args.term, { maxNodes: 1000, maxCharacters: 16000, maxDepth: 64 });
    return { command, state: args.state, editedSyntax: syntax === null
      ? { omitted: "Edited syntax exceeds the trace limit." } : JSON.parse(syntax) };
  }
  return null; // Navigation and rendering never add kernel operations.
}

// Kept on the page, so Copy still works during a reduction or after a worker
// crash. This is a bounded event log, not the undo stack: Back is an event too.
export class WorkbenchTrace {
  constructor({ maxEntries = 100, maxCharacters = 250000 } = {}) {
    this.startedAt = new Date().toISOString();
    this.started = performance.now();
    this.maxEntries = maxEntries; this.maxCharacters = maxCharacters;
    this.entries = []; this.sequence = 0; this.dropped = 0;
    this.metadata = {};
  }
  begin(attempt) {
    if (!attempt) return null;
    const entry = { sequence: ++this.sequence, atMs: Math.round(performance.now() - this.started),
      ...attempt, status: "running" };
    this.entries.push(entry); this.trim(); return entry;
  }
  finish(entry, result) {
    if (!entry) return;
    Object.assign(entry, result);
    this.trim();
  }
  trim() {
    while (this.entries.length > 1 && (this.entries.length > this.maxEntries
      || JSON.stringify(this.entries).length > this.maxCharacters)) {
      this.entries.shift(); this.dropped++;
    }
  }
  text(current) {
    return JSON.stringify({
      format: "cubist-workbench-trace", version: 1, startedAt: this.startedAt,
      notes: [
        "Manual operations since this page load; not the internal reduction steps of WHNF/Normalize.",
        "Native paths are operand indices from the expression/type root. Handles and judgements are session-local.",
        "AST excerpts are bounded, do not unfold definitions, and omit formula clauses; source SHA-256 identifies the checked imports.",
        "Back selects an earlier state without deleting attempts. Source text/edited syntax may be truncated as marked.",
      ],
      ...this.metadata, current, droppedEntries: this.dropped, entries: this.entries,
    }, null, 2);
  }
}

export async function traceSources(program, payload) {
  const sources = [];
  for (const [name, source] of Object.entries(program.sources).sort(([a], [b]) => a.localeCompare(b))) {
    const digest = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(source));
    sources.push({ name, characters: source.length,
      sha256: [...new Uint8Array(digest)].map(byte => byte.toString(16).padStart(2, "0")).join("") });
  }
  return { main: payload.main, binding: payload.binding, side: payload.side,
    mainSource: clipped(payload.source, 16000), sources, kernelAbi: program.kernel.module._cb_abi_version() };
}

// Read only a small part of the native DAG. In particular, do not decode a
// large term, normalize it, or serialize a shared graph as an expanded tree.
export function traceSnapshot(program, state, side, path, limit = 16) {
  const kernel = program.kernel, selected = kernelOccurrence(kernel, state.checked, side, path);
  const pending = [selected.handle], seen = new Set(), nodes = [];
  for (let i = 0; i < pending.length && nodes.length < limit; i++) {
    const handle = pending[i];
    if (!handle || seen.has(handle)) continue;
    seen.add(handle);
    const n = kernel.node(handle);
    const node = { handle, kind: n.kind, payload: n.payload, operands: [...n.children] };
    if (n.kind === "DefRef") node.definition = kernel.definition(handle);
    if (["Var", "Lam", "Pi", "Sigma"].includes(n.kind)) node.name = kernel.symbolName(n.payload);
    nodes.push(node); pending.push(...n.children.filter(Boolean));
  }
  return { state: state.id, binding: state.selected, judgement: state.checked.judgement,
    expression: state.checked.expression, type: state.checked.typeHandle,
    side, path: [...path], selected: selected.handle, nodes,
    omittedDiscoveredNodes: new Set(pending.filter(handle => !seen.has(handle))).size };
}
export function safeTrace(read) {
  try { return read(); }
  catch (error) { return { unavailable: String(error.message ?? error).slice(0, 1000) }; }
}
export function traceCounters(kernel) {
  return { work: kernel.work(), arena: kernel.arena() };
}
export function traceCost(kernel, before, started) {
  const after = traceCounters(kernel);
  return { elapsedMs: Math.round((performance.now() - started) * 1000) / 1000,
    work: Object.fromEntries(Object.entries(after.work).map(([key, value]) => [key, value - before.work[key]])),
    allocatedNodes: after.arena.nodes - before.arena.nodes,
    arenaBytesDelta: after.arena.bytes - before.arena.bytes };
}
