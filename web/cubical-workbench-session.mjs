// The workbench's checked states live with their kernel in a worker. The UI
// receives immutable snapshots; raw syntax supplied by it is always rechecked.
import { CubicalProgram } from "./cubical-program.mjs";
import { foldedInspection } from "./cubical-inspection.mjs";
import { kernelAssembly, operandNames, opcodeName } from "./cubical-assembly.mjs";
import { kernelOccurrence, kernelReductionActions, kernelStep } from "./cubical-kernel-step.mjs";
import { judgementGraph } from "./cubical-graph-view.mjs";
import { checkReduction, reduceView } from "./cubical-reduction.mjs";
import { levelText } from "./cubical-levels.mjs";
import { safeTrace, traceSources, traceSnapshot, traceCounters, traceCost } from "./cubical-workbench-trace.mjs";

// A transfer's sources are text, which no reader placed: `fromLibrary` says
// which of them is the library's (module-resolution.mjs, libraryProvenance),
// so that a library axiom keeps its bare name, and `fromArchive` which is the
// archive's (archiveProvenance), so that an archive module replays with its
// legacy builtins; without them none is.
export class WorkbenchSession {
  constructor(module, { fromLibrary = null, fromArchive = null } = {}) {
    this.module = module; this.states = []; this.fromLibrary = fromLibrary; this.fromArchive = fromArchive;
  }
  dispose() { this.program?.dispose(); }
  state(id) {
    const state = this.states[id];
    if (!state) throw new Error("Unknown workbench state.");
    return state;
  }
  publish(view, checked, selected) {
    const state = { id: this.states.length, view, checked, selected };
    this.states.push(state);
    // Declaration printing is a non-enumerable, session-owned getter. Carry
    // its current value explicitly across structured clone, without exporting
    // session identities or changing the program's declaration records.
    // Only display/inspection fields are needed by the UI. Spreading a whole
    // declaration would also force its lazy source/type text.
    const symbols = Object.fromEntries(Object.entries(view.symbols).map(([key, info]) => {
      const { name, binding, kind, local, printing } = info;
      return [key, { name, binding, kind, local, printing }];
    }));
    return { ...state, view: { ...view, symbols } };
  }
  check(view, term = view.expression) {
    return this.program.checker.checkView(term, view.type,
      view.context.map(x => [x.name, x.type]), new Map(view.dimensions ?? []));
  }
  async load(payload, progress) {
    if (payload.format !== "thth-cubical" || payload.version !== 1)
      throw new Error("Unsupported cubical transfer format.");
    this.dispose(); this.states = [];
    const read = async name => {
      if (typeof payload.sources?.[name] !== "string") throw new Error(`Missing source module ${name}.`);
      return payload.sources[name];
    };
    // Each source is authenticated by the file its transfer says it was read
    // from, which the provenance reads again.
    const file = name => typeof payload.files?.[name] === "string" ? payload.files[name] : null;
    if (this.fromLibrary) read.fromLibrary = (name, text) => this.fromLibrary(name, text, file(name));
    if (this.fromArchive) read.fromArchive = (name, text) => this.fromArchive(name, text, file(name));
    this.program = new CubicalProgram(this.module, read);
    // A transfer replays its sources: one that does not check completely
    // is no transfer of what was checked, and is refused.
    const replayed = await this.program.check(payload.source, payload.main, progress);
    if (!replayed.complete)
      throw new Error(`The transfer did not replay completely: ${replayed.gaps[0]?.reason ?? "a declaration did not check"}`);
    // Supplied term/type claims are informational; replay source for evidence.
    let view = this.program.inspect(payload.binding);
    if (payload.side === "type") {
      const type = this.program.checker.checkView(view.type, null,
        view.context.map(x => [x.name, x.type]), new Map(view.dimensions ?? []));
      view = { ...view, expression: type.term, type: type.type,
        folded: view.folded ? { ...view.folded, expression: view.folded.type, type: type.type } : null };
    }
    const result = this.publish(view, this.check(view), view.name);
    // Diagnostic metadata must never turn a checked load into a failure.
    try { result.traceSession = await traceSources(this.program, payload); }
    catch (error) { result.traceSession = { main: payload.main, binding: payload.binding, sourceMetadataError: error.message }; }
    result.traceInitial = safeTrace(() => traceSnapshot(this.program, this.state(result.id), "expression", []));
    return result;
  }
  occurrence(id, side, path) {
    const { view, checked } = this.state(id), { kernel, checker } = this.program;
    const node = kernelOccurrence(kernel, checked, side, path);
    const label = handle => {
      if (!handle) return "unused";
      const n = kernel.node(handle);
      if (n.kind === "DefRef") {
        const { name } = kernel.definition(handle);
        return view.symbols[name]?.name ?? name;
      }
      if (n.kind === "Var") {
        const name = kernel.symbolName(n.payload);
        return view.symbols[name]?.name ?? name;
      }
      return opcodeName(n.kind);
    };
    // A partial-system cell has no standalone type, but its operands do. Keep
    // it inspectable without pretending that it is a term in the outer context.
    let text = label(node.handle);
    if (["LConst", "LSucc", "LMax"].includes(node.kind)) text = levelText(checker.syntax.decodeLevel(node.handle));
    else if (!["Tube", "GlueSystem", "List", "LBound"].includes(node.kind)) {
      const dimensions = new Map(view.dimensions ?? []), term = checker.syntax.decode(node.handle, dimensions);
      text = checker.displayGoal(new Map(view.context.map(x => [x.name, x.type])),
        dimensions, term, null, { width: 180, kernel: true, reduce: false }).goal;
    }
    return { ...node, text, label: label(node.handle),
      actions: kernelReductionActions(kernel, checked, side, path),
      operands: node.children.map((handle, index) => ({ handle, index,
        role: operandNames[node.kind]?.[index] ?? "unused", label: label(handle),
        kind: handle ? kernel.node(handle).kind : null })) };
  }
  async handle(command, args) {
    if (command === "inspect") {
      const view = this.program.inspect(args.binding);
      return this.publish(view, this.check(view), args.binding);
    }
    const { view, checked, selected } = this.state(args.state);
    if (command === "check") {
      const next = this.check(view, args.term);
      return this.publish({ ...view, expression: next.term, folded: null }, next, selected);
    }
    if (command === "occurrence") return this.occurrence(args.state, args.side, args.path);
    if (command === "subtree") {
      const node = kernelOccurrence(this.program.kernel, checked, args.side, args.path);
      // One level only. Expanding a branch requests its children separately;
      // shared handles are still displayed at their distinct operand paths.
      const listing = kernelAssembly(this.program, view, checked, {
        limit: 5, focus: [node.handle, ...node.children.filter(Boolean)],
      });
      const records = new Map(listing.nodes.map(record => [record.id, record]));
      return { root: records.get(node.handle), children: node.children.map(handle => records.get(handle) ?? null) };
    }
    if (command === "assembly") return kernelAssembly(this.program, view, checked, args.options);
    if (command === "graph") return judgementGraph(this.program, view, checked, {
      ...args.options, expanded: new Set(args.options?.expanded ?? []),
      driver: this.program.checker.driver, root: checked.judgement,
    });
    if (command === "step") {
      const before = safeTrace(() => traceSnapshot(this.program, this.state(args.state), args.side, args.path));
      const counters = safeTrace(() => traceCounters(this.program.kernel)), started = performance.now();
      let result;
      try { result = kernelStep(this.program, view, checked, args.side, args.path, args.rule, args.budget); }
      catch (error) {
        error.trace = { before, retainedState: args.state,
          cost: safeTrace(() => traceCost(this.program.kernel, counters, started)) };
        throw error;
      }
      const cost = safeTrace(() => traceCost(this.program.kernel, counters, started));
      const next = this.publish(result.view, result.checked, selected);
      return { ...next, change: result.change, trace: { before, cost,
        after: safeTrace(() => traceSnapshot(this.program, this.state(next.id), args.side, args.path)) } };
    }
    if (command === "reduce") {
      const { side, kind, path } = args;
      let result;
      if (kind === "normalize") {
        const dimensions = new Map(view.dimensions ?? []);
        const original = this.program.checker.checkView(view[side], null,
          view.context.map(x => [x.name, x.type]), dimensions);
        // Folded, as every normal form shown on request is; checkReduction
        // checks it by conversion, as it would the full one.
        const term = this.program.checker.syntax.decode(this.program.kernel.normalizeFolded(original.expression), dimensions);
        result = { ...checkReduction(this.program, view, side, term), change: { rule: "Normalized", name: side } };
      } else result = reduceView(this.program, view, side, kind, path);
      if (!result.change) return { change: null };
      const folded = { ...(view.folded ?? foldedInspection(view)), [side]: result.view[side] };
      if (side === "expression") delete folded.reference;
      return { ...this.publish({ ...result.view, folded }, result.checked, selected), change: result.change };
    }
    throw new Error("Unsupported workbench operation.");
  }
}
