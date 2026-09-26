// The elaboration of each declaration of a checked module, step by step: its
// source, its type, each proof statement with the goal it faced and the term
// it built, the finished term, and the kernel's check as a forward derivation.
// The reference's Elaboration panels show it.
import { cubicalText } from "./cubical-notation.mjs";
import { betaReduce } from "./cubical-elaborator.mjs";

// The rule (opcode) of THTH's forward engine that derives each kind of node.
export const ththRules = {
  U: "UIntro", Var: "Vble", Pi: "PiForm", Lam: "PiIntro", App: "PiElim", Sigma: "SigmaForm", Pair: "SigmaIntro",
  Fst: "SigmaElim", Snd: "SigmaElim", Nat: "NatForm", Zero: "NatIntroZ", Succ: "NatIntroS", NatRec: "NatElim",
  Unit: "UnitForm", Point: "UnitIntro", UnitRec: "UnitElim", Void: "VoidForm", Abort: "VoidElim",
  Sum: "SumForm", Inl: "SumIntroL", Inr: "SumIntroR", SumRec: "SumElim", W: "WForm", Sup: "WIntro", WRec: "WElim",
  Path: "PathForm", PLam: "PathIntro", PApp: "PathElim", DefRef: "DefLookup", Comp: "Comp", HComp: "HComp",
  Trans: "Transp", Glue: "GlueForm", GlueTerm: "GlueIntro", Unglue: "GlueElim",
};

// The kernel's check of a declaration as a forward derivation, in the style of
// THTH's proofs: each step applies one rule (opcode) to earlier steps, and
// derives the judgement or context in its comment. The steps come from the
// kernel's trace (cc_trace_kind), in the order the kernel completed them;
// check reuse is off, so every node is derived. As in THTH, a judgement keeps
// only the context it depends on, and a judgement derived twice is numbered
// once. Steps that come from the elaborator's scaffolding rather than the
// source, such as exact's ascription, are labelled.
export function kernelDerivation(program, view, { limit = 400 } = {}) {
  const kernel = program.kernel, checker = program.checker, dimensions = new Map(view.dimensions ?? []);
  const context = view.context.map(entry => [entry.name, entry.type]);
  const saved = kernel.optimizations ?? { shareSyntax: true, reuseChecks: true, compactPaths: true };
  kernel.setOptimizations({ ...saved, reuseChecks: false });
  let traced;
  try { traced = kernel.traced(() => checker.syntax.check(view.expression, view.type, context, dimensions)); }
  finally { kernel.setOptimizations(saved); }
  const decode = handle => checker.syntax.decode(handle, dimensions);
  // Terms are shown as the kernel derived them, redexes included; types are
  // shown beta-reduced.
  const type = handle => betaReduce(decode(handle));
  const free = (term, out = new Set(), bound = new Set()) => {
    if (!term || typeof term !== "object") return out;
    if (term.tag === "Var" && !bound.has(term.name)) out.add(term.name);
    const inner = ["Pi", "Lam", "Sigma", "W"].includes(term.tag) ? new Set(bound).add(term.name) : bound;
    for (const [key, value] of Object.entries(term)) free(value, out, key === "body" ? inner : bound);
    return out;
  };
  // Terms in mathematical notation over the part of the context they depend
  // on, written {x : A, …}; one renaming keeps the names in agreement.
  const math = (entries, first, second = null) => {
    const needed = new Set([...free(first), ...free(second)]);
    for (let i = entries.length - 1; i >= 0; i--)
      if (needed.has(entries[i].symbol)) for (const name of free(entries[i].type)) needed.add(name);
    const kept = entries.filter(entry => needed.has(entry.symbol));
    const shown = checker.displayGoal(new Map(kept.map(entry => [entry.symbol, entry.type])), first, second, 240, cubicalText, false);
    return { scope: `{${shown.locals.map(local => `${local.name} : ${local.type}`).join(", ")}}`, first: shown.goal, second: shown.built };
  };
  const steps = [], numbers = new Map(), frames = [{ premises: [], start: [], context: [] }];
  const derive = (rule, premises, comment) => {
    if (numbers.has(comment)) return numbers.get(comment);
    steps.push({ number: steps.length + 1, rule, premises, comment, scaffold: null });
    numbers.set(comment, steps.length);
    return steps.length;
  };
  for (const event of traced.events) {
    if (steps.length >= limit) break;
    const frame = frames.at(-1);
    if (event.kind === "infer") {
      const node = kernel.node(event.a);
      frames.push({ node, premises: [], start: [...frame.context], context: [...frame.context],
        symbol: node.kind === "Var" ? kernel.symbolName(node.payload) : null });
    } else if (event.kind === "extend") {
      const entry = { symbol: kernel.symbolName(event.a), type: type(event.b) };
      // The context it creates: the new name and what its type depends on.
      entry.step = derive("CtxExt", frame.premises.slice(-1), math([...frame.context, entry], { tag: "Var", name: entry.symbol }).scope);
      frame.premises.push(entry.step);
      frame.context.push(entry);
    } else if (event.kind === "convert" && event.a !== event.b) {
      // A conversion between types that read the same is not shown.
      const shown = math(frame.context, type(event.b), type(event.a));
      if (shown.first !== shown.second)
        frame.premises.push(derive("Conv", frame.premises.slice(-1), `${shown.scope} ⊢ ${shown.second} ≡ ${shown.first}`));
    } else if (event.kind === "inferred") {
      const done = frames.pop();
      if (!event.c) break;
      if (done.symbol) {
        const entry = [...done.start].reverse().find(item => item.symbol === done.symbol);
        if (entry?.step) done.premises.unshift(entry.step);
      }
      const shown = math(done.start, type(event.c), decode(event.b));
      const number = derive(ththRules[done.node.kind] ?? done.node.kind, done.premises, `${shown.scope} ⊢ ${shown.second} : ${shown.first}`);
      const step = steps[number - 1];
      // A function applied at once is the elaborator's: exact's ascription,
      // or a type family applied to its argument.
      if (step.rule === "PiElim" && steps[step.premises[0] - 1]?.rule === "PiIntro") {
        const lambda = steps[step.premises[0] - 1];
        const label = /^\{[^}]*\} ⊢ λ \(ascription\b/.test(lambda.comment)
          ? "added by the elaborator: exact checks its value at the goal"
          : "added by the elaborator: a family applied to its argument";
        for (const marked of [step, lambda]) marked.scaffold ??= label;
        for (const premise of lambda.premises) if (steps[premise - 1].rule === "CtxExt") steps[premise - 1].bound ??= label;
      }
      frames.at(-1).premises.push(number);
    }
  }
  // A context is the elaborator's when only its steps use it.
  for (const step of steps) if (step.bound) {
    const users = steps.filter(other => other.premises.includes(step.number) && other.rule !== "Vble");
    if (users.every(user => user.scaffold)) step.scaffold = step.bound;
    delete step.bound;
  }
  // Variables of the elaborator's contexts are the elaborator's too.
  for (const step of steps) if (step.rule === "Vble" && steps[step.premises[0] - 1]?.scaffold) step.scaffold = steps[step.premises[0] - 1].scaffold;
  return { steps, truncated: steps.length >= limit || traced.dropped > 0 };
}

// Every declaration of `module`, in source order.
export function elaboration(program, module) {
  const source = program.sources[module] ?? "";
  const declarations = Object.values(program.symbols)
    .filter(info => info.binding?.startsWith(`${module}__`) && Number.isInteger(info.start))
    .sort((a, b) => a.start - b.start);
  return declarations.map(info => {
    const result = { name: info.name, source: source.slice(info.start, info.end), verified: !!info.verified };
    if (!info.verified) return { ...result, reason: info.reason };
    const steps = program.steps(module, info.name).map(step => ({ ...step, text: source.slice(step.start, step.end) }));
    try {
      const view = program.inspect(info.binding), checker = program.checker, dimensions = new Map(view.dimensions ?? []);
      return { ...result, steps,
        type: checker.displayText(view.type, 600), term: checker.displayText(view.expression, 600),
        derivation: kernelDerivation(program, view) };
    } catch (error) {
      return { ...result, steps, reason: error.message };
    }
  });
}
