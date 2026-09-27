// The elaboration of each declaration of a checked module, step by step: its
// source, its type, each proof statement with the goal it faced and the term
// it built, the finished term, and the kernel's check as a forward derivation.
// The reference's Elaboration panels show it.
import { cubicalText } from "./cubical-notation.mjs";
import { judgementGraph } from "./cubical-graph-view.mjs";

// The rule (opcode) of THTH's forward engine that derives each kind of node.
export const ththRules = {
  U: "UIntro", Var: "Vble", Pi: "PiForm", Lam: "PiIntro", App: "PiElim", Sigma: "SigmaForm", Pair: "SigmaIntro",
  Fst: "SigmaElim", Snd: "SigmaElim", Nat: "NatForm", Zero: "NatIntroZ", Succ: "NatIntroS", NatRec: "NatElim",
  Unit: "UnitForm", Point: "UnitIntro", UnitRec: "UnitElim", Void: "VoidForm", Abort: "VoidElim",
  Sum: "SumForm", Inl: "SumIntroL", Inr: "SumIntroR", SumRec: "SumElim", W: "WForm", Sup: "WIntro", WRec: "WElim",
  Path: "PathForm", PLam: "PathIntro", PApp: "PathElim", DefRef: "DefLookup", Comp: "Comp", HComp: "HComp",
  Trans: "Transp", Glue: "GlueForm", GlueTerm: "GlueIntro", Unglue: "GlueElim",
};


// The derivation as the instruction kernel checks it (web/cubical-graph-view.mjs),
// in the panel's form: each step one rule on earlier steps, under a comment
// with the judgement it derives. Context entries are CtxExt steps, placed just
// before their first use; a highlighted step names its rule and position.
const stepNames = { beta: "Beta", delta: "Delta", iota: "Iota", path: "PathBeta", normalize: "Normalize", whnf: "Whnf", face: "Face" };
export function instructionDerivation(program, view, { limit = 400 } = {}) {
  const graph = judgementGraph(program, view);
  const steps = [], numbers = new Map(), placed = new Map();
  const add = step => { steps.push({ number: steps.length + 1, scaffold: null, ...step }); return steps.length; };
  const place = entry => {
    if (placed.has(entry.id)) return placed.get(entry.id);
    const number = add({ rule: entry.dimension ? "DimExt" : "CtxExt", entry: entry.id,
      premises: entry.sourceNumber ? [numbers.get(entry.sourceNumber)] : [], comment: `{${entry.fragment.join(", ")}}` });
    placed.set(entry.id, number);
    return number;
  };
  for (const row of graph.rows) {
    for (const entry of row.context) if (entry) place(entry);
    const bound = row.entry ? [place(row.entry)] : [];
    const rule = row.rule === "step" ? stepNames[row.highlight.rule] : row.label;
    const note = row.highlight ? `at the ${row.highlight.side}${row.highlight.position.length ? ` [${row.highlight.position.join(", ")}]` : ""}: ${row.highlight.text}` : null;
    numbers.set(row.number, add({ rule, premises: [...bound, ...row.premises.map(premise => numbers.get(premise))],
      comment: row.statement, ...(note ? { note } : {}), judgement: row }));
  }
  // A function applied at once is the elaborator's: exact's ascription, or a
  // type family applied to its argument.
  for (const step of steps) {
    if (step.rule !== "PiElim") continue;
    const fn = steps[step.premises[0] - 1];
    if (fn?.rule !== "PiIntro") continue;
    const label = /^\{[^}]*\} ⊢ λ \(ascription\b/.test(fn.comment)
      ? "added by the elaborator: exact checks its value at the goal"
      : "added by the elaborator: a family applied to its argument";
    for (const marked of [step, fn]) marked.scaffold ??= label;
    const context = steps[fn.premises[0] - 1];
    if (context?.rule === "CtxExt") context.bound ??= label;
  }
  // A context, and its variables, are the elaborator's when only its steps use them.
  for (const step of steps) if (step.bound) {
    const users = steps.filter(other => other.premises.includes(step.number));
    const variables = users.filter(user => user.rule === "Vble");
    if (users.every(user => user.scaffold || user.rule === "Vble") &&
        variables.every(variable => steps.filter(other => other.premises.includes(variable.number)).every(user => user.scaffold))) {
      step.scaffold = step.bound;
      for (const variable of variables) variable.scaffold = step.bound;
    }
    delete step.bound;
  }
  for (const step of steps) { delete step.judgement; delete step.entry; }
  return { steps: steps.slice(0, limit), truncated: steps.length > limit || graph.truncated, source: "instructions" };
}

// The instruction kernel's derivation; if it cannot be shown, why not.
function derivation(program, view) {
  try { return instructionDerivation(program, view); }
  catch (error) { return { steps: [], truncated: false, source: "instructions", reason: error.message }; }
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
        derivation: derivation(program, view) };
    } catch (error) {
      return { ...result, steps, reason: error.message };
    }
  });
}
