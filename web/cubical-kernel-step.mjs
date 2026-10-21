// A workbench operation is one native Step on a checked judgement. Paths are
// operand indices from its term/type root, never a search for a shared handle.
export function kernelOccurrence(kernel, checked, side, path) {
  if (!["expression", "type"].includes(side)) throw new TypeError("Select the expression or its type.");
  let handle = side === "expression" ? checked.expression : checked.typeHandle;
  for (const child of path) {
    if (!Number.isInteger(child) || child < 0 || child > 3)
      throw new TypeError("A native operand index must be 0, 1, 2 or 3.");
    handle = kernel.node(handle).children[child];
    if (!handle) throw new TypeError("The selected occurrence is an unused operand.");
  }
  return { handle, ...kernel.node(handle) };
}

// Suggestions inspect native shapes only: never normalize or attempt a Step
// while navigating. Rules with further premises are explicitly labelled Try.
// The instruction kernel remains the authority when an action is applied.
export function kernelReductionActions(kernel, checked, side, path) {
  const node = kernelOccurrence(kernel, checked, side, path);
  const kind = handle => handle ? kernel.node(handle).kind : null;
  function targeted(n) {
    const a = kind(n.children[0]);
    const actions = [];
    const add = (rule, label) => actions.push({ rule, label });
    if ((n.kind === "App" && a === "Lam") || (n.kind === "LApp" && a === "LLam"))
      add("beta", "β reduce application");
    if (n.kind === "DefRef") add("delta", "δ unfold selected definition");
    if (["Fst", "Snd"].includes(n.kind) && a === "Pair") add("iota", "ι reduce projection");
    if ((n.kind === "UnitRec" && kind(n.children[2]) === "Point")
      || (n.kind === "SumRec" && ["Inl", "Inr"].includes(kind(n.children[3]))))
      add("iota", "ι compute eliminator");
    if (n.kind === "App" && a === "Elim") add("iota", "Try ι eliminator");
    if (n.kind === "PApp") add("path", a === "PLam" ? "Path reduce application" : "Try Path endpoint");
    if (["Comp", "HComp", "Trans"].includes(n.kind) && n.children[1])
      add("face", "Try Face boundary");
    if (n.kind === "GlueTerm") add("glue", "Try Glue η");
    if (["Comp", "HComp"].includes(n.kind) && n.children[1]) add("split", "Try Split tubes");
    return actions;
  }
  const actions = targeted(node).map(action => ({ ...action, path: [...path] }));
  if (path.length) {
    const parentPath = path.slice(0, -1), slot = path.at(-1);
    const parent = kernelOccurrence(kernel, checked, side, parentPath);
    // An unfolded function/constructor or a partial system can expose a rule
    // at its immediate parent. Never silently target an arbitrary ancestor.
    const operand = { App: 0, LApp: 0, Fst: 0, Snd: 0, UnitRec: 2,
      SumRec: 3, PApp: 0, Comp: 1, HComp: 1, Trans: 1, GlueTerm: 1 };
    if (operand[parent.kind] === slot) for (const action of targeted(parent)) {
      actions.push({ ...action, path: parentPath,
        label: action.rule === "beta" ? "β reduce containing application" : `${action.label} at parent` });
    }
  }
  if (!["Tube", "GlueSystem", "List", "LBound", "LConst", "LSucc", "LMax"].includes(node.kind)) {
    actions.push({ rule: "whnf", label: "WHNF selected subtree", path: [...path] },
      { rule: "normalize", label: "Normalize selected subtree", path: [...path] });
  }
  return actions;
}

export function kernelStep(program, view, checked, side, path, rule, budget = 100000) {
  if (!Number.isSafeInteger(budget) || budget < 1 || budget > 10000000)
    throw new TypeError("The work budget must be an integer from 1 to 10000000 kernel ticks.");
  const before = kernelOccurrence(program.kernel, checked, side, path).handle;
  const graph = program.checker.driver.graph;
  // within restores the ordinary budget even when Step refuses. No retry with
  // a larger budget, no JS reduction, and no fresh proof search for the result.
  const judgement = graph.within(budget, () =>
    graph.step(checked.judgement, side === "expression" ? "term" : "type", path, rule));
  const result = program.checker.viewOfJudgement(judgement, new Map(view.dimensions ?? []), checked.renamings, 1);
  const after = kernelOccurrence(program.kernel, result, side, path).handle;
  return { checked: result, view: { ...view, expression: result.term, type: result.type, folded: null },
    change: { before, after, judgement, side, path: [...path], rule } };
}
