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

export function kernelStep(program, view, checked, side, path, rule, budget = 100000) {
  if (!Number.isSafeInteger(budget) || budget < 1 || budget > 10000000)
    throw new TypeError("Choose a work budget from 1 to 10000000 kernel ticks.");
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
