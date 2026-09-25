// Source link sites: the source span of a syntax node that links to the
// checked term the node elaborates to. The elaborator records its checked
// terms at these sites, and an unelaborated template lists the same sites.
// Keyword spans come from the parser.

// Tactics whose keyword links to the checked proof they build.
const tactics = new Map([
  ["calc", ["calc", "calculation witness"]],
  ["rw", ["rw", "rewrite witness"]],
  ["simpOnly", ["simp", "simplification witness"]],
  ["simpaOnly", ["simpa", "simplification witness"]],
]);

export function tacticSite(statement) {
  const tactic = tactics.get(statement.kind);
  if (!tactic) return null;
  const [name, role] = tactic;
  return { name, start: statement.keyword.start, end: statement.keyword.end, role };
}

// Each calc step's `by` keyword links to the step's checked path.
export function calcStepSite(step, index) {
  return { name: `calc step ${index + 1}`, start: step.by.start, end: step.by.end,
    role: "calculation step", expansionIndex: index + 1 };
}

// A logical operator or a binder keyword links to the checked expression.
export function expressionSite(node) {
  if (node.kind === "binary" && ["=", "->", "and", "or"].includes(node.operator))
    return { name: node.operator, start: node.operatorStart, end: node.operatorEnd };
  if (node.keyword && ["lambda", "forall", "exists", "binderGroup"].includes(node.kind)) {
    const binder = node.binderKind ?? node.kind;
    return { name: binder === "lambda" ? "fun" : binder, start: node.keyword.start, end: node.keyword.end };
  }
  return null;
}
