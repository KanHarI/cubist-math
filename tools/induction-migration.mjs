// Move only binders identified as induction hypotheses by a checked program.
// Token edits preserve comments and nested clause bodies byte for byte.
// Only declarations are migrated: a directive records no bindings of its own
// (its references go to the declaration after it, if any), and the migration
// verifier compares declarations. A directive's induction clauses that name
// fields are left as written and returned as `unchecked`, by their starts.
import { parse, tokenize } from "../web/cubist/parser.mjs";

// Every node under `root`, once.
const walk = (root, f, seen = new Set()) => {
  const visit = node => {
    if (!node || typeof node !== "object" || seen.has(node)) return;
    seen.add(node);
    if (!Array.isArray(node)) f(node);
    for (const child of Object.values(node)) visit(child);
  };
  visit(root);
};
const inductionClauses = node => node.kind === "induction" || node.kind === "matchStatement" && node.induction
  ? [...node.clauses ?? [], ...node.obligations ?? []] : [];

export function migrateInductionHypotheses(source, hypothesisStarts) {
  const tokens = tokenize(source), edits = [], unchecked = [];
  const tokenIndex = new Map(tokens.map((token, index) => [token.start, index]));
  const ast = parse(source);
  walk(ast.declarations, node => {
    if (node.kind !== "clause" || node.hypotheses || !node.args?.length) return;
    const split = node.args.findIndex(arg => hypothesisStarts.has(arg.start));
    if (split < 0) return;
    if (!split || node.args.slice(split).some(arg => !hypothesisStarts.has(arg.start)))
      throw Error("Checked induction hypotheses must follow all constructor fields.");
    const first = node.args[split], last = node.args.at(-1);
    const comma = tokens[tokenIndex.get(first.start) - 1];
    const close = tokens[tokenIndex.get(last.start) + 1];
    const end = node.coordinates.at(-1)?.end ?? close.end;
    // Move the suffix with its comments; leave the original closing
    // parenthesis and coordinates next to the constructor fields.
    const suffix = source.slice(comma.end, close.start);
    edits.push({ start: comma.start, end: close.start, text: "" },
      { start: end, end, text: ` with${/^\s/.test(suffix) ? "" : " "}${suffix}` });
  });
  walk(ast.directives ?? [], node => {
    for (const clause of inductionClauses(node)) if (!clause.hypotheses && clause.args?.length) unchecked.push(clause.start);
  });
  let edited = source;
  for (const edit of edits.sort((a, b) => b.start - a.start))
    edited = edited.slice(0, edit.start) + edit.text + edited.slice(edit.end);
  parse(edited);
  return { source: edited, clauses: edits.length / 2, unchecked: unchecked.sort((a, b) => a - b) };
}

export function checkedHypothesisStarts(program, module) {
  return new Set([...program.declarationBindings]
    .filter(([binding]) => binding.startsWith(`${module}__`))
    .flatMap(([, bindings]) => bindings.filter(item => item.node.role === "induction hypothesis").map(item => item.node.start)));
}
