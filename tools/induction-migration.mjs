// Move only binders identified as induction hypotheses by a checked program.
// Token edits preserve comments and nested clause bodies byte for byte.
import { parse, tokenize } from "../web/cubist/parser.mjs";

export function migrateInductionHypotheses(source, hypothesisStarts) {
  const tokens = tokenize(source), edits = [], seen = new Set();
  const tokenIndex = new Map(tokens.map((token, index) => [token.start, index]));
  const visit = node => {
    if (!node || typeof node !== "object" || seen.has(node)) return;
    seen.add(node);
    if (node.kind === "clause" && !node.hypotheses && node.args?.length) {
      const split = node.args.findIndex(arg => hypothesisStarts.has(arg.start));
      if (split >= 0) {
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
      }
    }
    for (const child of Object.values(node)) if (child && typeof child === "object")
      if (Array.isArray(child)) child.forEach(visit); else visit(child);
  };
  visit(parse(source));
  let edited = source;
  for (const edit of edits.sort((a, b) => b.start - a.start))
    edited = edited.slice(0, edit.start) + edit.text + edited.slice(edit.end);
  parse(edited);
  return { source: edited, clauses: edits.length / 2 };
}

export function checkedHypothesisStarts(program, module) {
  return new Set([...program.declarationBindings]
    .filter(([binding]) => binding.startsWith(`${module}__`))
    .flatMap(([, bindings]) => bindings.filter(item => item.node.role === "induction hypothesis").map(item => item.node.start)));
}
