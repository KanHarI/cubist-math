import { parse } from "./parser.mjs";
import { diagnosticCode } from "../diagnostics.mjs";

// Warnings for bindings that are never used and can simply be removed:
//   induction v as k   when neither the return type nor the successor clause uses k;
//   match v as z       when the return type does not mention z;
//   forall/exists x    when the body does not mention x (write A -> B, A and B);
//   let, obtain        when nothing after them in their block uses their names.
// A binding the syntax requires is never reported: a parameter, a fun binder,
// a clause's argument or coordinate, an induction hypothesis, intro.
//
// A use is an identifier of the same name inside the binding's scope, so a
// shadowing binder can hide an unused binding but never invents one. hlevel
// and generated squash clauses search the context for evidence without
// naming it, so let and obtain are not reported before an hlevel or a match
// in the same block.
export function lint(source, ast = parse(source)) {
  // Every identifier's positions, skipping comments and numerals (0b110).
  const positions = new Map();
  for (const match of source.matchAll(/\/\/[^\n]*|[0-9][A-Za-z0-9_]*|[A-Za-z_][A-Za-z0-9_]*/g)) {
    if (!/^[A-Za-z_]/.test(match[0])) continue;
    if (!positions.has(match[0])) positions.set(match[0], []);
    positions.get(match[0]).push(match.index);
  }
  const used = (name, start, end) => (positions.get(name) ?? []).some(at => at >= start && at < end);
  const text = node => source.slice(node.start, node.end);
  const warnings = [];
  const warn = (at, message) => warnings.push({ start: at.start, end: at.end, message });

  // A block's statements: each let and obtain is in scope for the rest of the
  // block, nested blocks included.
  const block = statements => {
    const last = statements.at(-1);
    if (!last || !Number.isInteger(last.end)) return;
    statements.forEach(statement => {
      const names = statement.kind === "let" ? [statement.target]
        : statement.kind === "obtain" ? patternNames(statement.target) : null;
      if (!names || statement === last) return;
      const start = statement.end, end = last.end;
      if (used("hlevel", start, end) || used("match", start, end)) return;
      const name = token => token.text ?? token.name;
      if (names.some(token => used(name(token), start, end))) return;
      if (statement.kind === "obtain")
        warn(statement.target, `None of ${names.map(name).join(", ")} is used after this obtain: remove it.`);
      else warn(names[0], `${name(names[0])} is never used after this let: remove it.`);
    });
  };
  const visit = node => {
    if (Array.isArray(node)) {
      if (node.some(item => ["let", "obtain"].includes(item?.kind))) block(node);
      node.forEach(visit);
      return;
    }
    if (!node || typeof node !== "object") return;
    if (node.kind === "induction" && node.index) {
      const k = node.index.text;
      if (!used(k, node.type.start, node.type.end) && !used(k, node.step.start, node.step.end))
        warn(node.index, `${k} is unused: the return type does not mention it and the successor clause does not use it. `
          + `Omit as ${k}: induction ${text(node.value)} return ….`);
    }
    if (node.kind === "match" && node.motiveName && node.type && !used(node.motiveName.text, node.type.start, node.type.end))
      warn(node.motiveName, `${node.motiveName.text} is unused: the return type does not mention it. `
        + `Omit as ${node.motiveName.text}: match ${text(node.value)} return ….`);
    // A quantifier's variable the body does not mention; a universe variable
    // has no unnamed form.
    const quantifier = node.binderKind ?? node.kind;
    if ((quantifier === "forall" || quantifier === "exists") && !node.bound && node.body) {
      const names = node.names ?? [node.name], domain = text(node.domain);
      const plain = quantifier === "forall" ? `${domain} -> …` : `${domain} and …`;
      for (const token of names) if (!used(token.text, node.body.start, node.body.end))
        warn(token, names.length === 1
          ? `${token.text} is unused in the body: write ${plain} instead of ${quantifier} ${token.text} : ${domain}. ….`
          : `${token.text} is unused in the body: take it out of the group and write ${plain} for it.`);
    }
    for (const value of Object.values(node)) if (value && typeof value === "object") visit(value);
  };
  visit(ast.declarations);
  // Each warning with its declaration and its line and column.
  const lineStarts = [0];
  for (let i = 0; i < source.length; i++) if (source[i] === "\n") lineStarts.push(i + 1);
  return warnings.sort((a, b) => a.start - b.start).map(warning => {
    let line = lineStarts.findLastIndex(start => start <= warning.start);
    const declaration = ast.declarations.find(d => d.start <= warning.start && warning.start < d.end);
    return { ...warning, code: diagnosticCode(warning.message), line: line + 1, column: warning.start - lineStarts[line] + 1,
      ...(declaration?.name?.text ? { declaration: declaration.name.text } : {}) };
  });
}

// The names an obtain pattern binds: (a, (b, c)) binds a, b and c.
function patternNames(pattern) {
  if (!pattern) return [];
  if (pattern.kind === "name") return [pattern];
  if (pattern.kind === "pair") return [...patternNames(pattern.left), ...patternNames(pattern.right)];
  return [];
}
