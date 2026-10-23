import { parse, scan, builtinNames, primitiveNames, isUniverseConstant } from "./parser.mjs";

// Warnings for evaluation demand marks that ask for nothing more (below), and
// for bindings that are never used and can simply be removed:
//   induction v as k   when neither the return type nor the successor clause uses k;
//   induction v as z   on a declared type, when the return type does not mention z;
//   match v as z       when the return type does not mention z;
//   forall/exists x    when the body does not mention x (write A -> B, A and B);
//   let, obtain        when nothing after them in their block uses their names.
// A binding the syntax requires is never reported: a parameter, a fun binder,
// a clause's argument or coordinate, an induction hypothesis, intro.
//
// A use is an identifier of the same name inside the binding's scope, so a
// shadowing binder can hide an unused binding but never invents one; a named
// argument's parameter name is not a use. hlevel
// and generated squash clauses search the context for evidence without
// naming it, so let and obtain are not reported before an hlevel or a match
// in the same block.
export function lint(source, ast = parse(source)) {
  // Every identifier's positions, skipping comments and numerals (0b110).
  const positions = new Map();
  for (const { text, start } of scan(source)) {
    if (!/^[A-Za-z_]/.test(text)) continue;
    if (!positions.has(text)) positions.set(text, []);
    positions.get(text).push(start);
  }
  // A named argument's name, f(x := e), is f's parameter, not a use of x.
  const parameterNames = new Set();
  const named = node => {
    if (!node || typeof node !== "object") return;
    if (node.kind === "namedArgument") parameterNames.add(node.name.start);
    for (const value of Object.values(node)) if (value && typeof value === "object") named(value);
  };
  named(ast.declarations);
  // Operation and law telescopes are public generated interfaces. Their
  // named arguments and generated capabilities survive only if these
  // binders stay, even when an arrow would have the same function type.
  const publicTelescopes = new WeakSet();
  for (const declaration of ast.declarations) if (declaration.kind === "theory")
    for (const field of declaration.fields) if (["operation", "law"].includes(field.kind)) {
      let type = field.type;
      while ((type?.binderKind ?? type?.kind) === "forall") {
        publicTelescopes.add(type);
        type = type.body;
      }
    }
  const used = (name, start, end) => (positions.get(name) ?? []).some(at => at >= start && at < end && !parameterNames.has(at));
  const text = node => source.slice(node.start, node.end);
  const warnings = [];
  const warn = (at, code, message) => warnings.push({ start: at.start, end: at.end, code, message });

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
        warn(statement.target, "W701", `None of ${names.map(name).join(", ")} is used after this obtain: remove it.`);
      else warn(names[0], "W702", `${name(names[0])} is never used after this let: remove it.`);
    });
  };
  const visit = node => {
    if (Array.isArray(node)) {
      if (node.some(item => ["let", "obtain"].includes(item?.kind))) block(node);
      node.forEach(visit);
      return;
    }
    if (!node || typeof node !== "object") return;
    if (node.kind === "induction" && node.motiveName && node.type && !used(node.motiveName.text, node.type.start, node.type.end))
      warn(node.motiveName, "W707", `${node.motiveName.text} is unused: the return type does not mention it. `
        + `Omit as ${node.motiveName.text}: induction ${text(node.value)} return ….`);
    if (node.kind === "induction" && node.index) {
      const k = node.index.text;
      if (!used(k, node.type.start, node.type.end) && !used(k, node.step.start, node.step.end))
        warn(node.index, "W703", `${k} is unused: the return type does not mention it and the successor clause does not use it. `
          + `Omit as ${k}: induction ${text(node.value)} return ….`);
    }
    if (node.kind === "match" && node.motiveName && node.type && !used(node.motiveName.text, node.type.start, node.type.end))
      warn(node.motiveName, "W704", `${node.motiveName.text} is unused: the return type does not mention it. `
        + `Omit as ${node.motiveName.text}: match ${text(node.value)} return ….`);
    // A quantifier's variable the body does not mention; a universe variable
    // has no unnamed form.
    const quantifier = node.binderKind ?? node.kind;
    if ((quantifier === "forall" || quantifier === "exists") && !node.bound && node.body && !publicTelescopes.has(node)) {
      const names = node.names ?? [node.name], domain = text(node.domain);
      const plain = quantifier === "forall" ? `${domain} -> …` : `${domain} and …`;
      for (const token of names) if (!used(token.text, node.body.start, node.body.end))
        warn(token, names.length === 1 ? "W705" : "W706", names.length === 1
          ? `${token.text} is unused in the body: write ${plain} instead of ${quantifier} ${token.text} : ${domain}. ….`
          : `${token.text} is unused in the body: take it out of the group and write ${plain} for it.`);
    }
    for (const value of Object.values(node)) if (value && typeof value === "object") visit(value);
  };
  visit(ast.declarations);
  // Demand marks that ask for nothing more than their part already computes
  // (docs/roadmaps/runtime/evaluation-demand-marks.md): ! before a part that
  // computes its weak head itself, a pair, an injection, a constructor or an
  // expression; !! before an expression, which is compared by its normal
  // form; and a mark under !! or !!! that asks for no more than it, whose
  // part is normalized (docs/roadmaps/runtime/folded-normal-forms.md). A !!!
  // under !! asks for more, which the checker refuses (E486).
  // What a part computes by itself, read from its syntax alone: a hole
  // nothing, typed(T, p) what p does, and anything else at least the part's
  // weak head. Only an expression surely computes the full normal form: a
  // name or a call may be a constructor, which computes the weak head and
  // reads its arguments, unless it is a builtin's, as tt or refl(tt), which
  // no constructor is; and a pair leaves its type uncomputed.
  const hole = node => node?.kind === "name" && node.name === "_";
  const builtin = node => node?.kind === "name"
    && (builtinNames.has(node.name) || primitiveNames.includes(node.name) || isUniverseConstant(node.name));
  const typedPart = node => node?.kind === "call" && node.fn?.kind === "name" && node.fn.name === "typed"
    && node.args.length === 2 ? node.args[1] : null;
  const computesHead = node => typedPart(node) ? computesHead(typedPart(node)) : !hole(node);
  const expression = node => typedPart(node) ? expression(typedPart(node))
    : node.kind === "name" ? builtin(node) : node.kind === "call" ? builtin(node.fn)
    : !["pair", "demand"].includes(node.kind);
  // Removing marks must leave the expected value a pattern, or it would be
  // compared exactly instead: ! and !! are reported only where a hole keeps
  // it one. A mark under !! or !!! leaves that mark. `normalized` is the
  // mark a part is under, the stronger of two.
  let holed = false;
  const marked = (mark, at, value, normalized) => {
    if (normalized && normalized.length >= mark.length)
      warn(at, "W708", `The ${mark} before ${text(value)} asks for nothing more: it is under ${normalized}, which normalizes its part.`);
    else if (!normalized && holed && mark === "!" && computesHead(value))
      warn(at, "W709", `The ! before ${text(value)} asks for nothing more: a pair, an injection, a constructor or an expression computes its part's weak head itself.`);
    else if (!normalized && holed && mark === "!!" && expression(value))
      warn(at, "W710", `The !! before ${text(value)} asks for nothing more: an expression is compared by its normal form.`);
    marks(value, mark.length > 1 && mark.length > (normalized?.length ?? 0) ? mark : normalized);
  };
  // The parts of a pattern: a pair's components and a call's arguments. A
  // mark inside any other expression is refused by the checker (E484).
  const marks = (node, normalized) => {
    if (node?.kind === "demand") marked(node.mark, { start: node.markStart, end: node.markEnd }, node.value, normalized);
    else if (node?.kind === "pair") [node.left, node.right].forEach(part => marks(part, normalized));
    else if (node?.kind === "call") node.args.forEach(part => marks(part, normalized));
  };
  const holes = node => !!node && typeof node === "object" && (hole(node)
    || Object.entries(node).some(([key, value]) => key !== "start" && key !== "end" && holes(value)));
  for (const directive of ast.directives ?? []) if (directive.kind === "evaluate" && directive.expected) {
    holed = holes(directive.expected);
    if (directive.mark) marked(directive.mark, { start: directive.markStart, end: directive.markEnd }, directive.expected, null);
    else marks(directive.expected, null);
  }
  // Each warning with its declaration and its line and column.
  const lineStarts = [0];
  for (let i = 0; i < source.length; i++) if (source[i] === "\n") lineStarts.push(i + 1);
  return warnings.sort((a, b) => a.start - b.start).map(warning => {
    let line = lineStarts.findLastIndex(start => start <= warning.start);
    const declaration = ast.declarations.find(d => d.start <= warning.start && warning.start < d.end);
    return { ...warning, line: line + 1, column: warning.start - lineStarts[line] + 1,
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
