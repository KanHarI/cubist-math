import { parse, tokenize } from "./parser.mjs";
import { linearizeTuples as linearizeTupleSyntax, expandedSyntax } from "./tuples.mjs";

const line = { kind: "line", flat: " " }, soft = { kind: "line", flat: "" };
const hard = { kind: "hard" };
const group = body => ({ kind: "group", body });
const indent = body => ({ kind: "indent", body });
// A paragraph packs complete phrases, instead of breaking every separator when
// the whole statement exceeds the width. Nested delimiters still have groups.
const flow = body => ({ kind: "flow", body });
const punctuation = new Set([",", ";", ")", "]", "}"]);
const operators = new Set(["=", "->", "=>", "+", "*", "<", "<=", "and", "or"]);

function render(document, width) {
  let output = "", column = 0;
  const stack = [{ doc: document, level: 0, flat: false }];
  function fits(doc, remaining) {
    const pending = [doc];
    while (pending.length && remaining >= 0) {
      const d = pending.pop();
      if (typeof d === "string") remaining -= d.length;
      else if (Array.isArray(d)) pending.push(...[...d].reverse());
      else if (d.kind === "hard") return true;
      else if (d.kind === "line") remaining -= d.flat.length;
      else pending.push(d.body);
    }
    return remaining >= 0;
  }
  while (stack.length) {
    const { doc, level, flat } = stack.pop();
    if (typeof doc === "string") { output += doc; column += doc.length; }
    else if (Array.isArray(doc)) for (const d of [...doc].reverse()) stack.push({ doc: d, level, flat });
    else if (doc.kind === "group") stack.push({ doc: doc.body, level, flat: fits(doc.body, width - column) });
    else if (doc.kind === "flow") {
      const pieces = [];
      let phrase = [];
      for (const d of doc.body) {
        if (d === line) { pieces.push(phrase, line); phrase = []; }
        else phrase.push(d);
      }
      pieces.push(phrase);
      for (let i = pieces.length - 1; i >= 0; i--) {
        const d = pieces[i];
        stack.push({ doc: d === line ? { kind: "flowBreak", next: pieces[i + 1] } : d, level, flat });
      }
    }
    else if (doc.kind === "flowBreak") {
      if (flat || fits(doc.next, width - column - 1)) { output += " "; column++; }
      else { output = output.replace(/ +$/, "") + "\n" + " ".repeat(level); column = level; }
    }
    else if (doc.kind === "indent") stack.push({ doc: doc.body, level: level + 2, flat });
    else if (doc.kind === "line" && flat) { output += doc.flat; column += doc.flat.length; }
    else { output = output.replace(/ +$/, "") + "\n" + " ".repeat(level); column = level; }
  }
  return output.replace(/[ \t]+\n/g, "\n").replace(/\n{3,}/g, "\n\n").trimEnd() + "\n";
}

// Canonicalize right-nested tuples first, with expanded-AST equality checked by
// the rewriter. Everything else changes whitespace only; comments stay intact.
export function formatMathScript(source, { printWidth = 100, linearizeTuples = true } = {}) {
  if (!Number.isInteger(printWidth) || printWidth < 40 || printWidth > 240)
    throw new Error("Print width must be an integer between 40 and 240.");
  if (typeof linearizeTuples !== "boolean") throw new Error("linearizeTuples must be Boolean.");
  if (linearizeTuples) source = linearizeTupleSyntax(source).source;
  const tokens = tokenize(source).slice(0, -1);
  const construction = tokens[0]?.text === "construction";
  const syntax = construction ? null : parse(source);
  const declarationEnds = new Set(syntax?.declarations.map(node => node.end) ?? []);
  // `computable` and `evaluate` are ordinary names except where the parser
  // found a top-level modifier or directive.
  const itemStarts = new Set([
    ...(syntax?.declarations ?? []).map(node => node.modifierStart).filter(Number.isInteger),
    ...(syntax?.directives ?? []).filter(node => node.kind === "evaluate").map(node => node.start),
  ]);
  // A binder's short domain is one phrase: `forall f : A -> B,` must not
  // split the arrow merely because the surrounding theorem is long.
  const domains = [];
  const expressionBlockEnds = new Set();
  const assignmentTokens = new Set(), annotationStarts = new Set(), proofBodyStarts = new Set();
  // `simp_set name = [rules]` is an assignment, not an `=[T]` carrier.
  const setAssignments = new Set();
  const tokenBefore = new Map(tokens.map((token, index) => [token.start, tokens[index - 1]]));
  const tokenAfter = new Map(tokens.map((token, index) => [token.end, tokens[index + 1]]));
  function visit(node) {
    if (!node || typeof node !== "object") return;
    if (node.kind === "withUnfolding") expressionBlockEnds.add(node.end);
    // Only declaration/let assignments introduce an indented right-hand side.
    // An equality inside an annotated definition's type is not an assignment.
    const valueStart = node.valueStart ?? (node.kind === "let" ? node.value?.start : undefined);
    if (valueStart !== undefined && tokenBefore.get(valueStart)?.text === "=")
      assignmentTokens.add(tokenBefore.get(valueStart).start);
    if (node.type && ["def", "have"].includes(node.kind)) {
      annotationStarts.add(node.type.start);
      const next = tokenAfter.get(node.type.end);
      if (next?.text === "{") proofBodyStarts.add(next.start);
    }
    if (node.kind === "simp_set") {
      const equals = tokenAfter.get(node.name.end);
      if (equals?.text === "=") setAssignments.add(equals.start);
    }
    if (node.domain && source.slice(node.domain.start, node.domain.end).replace(/\s+/g, " ").length < printWidth / 2)
      domains.push([node.domain.start, node.domain.end]);
    for (const value of Object.values(node)) {
      if (Array.isArray(value)) value.forEach(visit);
      else if (value && typeof value === "object") visit(value);
    }
  }
  visit(syntax);
  const comments = [...source.matchAll(/\/\/[^\n\r]*/g)].map(m => ({ text: m[0], start: m.index, end: m.index + m[0].length, comment: true }));
  const all = [...tokens, ...comments].sort((a, b) => a.start - b.start);
  let position = 0;
  function sequence(close = null) {
    const docs = [], statement = [];
    let previous = null;
    let assignment = -1;
    let annotation = -1, proofBody = -1;
    function flush() {
      if (statement.length) {
        const parts = statement.splice(0);
        // Keep the whole right-hand side indented, not just its first token.
        if (annotation >= 0) {
          const signature = parts.slice(0, proofBody < 0 ? parts.length : proofBody);
          docs.push(group([signature.slice(0, annotation), indent([line, flow(signature.slice(annotation))])]));
          if (proofBody >= 0) docs.push(" ", parts.slice(proofBody));
        } else docs.push(group(assignment < 0 ? flow(parts)
          : [parts.slice(0, assignment), indent([line, flow(parts.slice(assignment))])]));
      }
      assignment = -1;
      annotation = -1; proofBody = -1;
    }
    while (position < all.length) {
      const token = all[position];
      if (token.text === close) {
        position++; flush();
        while (docs.at(-1) === hard) docs.pop();
        return docs;
      }
      const preceding = all[position - 1];
      if (!close && preceding && /\n\s*\n/.test(source.slice(preceding.end, token.start))) {
        flush();
        if (docs.at(-1) !== hard) docs.push(hard);
        docs.push(hard);
        previous = null;
      }
      position++;
      const text = token.text;
      if (token.comment) {
        const trailing = previous && !source.slice(previous.end, token.start).includes("\n");
        if (trailing) {
          if (statement.at(-1) === line) statement.pop();
          statement.push(" ");
        }
        else { flush(); if (docs.length && docs.at(-1) !== hard) docs.push(hard); }
        statement.push(text); flush(); docs.push(hard);
        if (!close && trailing && preceding && declarationEnds.has(preceding.end)) docs.push(hard);
        previous = null; continue;
      }
      const itemStart = ["def", "opaque", "construction", "simp_rule", "simp_set"].includes(text)
        || itemStarts.has(token.start);
      if (!close && itemStart && previous && !(["opaque", "computable"].includes(previous.text) && text === "def")
        && !(previous.text === "computable" && text === "opaque")) {
        flush(); docs.push(hard, hard); previous = null;
      }
      const space = previous && !punctuation.has(text) && !["(", "["].includes(previous.text)
        && !(text === "(" && (/^[A-Za-z_0-9]+$/.test(previous.text) && !["fun", "exact", "return", "obtain", "as", "and", "or"].includes(previous.text) || [")", "]"].includes(previous.text) || previous.text === "}" && expressionBlockEnds.has(previous.end)))
        && !(text === "[" && previous.text === "=" && !setAssignments.has(previous.start));
      if (space && previous.text !== ",") {
        if (annotationStarts.has(token.start)) annotation = statement.length;
        else if (proofBodyStarts.has(token.start)) proofBody = statement.length;
        else if (assignmentTokens.has(previous.start) && assignment < 0) assignment = statement.length;
        else statement.push(operators.has(text) && ["->", "and", "or"].includes(text)
          && !domains.some(([start, end]) => start <= token.start && token.end <= end) ? line : " ");
      }
      if (["(", "[", "{"].includes(text)) {
        const end = { "(": ")", "[": "]", "{": "}" }[text];
        const body = sequence(end);
        statement.push(text === "{" ? ["{", indent([hard, body]), hard, "}"]
          : group([text, indent([soft, body]), soft, end]));
        previous = { text: end, end: all[position - 1].end };
        if (!close && declarationEnds.has(previous.end)) {
          // A trailing comment stays beside its declaration; separate the
          // next declaration (and its documentation) with one empty line.
          if (!(all[position]?.comment && !source.slice(previous.end, all[position].start).includes("\n"))) {
            flush(); docs.push(hard, hard); previous = null;
          }
        } else if (text === "{" && !expressionBlockEnds.has(previous.end) && all[position] && ![";", ",", ")", "]", "}"].includes(all[position].text) && !all[position].comment) {
          flush(); docs.push(hard); previous = null;
        }
      } else if (text === ";") {
        statement.push(text);
        // A following line comment belongs to this statement.
        if (!(all[position]?.comment && !source.slice(token.end, all[position].start).includes("\n"))) {
          flush(); docs.push(hard);
          if (!close && declarationEnds.has(token.end)) docs.push(hard);
          previous = null;
        } else {
          previous = token;
        }
      } else {
        statement.push(text);
        if (text === ",") statement.push(line);
        previous = token;
      }
    }
    if (close) throw new Error(`Missing ${close}`);
    flush(); return docs;
  }
  const formatted = render(sequence(), printWidth);
  const before = tokens.map(t => t.text), after = tokenize(formatted).slice(0, -1).map(t => t.text);
  if (JSON.stringify(before) !== JSON.stringify(after)) throw new Error("Formatting changed source tokens.");
  if (!construction && expandedSyntax(parse(formatted)) !== expandedSyntax(syntax))
    throw new Error("Formatting changed the expanded syntax tree.");
  return formatted;
}
