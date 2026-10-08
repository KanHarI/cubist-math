// Resolved syntax separates a declaration's identity from its source spelling.
// A reference is not a name: renaming, substitution and source generation must
// preserve it as syntax, never look it up again or print its binding as source.
import {rewritten} from "./scopes.mjs";

export function reference(binding, spelling, at = {}) {
  const {kind: _, name: __, ...site} = at;
  return {...site, kind: "reference", binding, spelling};
}

export const referenceKey = node => node.kind === "reference" ? node.binding : node.kind === "name" ? node.name : null;

// A field selection keeps its receiver as syntax. In particular, a local
// T's T.M cannot be confused with the declaration whose qualified name is T.M.
export function members(node, receiver, fields) {
  const dots = node.qualifiedDots ?? (node.qualifiedDot ? [node.qualifiedDot] : []);
  let value = receiver, end = receiver.end;
  for (const [index, text] of fields.entries()) {
    const start = dots[index]?.end ?? end + 1;
    end = start + text.length;
    value = {kind: "member", value, field: {text, start, end}, start: node.start, end,
      ...(node.synthetic ? {synthetic: true} : {})};
  }
  return value;
}

// The elaborator still has one environment for lexical aliases and source
// names. Lower identities only at its entry, after syntax transformation.
// Theory records remain resolved syntax for subsequent derivations.
export function elaborationSyntax(node) {
  const {theory, ...syntax} = node;
  return {...rewritten(syntax, n => n.kind === "reference"
    ? {...n, kind: "name", name: n.binding} : n), ...(theory ? {theory} : {})};
}
