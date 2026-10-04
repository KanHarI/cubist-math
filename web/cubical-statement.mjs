import { tokenize } from "./cubist/parser.mjs";

// Preserve the checked declaration's source notation. This is a statement
// summary; the kernel inspector independently shows the elaborated type.
export function sourceStatement(source, declaration, references = []) {
  if (!declaration.type) return null;
  const bindings = new Map(references.map(reference => [reference.start, reference.binding]));
  const fragment = node => {
    const text = source.slice(node.start, node.end);
    let end = 0;
    const parts = [];
    for (const token of tokenize(text)) {
      if (token.text === "EOF") break;
      const gap = text.slice(end, token.start).replace(/\/\/[^\n]*/g, "").replace(/\s+/g, " ");
      if (gap) parts.push({ text: gap });
      parts.push({ text: token.text, binding: bindings.get(node.start + token.start) });
      end = token.end;
    }
    return parts;
  };
  return {
    conclusion: fragment(declaration.type),
    // A universe parameter U < UU0 has a bound where others have a type; an
    // implicit one is shown in braces, as declared.
    parameters: declaration.params.map(parameter => ({ name: fragment(parameter.name),
      relation: parameter.bound ? "<" : ":", type: fragment(parameter.bound ?? parameter.type),
      ...(parameter.implicit ? { implicit: true } : {}) })),
  };
}
