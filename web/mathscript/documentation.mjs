// Inspector documentation is prose from the checked source, never proof evidence.
// Only a contiguous block of full-line // comments immediately above a
// declaration belongs to it. A physical blank line separates section headers;
// an empty // line separates paragraphs inside documentation.
export function leadingDocumentation(source, declarationStart) {
  const lineStart = source.lastIndexOf("\n", declarationStart - 1) + 1;
  const prefix = source.slice(lineStart, declarationStart);
  // Mathematical parsing points at `def`.
  if (!/^[\t ]*$/.test(prefix)) return null;
  let start = lineStart, end = lineStart;
  const lines = [];
  while (end > 0) {
    const previous = source.lastIndexOf("\n", end - 2) + 1;
    const match = source.slice(previous, end).match(/^[\t ]*\/\/ ?([^\r\n]*)(?:\r?\n)?$/);
    if (!match) break;
    lines.unshift(match[1].trim());
    start = previous;
    end = previous;
  }
  if (!lines.length) return null;
  const paragraphs = [], current = [];
  for (const line of [...lines, ""]) {
    if (line) current.push(line);
    else if (current.length) { paragraphs.push(current.join(" ")); current.length = 0; }
  }
  return { text: paragraphs.join("\n\n"), source: source.slice(start, lineStart), start, end: lineStart };
}
