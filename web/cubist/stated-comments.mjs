// What a source's checked comments state (tools/inline-errors.mjs): an error
// or a warning the checker reports, or what a print directive shows, as a
// comment directly above the declaration or directive it belongs to,
//
//   // Error: E606: Type mismatch: found succ(zero) = succ(zero), expected zero = zero.
//
// continued on `//   …` lines. The Cubist tests mark their intended failures
// so, and the benchmark reads them (benchmark-runner.mjs).
const annotation = /\/\/ (Error|Warning|Output): (.*)$/;
export const comment = new RegExp(`^\\s*${annotation.source}`), continued = /^\s*\/\/ {3}(.*)$/;
// Text as a comment holds it: its whitespace collapsed, and a message
// without the position that ends a reason.
const collapsed = text => text.replace(/\s+/g, " ").trim();
export const normal = (text, label = "Error") => label === "Output" ? collapsed(text) : collapsed(text).replace(/ at \d+:\d+$/, "");

// One annotation block, preserving its text and last line. Reference examples
// also allow trailing comments, with continuations only at the original indent.
// Module comments retain their existing indentation-insensitive continuation.
export function readComment(lines, start, { inline = false, sameIndent = false } = {}) {
  const match = lines[start].match(inline ? annotation : comment);
  if (!match) return null;
  const own = lines[start].match(/^(\s*)\/\/ (?:Error|Warning|Output): /);
  let text = match[2].trim(), end = start;
  while (own && end + 1 < lines.length && continued.test(lines[end + 1])
    && (!sameIndent || lines[end + 1].startsWith(`${own[1]}//   `)))
    text += ` ${lines[++end].match(continued)[1].trim()}`;
  return { label: match[1], text, end };
}

// What the comments state, each at the line (from 0) below its comment block.
export function stated(source) {
  const lines = source.split("\n"), items = [];
  let pending = [];
  for (let i = 0; i < lines.length; i++) {
    const block = readComment(lines, i);
    if (block) {
      i = block.end;
      pending.push({ label: block.label, text: normal(block.text, block.label) });
      continue;
    }
    if (/^\s*\/\//.test(lines[i])) continue;
    for (const item of pending) items.push({ line: i, ...item });
    pending = [];
  }
  return items;
}
