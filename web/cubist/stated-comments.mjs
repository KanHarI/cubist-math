// What a source's checked comments state (tools/inline-errors.mjs): an error
// or a warning the checker reports, or what a print directive shows, as a
// comment directly above the declaration or directive it belongs to,
//
//   // Error: E606: Type mismatch: found succ(zero) = succ(zero), expected zero = zero.
//
// continued on `//   …` lines. The Cubist tests mark their intended failures
// so, and the benchmark reads them (benchmark-runner.mjs).
export const comment = /^\s*\/\/ (Error|Warning|Output): (.*)$/, continued = /^\s*\/\/ {3}(.*)$/;
// Text as a comment holds it: its whitespace collapsed, and a message
// without the position that ends a reason.
const collapsed = text => text.replace(/\s+/g, " ").trim();
export const normal = (text, label = "Error") => label === "Output" ? collapsed(text) : collapsed(text).replace(/ at \d+:\d+$/, "");

// What the comments state, each at the line (from 0) below its comment block.
export function stated(source) {
  const lines = source.split("\n"), items = [];
  let pending = [];
  for (let i = 0; i < lines.length; i++) {
    const match = lines[i].match(comment);
    if (match) {
      let text = match[2];
      while (i + 1 < lines.length && continued.test(lines[i + 1])) text += ` ${lines[++i].match(continued)[1]}`;
      pending.push({ label: match[1], text: normal(text, match[1]) });
      continue;
    }
    if (/^\s*\/\//.test(lines[i])) continue;
    for (const item of pending) items.push({ line: i, ...item });
    pending = [];
  }
  return items;
}
