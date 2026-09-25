// Reading the code examples of the reference pages. Every example declares
// how it is checked; see tests/reference-examples.test.mjs.
export const decode = text => text.replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, "\"").replace(/&#39;/g, "'").replace(/&amp;/g, "&");
const attributes = text => Object.fromEntries([...text.matchAll(/([a-z-]+)="([^"]*)"/g)].map(([, key, value]) => [key, decode(value)]));

export function referenceExamples(file, source) {
  const examples = [];
  for (const match of source.matchAll(/<pre([^>]*)>(?:<code([^>]*)>)?([\s\S]*?)(?:<\/code>)?<\/pre>/g)) {
    const attrs = { ...attributes(match[1]), ...attributes(match[2] ?? "") };
    const line = source.slice(0, match.index).split("\n").length;
    examples.push({ label: `${file}:${line}`, attrs, text: decode(match[3]) });
  }
  return examples;
}

// `// Error: message` states one error that checking reports. On a line of
// its own, it may continue on following `//   …` lines at the same indent.
// A rejected example states every error it causes.
export function statedErrors(text) {
  const errors = [], lines = text.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const start = lines[i].match(/\/\/ Error: (.*)$/);
    if (!start) continue;
    let message = start[1].trim();
    const own = lines[i].match(/^(\s*)\/\/ Error:/);
    while (own && i + 1 < lines.length && lines[i + 1].startsWith(`${own[1]}//   `)) message += ` ${lines[++i].trim().slice(2).trim()}`;
    errors.push(message);
  }
  return errors;
}

// `$ node cli/repl.mjs …` starts the checker, `> …` lines are its input, and
// every other line is output that must appear in order within stdout or
// stderr. `…` in an output line matches any text.
export function transcript(text) {
  let args = null;
  const input = [], expected = [];
  for (const line of text.split("\n")) {
    if (line.startsWith("$ ")) {
      const command = line.match(/^\$ node cli\/repl\.mjs(?: (.*))?$/);
      if (!command || args) throw Error(`A session runs one \`node cli/repl.mjs\` command: ${line}`);
      args = command[1] ? command[1].split(" ") : [];
    } else if (line.startsWith("> ")) input.push(line.slice(2));
    else if (line.trim()) expected.push(line.trimEnd());
  }
  if (!args) throw Error("A session starts with `$ node cli/repl.mjs`.");
  return { args, input, expected };
}
