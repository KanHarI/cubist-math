// Diagnostic codes (web/diagnostics.mjs): every error and warning the
// checker can report has one. This tool finds the messages in the sources,
// checks that each has a code, and gives new messages codes.
//
//   node tools/diagnostic-codes.mjs          check: every message has a code,
//                                            and every code's message is still
//                                            in the sources or retired
//   node tools/diagnostic-codes.mjs --add    give each new message the next free
//                                            code of its group, write the
//                                            registry, and write the index of
//                                            codes in reference/errors.html
//
// A message is a string or template literal where the sources report one:
// the argument of Error(…), of withCode(…) and of error classes such as
// SearchLimit(…), a
// value assigned to `.message`, `detail` or `reason`, a linter warning, a
// function that returns a message template, and a kernel failure, ck_fail(k,
// "…"). A template's `${…}` becomes `…`, which matches any text. A literal
// counts only when it reads as a sentence: it starts with a letter, …, a
// tilde (as ~p does) or a minus (as -x does), and has a space and at least ten other
// characters, so names and keys are not messages.
import { readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { diagnostics, groups } from "../web/diagnostics.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
const sourceFiles = directory => readdirSync(join(root, directory)).filter(name => /\.(mjs|c)$/.test(name))
  .sort().map(name => `${directory}/${name}`);

// The group of a source file's messages, by what the file does.
const fileGroups = [
  [/^web\/cubist\/lint\.mjs$/, "W7"],
  [/^web\/(cubist|translator)\/theories\.mjs$/, "E8"],
  [/^web\/cubist\//, "E1"],
  [/^web\/translator\/(builtins|tactics|proof-rewrite|proof-goals|motives|simp-registry|fuel|evaluation)\.mjs$/, "E4"],
  [/^web\/translator\/(inductive|match|patterns|hlevel)\.mjs$/, "E5"],
  [/^web\/cubical-signatures\.mjs$/, "E5"],
  // Argument inference's earlier messages are E3's, which is full.
  [/^web\/translator\/arguments\.mjs$/, "E7"],
  // Notation's messages in elaboration, also beyond full E3 (L2.10).
  [/^web\/translator\/notations\.mjs$/, "E9"],
  [/^web\/translator\//, "E3"],
  [/^web\/(cubical-instruction-driver|cubical-syntax|cubical-kernel|cubical-reduction|cubical-elaborator|cubical-instructions|cubical-assumptions|cubical-transaction)\.mjs$/, "E6"],
  [/^(web|cli)\//, "E2"],
  [/^kernel\/src\/(signatures|eliminators|hit_composition)\.c$/, "K1"],
  [/^kernel\/src\/instruction/, "K2"],
  [/^kernel\/src\//, "K3"],
];
export const groupOf = file => fileGroups.find(([pattern]) => pattern.test(file))?.[1];

// A JavaScript string or template literal starting at `at`: its text, each
// ${…} as …, and the index after it.
function literal(source, at) {
  const quote = source[at];
  let text = "", i = at + 1;
  while (i < source.length && source[i] !== quote) {
    if (source[i] === "\\") { text += source[i + 1]; i += 2; continue; }
    if (quote === "`" && source[i] === "$" && source[i + 1] === "{") {
      let depth = 1;
      for (i += 2; depth && i < source.length; i++) {
        if (source[i] === "{") depth++;
        else if (source[i] === "}") depth--;
        else if ("'\"`".includes(source[i])) i = literal(source, i).end - 1;
      }
      text += "…";
      continue;
    }
    text += source[i++];
  }
  return { text, end: i + 1 };
}
const sentence = text => /^[-~A-Za-z…]/.test(text) && /\s/.test(text.trim()) && text.replace(/…/g, "").trim().length >= 10;

// Where a JavaScript source reports a message: a call's arguments, or an
// assigned or returned value up to the end of its statement.
const reporting = /\b(?:Kernel)?Error\(|\bwithCode\(|\bnew [A-Z]\w*(?:Limit|Exhausted|Failure|Stopped)\(|\.message\s*=(?!=)|\bwarn\([^,]*,|\breason:\s*|\bdetail\s*=(?!=)|=\s*\(?[\w, ]*\)?\s*=>\s*(?=`)/g;
function javascriptMessages(file) {
  const source = readFileSync(join(root, file), "utf8"), found = [];
  for (const match of source.matchAll(reporting)) {
    const call = match[0].endsWith("(");
    for (let i = match.index + match[0].length, depth = 1; i < source.length && depth;) {
      const c = source[i];
      if (c === "(") depth++;
      else if (c === ")") depth--;
      else if (!call && depth === 1 && (c === ";" || c === "\n" && /[;,]\s*$/.test(source.slice(match.index, i)))) break;
      else if (c === "/" && source[i + 1] === "/") { i = source.indexOf("\n", i); continue; }
      else if ("'\"`".includes(c)) {
        // Literals joined by + are one message.
        let { text, end } = literal(source, i);
        for (let next; (next = /^\s*\+\s*(?=['"`])/.exec(source.slice(end, end + 200)));) {
          const part = literal(source, end + next[0].length);
          text += part.text;
          end = part.end;
        }
        if (sentence(text)) found.push(text);
        i = end;
        continue;
      }
      i++;
    }
  }
  return found;
}
// A kernel failure: ck_fail(k, "…"), ck_fail_as(k, KIND, "…") or a file's
// own fail helper, with C's adjacent literals joined.
function kernelMessages(file) {
  const source = readFileSync(join(root, file), "utf8").replace(/\/\*[\s\S]*?\*\//g, "").replace(/\/\/[^\n]*/g, "");
  return [...source.matchAll(/\b(?:ck_fail_as|ck_fail|fail_as|fail)\s*\(\s*k\s*,\s*(?:[A-Z_]+\s*,\s*)?((?:"(?:[^"\\]|\\.)*"\s*)+)/g)]
    .map(match => [...match[1].matchAll(/"((?:[^"\\]|\\.)*)"/g)].map(part => part[1].replace(/\\(.)/g, "$1")).join(""));
}

// Every message in the sources, each once, with the file it is first found in.
export function sourceMessages() {
  const files = [...["web", "web/cubist", "web/translator", "cli"].flatMap(sourceFiles).filter(file => file.endsWith(".mjs")),
    ...sourceFiles("kernel/src").filter(file => file.endsWith(".c"))];
  const messages = new Map();
  for (const file of files) {
    if (file === "web/diagnostics.mjs" || !groupOf(file)) continue;
    for (const text of file.endsWith(".c") ? kernelMessages(file) : javascriptMessages(file))
      if (!messages.has(text)) messages.set(text, file);
  }
  return messages;
}

// The registry against the sources: messages without a code, and codes whose
// message is in no source and is not retired.
export function compare(registry = diagnostics, messages = sourceMessages()) {
  const coded = new Set(registry.map(([, message]) => message));
  return {
    missing: [...messages].filter(([text]) => !coded.has(text)).map(([text, file]) => ({ text, file, group: groupOf(file) })),
    stale: registry.filter(([, message, status]) => status !== "retired" && !messages.has(message)).map(([code, message]) => ({ code, message })),
  };
}

// The registry with codes for the missing messages: the next free number of
// each one's group. Codes are never renumbered or reused.
export function assign(registry, missing) {
  const next = new Map(), result = registry.map(entry => [...entry]);
  for (const [code] of registry) next.set(code.slice(0, 2), Math.max(next.get(code.slice(0, 2)) ?? 0, Number(code.slice(2))));
  for (const { text, group } of missing) {
    const number = (next.get(group) ?? 0) + 1;
    if (number > 99) throw Error(`Group ${group} has no free code for: ${text}`);
    next.set(group, number);
    result.push([`${group}${String(number).padStart(2, "0")}`, text]);
  }
  const order = Object.keys(groups);
  return result.sort((a, b) => order.indexOf(a[0].slice(0, 2)) - order.indexOf(b[0].slice(0, 2)) || a[0].localeCompare(b[0]));
}

// The registry's source, with its header kept.
export function registrySource(registry, current = readFileSync(join(root, "web/diagnostics.mjs"), "utf8")) {
  const start = current.indexOf("export const diagnostics = ["), end = current.indexOf("];", start) + 2;
  let group = null;
  const lines = registry.map(entry => {
    const heading = entry[0].slice(0, 2) !== group ? `  // ${groups[group = entry[0].slice(0, 2)]}\n` : "";
    return `${heading}  ${JSON.stringify(entry).replace(/^\[/, "[").replace(/","/g, "\", \"")},`;
  });
  return `${current.slice(0, start)}export const diagnostics = [\n${lines.join("\n")}\n];${current.slice(end)}`;
}

// The errors chapter's index of every code (reference/errors.html#codes),
// one table per group. A code that a section above explains has its anchor
// there, and the index links to it; any other code has its anchor here.
const escape = text => text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
export function codeIndex(registry, html) {
  const start = html.indexOf('          <section id="codes">'), end = html.indexOf("          </section>\n", start) + "          </section>\n".length;
  const explained = new Set([...html.slice(0, start).matchAll(/<tr id="([EKW]\d{3})">/g)].map(match => match[1]));
  const intro = html.slice(start, html.indexOf("            <h3", start));
  const tables = Object.keys(groups).map(group => `            <h3 id="codes-${group.toLowerCase()}">${groups[group]}</h3>
            <div class="table-scroll"><table class="codes">
              <thead><tr><th>Code</th><th>Message</th></tr></thead>
              <tbody>
${registry.filter(([code]) => code.startsWith(group)).map(([code, message, status]) => explained.has(code)
    ? `                <tr><td><a href="#${code}"><code>${code}</code></a></td><td>${escape(message)}${status === "retired" ? " (retired)" : ""}</td></tr>`
    : `                <tr id="${code}"><td><code>${code}</code></td><td>${escape(message)}${status === "retired" ? " (retired)" : ""}</td></tr>`).join("\n")}
              </tbody>
            </table></div>
`).join("");
  return `${html.slice(0, start)}${intro}${tables}          </section>\n${html.slice(end)}`;
}

if (process.argv[1]?.endsWith("diagnostic-codes.mjs")) {
  const { missing, stale } = compare();
  if (process.argv.includes("--add")) {
    const registry = assign(diagnostics, missing), errors = join(root, "web/reference/errors.html");
    if (missing.length) writeFileSync(join(root, "web/diagnostics.mjs"), registrySource(registry));
    writeFileSync(errors, codeIndex(registry, readFileSync(errors, "utf8")));
    console.log(`Gave codes to ${missing.length} new messages, and wrote the errors chapter's index.`);
  } else if (missing.length) {
    for (const { text, file } of missing) console.log(`no code: ${text}  (${file})`);
  }
  for (const { code, message } of stale) console.log(`${code} is in no source; retire it with "retired": ${message}`);
  process.exitCode = (!process.argv.includes("--add") && missing.length) || stale.length ? 1 : 0;
}
