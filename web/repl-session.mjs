// A REPL session over a checked program. Each entry is checked as a small
// module on top of the ones before it: `repl_1` imports the base module (a
// proof file, or nothing), `repl_2` imports `repl_1`, and so on, so every
// entry sees what came before. Declarations and imports that check extend
// the session; `typeof` and `evaluate` check a scratch module and leave the
// session as it was. Every result is checked by the kernel like a file.

export const replHelp = [
  "let NAME := TERM;     define a name (def works too, with any declaration form)",
  "typeof TERM;          the type of a term",
  "evaluate TERM;        the value of a term",
  "TERM;                 a term alone is evaluated",
  "import MODULE;        load a module, such as naturals",
  "/modules [TEXT]       the modules import can load, or those whose names contain TEXT",
  "/clear                clear the log",
  "/restart              start a new session: forget every name defined here",
  "/help                 this list (help works too)",
].join("\n");

// Commands of the console around a session rather than of the session: the
// console clears its log, or restarts, itself.
export const consoleCommands = new Set(["/clear", "/restart"]);

// Split input into statements. A statement ends at `;` outside brackets; a
// declaration with a block, `def name : T { … }`, ends at its closing brace.
// `rest` is an unfinished statement, and `depth` its open bracket count.
export function replStatements(input) {
  const statements = [];
  let start = 0, depth = 0;
  for (let i = 0; i < input.length; i++) {
    const c = input[i];
    if (c === "/" && input[i + 1] === "/") {
      const end = input.indexOf("\n", i);
      i = end < 0 ? input.length : end;
    } else if ("({[".includes(c)) depth++;
    else if (")}]".includes(c)) {
      depth = Math.max(0, depth - 1);
      const statement = input.slice(start, i + 1);
      if (c === "}" && depth === 0 && !/:=/.test(statement.slice(0, statement.indexOf("{")))) {
        statements.push(statement.trim());
        start = i + 1;
      }
    } else if (c === ";" && depth === 0) {
      if (input.slice(start, i).trim()) statements.push(input.slice(start, i + 1).trim());
      start = i + 1;
    }
  }
  return { statements, rest: input.slice(start).trim(), depth };
}

// A written REPL session: `> ` lines are entries, continued on further `> `
// lines while a bracket is open, and the other lines are their results.
export function replTranscript(text) {
  const entries = [];
  let pending = null;
  for (const line of text.split("\n")) {
    if (line.startsWith("> ")) {
      pending = pending === null ? line.slice(2) : `${pending}\n${line.slice(2)}`;
      if (replStatements(pending).depth > 0) continue;
      entries.push({ input: pending, results: [] });
      pending = null;
    } else if (line.trim() && entries.length) entries.at(-1).results.push(line.trimEnd());
  }
  return entries;
}

export class ReplSession {
  // `modules` lists what import can load: { library, archive } module names.
  constructor(program, { base = null, modules = null } = {}) {
    this.program = program;
    this.base = base;
    this.modules = modules;
    this.previous = base;
    this.count = 0;
    // Statements that extended the session, replayed by rebase.
    this.accepted = [];
  }

  // The same session over another program, such as a rechecked proof: what
  // extended it is replayed, and what no longer checks is dropped.
  async rebase(program, base = this.base) {
    const session = new ReplSession(program, { base, modules: this.modules });
    for (const statement of this.accepted) await session.statement(statement);
    return session;
  }

  // Run every statement of the input; a last statement may omit its `;`.
  async run(input) {
    const { statements, rest } = replStatements(input);
    if (rest) statements.push(rest);
    const results = [];
    for (const statement of statements) results.push(...await this.statement(statement));
    return results;
  }

  async statement(entry) {
    // Comments before a statement, as in a pasted file, are not part of it.
    const text = entry.replace(/^(\s*\/\/[^\n]*(\n|$))+/, "").trim(), source = text.replace(/;\s*$/, "").trim();
    let match;
    if (!source) return [];
    if (source === "help" || source === "/help") return [{ kind: "help", text: replHelp }];
    if ((match = /^\/modules(?:\s+(\S+))?$/.exec(source))) return this.listModules(match[1]);
    if (consoleCommands.has(source)) return [{ kind: "error", text: `${source} is a command of the console, not of an entry.` }];
    if (/^\//.test(source)) return [{ kind: "error", text: `Unknown command ${source.split(/\s/)[0]}. /help lists the commands.` }];
    if ((match = /^typeof\s+([\s\S]+)$/.exec(source))) return this.typeOf(match[1]);
    if ((match = /^import\s+([A-Za-z_][A-Za-z_0-9]*)$/.exec(source))) return this.import(match[1], text);
    if (/^evaluate\s/.test(source) && !/\bexpecting\b/.test(source)) return this.evaluate(source.replace(/^evaluate\s+/, ""));
    if (/^let\s/.test(source)) return this.declare(`def${source.slice(3)};`, text);
    if (/^(def|computable|simp_rule|simp_set|evaluate)\s/.test(source))
      return this.declare(/[;}]$/.test(text.trim()) ? text.trim() : `${source};`, text);
    return this.evaluate(source);
  }

  // The modules import can load: the rebuilt library, then the archive of the
  // first library, whose modules the library's shadow.
  async listModules(filter) {
    if (!this.modules) return [{ kind: "error", text: "This session cannot list its modules." }];
    const { library = [], archive = [] } = await this.modules(), matches = name => !filter || name.includes(filter);
    const groups = [["Library", library.filter(matches)],
      ["Archive, the first library", archive.filter(name => matches(name) && !library.includes(name))]];
    const lines = groups.filter(([, names]) => names.length)
      .map(([label, names]) => `${label} (${names.length}): ${[...names].sort().join(", ")}`);
    if (!lines.length) return [{ kind: "info", text: filter ? `No importable module's name contains ${filter}.` : "No module can be imported." }];
    return [{ kind: "info", text: `${lines.join("\n")}\nLoad one with import NAME;` }];
  }

  async entry(body) {
    const name = `repl_${++this.count}`, header = this.previous ? `import ${this.previous};\n` : "";
    try { return { name, ...await this.program.checkEntry(header + body, name) }; }
    catch (error) { return { name, error: error.message }; }
  }

  typeText(info) {
    const view = this.program.checker.definitionViews?.get(info.binding);
    return view ? this.program.checker.displayText(view.type, 4000) : info.type;
  }

  // Failures of an entry: its declarations, directives, and modules it loaded.
  failures(result, { position = false } = {}) {
    if (result.error) return [{ kind: "error", text: result.error }];
    const clean = reason => position ? reason : reason.replace(/ at \d+:\d+$/, "");
    return [
      ...result.declarations.filter(info => !info.verified && !info.template)
        .map(info => ({ kind: "error", text: clean(info.reason) })),
      ...result.gaps.filter(gap => gap.directive || !gap.name).map(gap => ({ kind: "error", text: clean(gap.reason) })),
    ];
  }

  advance(result, text) {
    this.previous = result.name;
    this.accepted.push(text);
  }

  async declare(body, text) {
    const result = await this.entry(body), failures = this.failures(result);
    const defined = (result.declarations ?? []).filter(info => info.verified || info.template);
    if (defined.length || !failures.length && !result.error) this.advance(result, text);
    return [
      ...defined.map(info => ({ kind: "defined", text: `${info.name} : ${this.typeText(info)}` })),
      ...(result.evaluations ?? []).map(evaluation => ({ kind: "value", text: evaluation.value })),
      ...failures,
    ];
  }

  async import(name, text) {
    const result = await this.entry(`import ${name};`), failures = this.failures(result);
    if (failures.length || !this.program.modules.has(name)) return failures.length ? failures
      : [{ kind: "error", text: `Module ${name} was not loaded.` }];
    this.advance(result, text);
    return [{ kind: "info", text: `Imported ${name}.` }];
  }

  async typeOf(term) {
    const result = await this.entry(`def repl_value := ${term};`), failures = this.failures(result);
    if (failures.length) return failures;
    return [{ kind: "type", text: this.typeText(result.declarations[0]) }];
  }

  // Both sides are the same term, so the directive reports its normal form;
  // an assumption is reported with the path it enters through.
  async evaluate(term) {
    const result = await this.entry(`evaluate ${term} expecting ${term};`), failures = this.failures(result);
    if (failures.length) return failures;
    return result.evaluations.map(evaluation => ({ kind: "value", text: evaluation.value }));
  }
}
