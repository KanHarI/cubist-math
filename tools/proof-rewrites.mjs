// Source rewrites that move library proofs to newer syntax. Each rewrite edits
// only the spans it recognizes and keeps all other text, including comments.
// A rewrite is skipped wherever it would drop a comment. tools/
// verify-proof-migration.mjs then checks the checked meaning of the result.
import { parse, tokenize } from "../web/mathscript/parser.mjs";

// Rewrites whose output elaborates to the same checked terms.
export const identicalRewrites = ["path-apply", "along", "intro", "have", "params", "fun"];
// Rewrites that keep public types but may change proof terms.
export const typePreservingRewrites = ["wrappers", "rfl", "path-lambda", "ext"];

const statementKinds = new Set(["intro", "let", "obtain", "have", "haveValue", "cases", "exact", "rfl",
  "calc", "rw", "simpOnly", "simpaOnly", "ext", "over"]);
const spanned = value => value && typeof value === "object" && Number.isInteger(value.start) && Number.isInteger(value.end);
const identifiers = text => new Set(text.match(/[A-Za-z_][A-Za-z_0-9]*/g) ?? []);
const squash = text => text.replace(/\s+/g, " ").trim();
// Operands that bind at least as tightly as application need no parentheses.
const atomic = node => ["name", "call", "number", "binaryNumber", "pathApply"].includes(node.kind);

export function rewriteModule(source, { rewrites = identicalRewrites, skip = new Set() } = {}) {
  const enabled = new Set(rewrites);
  const ast = parse(source), tokens = tokenize(source);
  const comment = (start, end) => source.slice(start, end).includes("//");
  const applied = new Map();
  const count = name => applied.set(name, (applied.get(name) ?? 0) + 1);

  // The text of a node, with rewritten children spliced into the original span.
  function render(node, context = "operand") {
    const rule = rewriteNode(node, context);
    if (rule !== null) return rule;
    return splice(node);
  }
  function childUnits(node) {
    const units = [];
    for (const [key, value] of Object.entries(node)) {
      if (["start", "end"].includes(key)) continue;
      const context = childContext(node, key);
      if (Array.isArray(value)) {
        if (value.some(item => statementKinds.has(item?.kind))) units.push(...blockUnits(value));
        else for (const item of value) if (spanned(item)) units.push({ start: item.start, end: item.end,
          text: () => render(item, context) });
      } else if (spanned(value) && value !== node) units.push({ start: value.start, end: value.end,
        text: () => render(value, context) });
    }
    return units.sort((left, right) => left.start - right.start || right.end - left.end);
  }
  function splice(node, start = node.start, end = node.end) {
    let out = "", position = start;
    for (const unit of childUnits(node)) {
      if (unit.start < position || unit.end > end) continue;
      out += source.slice(position, unit.start) + unit.text();
      position = unit.end;
    }
    return out + source.slice(position, end);
  }
  function childContext(node, key) {
    if (node.kind === "call") return key === "fn" ? "callee" : "delimited";
    if (["pair", "exact", "let", "obtain", "have", "haveValue", "over", "along", "rw", "simpOnly",
      "simpaOnly", "lambda", "binderGroup", "forall", "exists", "pathLambda", "withUnfolding"].includes(node.kind))
      return "delimited";
    if (node.kind === undefined && key === "value") return "delimited";
    return "operand";
  }
  // Consecutive statements of a block, with runs of introductions merged.
  function blockUnits(statements) {
    const units = [], seen = new Set();
    for (let index = 0; index < statements.length; index++) {
      const statement = statements[index];
      if (seen.has(statement.start)) continue;
      if (statement.kind === "intro" && enabled.has("intro")) {
        const names = [], run = [];
        let cursor = index;
        while (cursor < statements.length && statements[cursor].kind === "intro"
          && (!run.length || !comment(run.at(-1).end, statements[cursor].start))) {
          const current = statements[cursor];
          if (!run.length || current.start !== run.at(-1).start) run.push(current);
          names.push(current.name.text);
          cursor++;
        }
        for (const item of run) seen.add(item.start);
        if (run.length > 1) {
          count("intro");
          units.push({ start: run[0].start, end: run.at(-1).end, text: () => `intro ${names.join(" ")};` });
        } else units.push({ start: statement.start, end: statement.end, text: () => source.slice(statement.start, statement.end) });
        index = cursor - 1;
        continue;
      }
      seen.add(statement.start);
      units.push({ start: statement.start, end: statement.end, text: () => render(statement, "statement") });
    }
    return units;
  }
  // Library wrappers whose bodies are the builtins: name -> [arity, builtin, kept arguments].
  const wrappers = { concatenate: [7, "trans", [5, 6]], append_path: [6, "trans", [4, 5]],
    inverse: [5, "sym", [4]], ap: [7, "cong", [3, 6]] };
  function rewriteNode(node, context) {
    if (node.kind === "exact" && node.value.kind === "call" && node.value.fn.kind === "name"
      && !comment(node.start, node.end)) {
      const { name } = node.value.fn, args = node.value.args;
      if (name === "refl" && args.length === 1 && enabled.has("rfl")) { count("rfl"); return "rfl;"; }
      if (name === "path" && args.length === 2 && enabled.has("path-lambda")
        && args.every(arg => arg.kind === "lambda" && arg.domain?.kind === "name" && arg.domain.name === "Interval")) {
        count("path-lambda");
        return `exact path ${args[1].name.text} => ${render(args[1].body, "delimited")};`;
      }
      if (name === "FunExt" && args.length === 6 && enabled.has("ext")) {
        const proof = args[5];
        count("ext");
        if (proof.kind === "lambda" && proof.domain) {
          const body = proof.body, closed = enabled.has("rfl") && body.kind === "call" && body.fn.kind === "name"
            && body.fn.name === "refl" && body.args.length === 1;
          if (closed) count("rfl");
          return `ext ${proof.name.text};\n${closed ? "rfl;" : `exact ${render(body, "delimited")};`}`;
        }
        const used = identifiers(source.slice(proof.start, proof.end));
        const point = ["x", "a", "v", "w", "t", "z"].find(name => !used.has(name)) ?? "x_ext";
        const callee = atomic(proof) ? render(proof, "operand") : `(${render(proof, "delimited")})`;
        return `ext ${point};\nexact ${callee}(${point});`;
      }
    }
    if (node.kind === "call" && node.fn.kind === "name" && enabled.has("wrappers")
      && Object.hasOwn(wrappers, node.fn.name)) {
      const [arity, builtin, kept] = wrappers[node.fn.name];
      if (node.args.length === arity && !comment(node.start, node.end)) {
        count("wrappers");
        return `${builtin}(${kept.map(index => render(node.args[index], "delimited")).join(", ")})`;
      }
    }
    if (node.kind === "call" && node.fn.kind === "name") {
      const name = node.fn.name, args = node.args, gaps = () => {
        let position = node.fn.end;
        for (const arg of args) { if (comment(position, arg.start)) return true; position = arg.end; }
        return comment(position, node.end);
      };
      if (name === "at" && args.length === 2 && enabled.has("path-apply") && !gaps()) {
        count("path-apply");
        const left = atomic(args[0]) ? render(args[0], "operand") : `(${render(args[0], "delimited")})`;
        const text = `${left} @ ${render(args[1], "operand")}`;
        return context === "callee" ? `(${text})` : text;
      }
      if (name === "transport" && args.length === 5 && enabled.has("along") && !gaps()
        && !comment(args[1].start, args[2].end)) {
        count("along");
        const family = ["name", "call"].includes(args[0].kind) ? render(args[0], "operand") : `(${render(args[0], "delimited")})`;
        const text = `along ${family} by ${render(args[3], "delimited")} from ${render(args[4], "delimited")}`;
        return ["delimited", "statement"].includes(context) ? text : `(${text})`;
      }
    }
    if (node.kind === "have" && enabled.has("have") && node.body?.length === 1 && node.body[0].kind === "exact"
      && !comment(node.start, node.body[0].value.start) && !comment(node.body[0].value.end, node.end)) {
      count("have");
      return `have ${node.name.text} : ${render(node.type, "delimited")} := ${render(node.body[0].value, "delimited")};`;
    }
    if (["lambda", "binderGroup"].includes(node.kind) && (node.binderKind ?? "lambda") === "lambda"
      && enabled.has("fun") && !node.generatedBinder && source.startsWith("fun", funStart(node))) {
      const text = funChain(node);
      if (text !== null) { count("fun"); return text; }
    }
    return null;
  }
  // A parenthesized lambda's span starts at its opening parenthesis.
  function funStart(node) {
    return node.start + /^[(\s]*/.exec(source.slice(node.start, node.start + 64))[0].length;
  }
  // fun (x : A) => fun (y : A) => body  becomes  fun (x y : A) => body.
  // Parentheses around the whole lambda are kept.
  function funChain(node) {
    const groups = [];
    let current = node, separate = 0;
    while (["lambda", "binderGroup"].includes(current.kind) && (current.binderKind ?? "lambda") === "lambda"
      && current.domain) {
      if (current !== node && !current.generatedBinder) {
        if (!source.startsWith("fun", current.start)) break;
        separate++;
      }
      groups.push({ names: (current.names ?? [current.name]).map(token => token.text), domain: current.domain });
      current = current.body;
    }
    const body = current;
    if (groups.length < 2 || comment(node.start, body.start)) return null;
    const merged = mergeGroups(groups.map(group => ({ ...group, text: squash(render(group.domain, "delimited")) })));
    if (!separate && merged.length === groups.length) return null;
    const lead = source.slice(node.start, funStart(node)), trail = source.slice(body.end, node.end);
    return `${lead}fun ${merged.map(group => `(${group.names.join(" ")} : ${group.text})`).join(" ")} => ${
      render(body, "delimited")}${trail}`;
  }
  // Adjacent binders share a group when their domains are the same text and
  // do not mention a name bound earlier in that group.
  function mergeGroups(groups) {
    const merged = [];
    for (const group of groups) {
      const previous = merged.at(-1);
      if (previous && previous.text === group.text
        && ![...identifiers(group.text)].some(name => previous.names.includes(name)))
        previous.names.push(...group.names);
      else merged.push({ ...group, names: [...group.names] });
    }
    return merged;
  }

  function renderDeclaration(declaration) {
    const edits = [];
    const parameters = declaration.valueParameters?.length ? declaration.valueParameters : declaration.params;
    const open = tokens.findIndex(token => token.start >= declaration.name.end);
    if (parameters.length && tokens[open]?.text === "(") {
      let depth = 0, close = open;
      for (; close < tokens.length; close++) {
        if (tokens[close].text === "(") depth++;
        if (tokens[close].text === ")" && !--depth) break;
      }
      const start = tokens[open].start, end = tokens[close].end;
      const groups = [];
      for (const parameter of parameters) {
        const last = groups.at(-1);
        if (last && last.group === parameter.group) last.names.push(parameter.name.text);
        else groups.push({ group: parameter.group, names: [parameter.name.text], domain: parameter.type });
      }
      const rendered = groups.map(group => ({ ...group, text: squash(render(group.domain, "delimited")) }));
      const merged = enabled.has("params") && !comment(start, end) ? mergeGroups(rendered) : rendered;
      const retyped = rendered.some(group => group.text !== squash(source.slice(group.domain.start, group.domain.end)));
      if (merged.length < rendered.length) count("params");
      // Regenerate the list only when it changes; comments keep it in place.
      if (!comment(start, end) && (merged.length < rendered.length || retyped)) edits.push({ start, end,
        text: `(${merged.map(group => `${group.names.join(" ")} : ${group.text}`).join(", ")})` });
      else if (retyped) for (const group of groups) edits.push({ start: group.domain.start, end: group.domain.end,
        text: render(group.domain, "delimited") });
    }
    if (declaration.value) {
      let value = declaration.value;
      while (value.start < declaration.valueStart) value = value.body;
      edits.push({ start: value.start, end: value.end, text: render(value, "statement") });
    }
    if (declaration.type) edits.push({ start: declaration.type.start, end: declaration.type.end,
      text: render(declaration.type, "delimited") });
    if (declaration.body) for (const unit of blockUnits(declaration.body))
      edits.push({ start: unit.start, end: unit.end, text: unit.text() });
    edits.sort((left, right) => left.start - right.start);
    let out = "", position = declaration.start;
    for (const edit of edits) {
      if (edit.start < position) continue;
      out += source.slice(position, edit.start) + edit.text;
      position = edit.end;
    }
    return out + source.slice(position, declaration.end);
  }

  let out = "", position = 0;
  for (const declaration of ast.declarations) {
    if (declaration.kind !== "def" || skip.has(declaration.name.text)) continue;
    out += source.slice(position, declaration.start) + renderDeclaration(declaration);
    position = declaration.end;
  }
  return { source: out + source.slice(position), applied: Object.fromEntries([...applied].filter(([, value]) => value)) };
}
