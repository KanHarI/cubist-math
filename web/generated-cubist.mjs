import { formatCubist } from "./cubist/formatter.mjs";
import { tokenize } from "./cubist/parser.mjs";
import { rewritten } from "./cubist/scopes.mjs";
import { sourceText } from "./cubical-source-text.mjs";
import { substituteTerm, T } from "./translator/core.mjs";
import { lexicalBinding } from "./translator/lexical.mjs";
import { diagnosticCode } from "./diagnostics.mjs";

// A display of the retained frontend syntax, before reference lowering and
// kernel elaboration. This is not an export: captured bindings, public labels
// and generated capabilities cannot all be serialized as ordinary source.
// Never reconstruct an expansion from names or run the generator again.
export function generatedCubist(program, module = program.main) {
  const groups = program.generation.get(module) ?? [];
  const publications = program.publications.get(module) ?? [];
  const symbols = { ...program.symbols }, unavailable = new Map(), env = program.modules?.get(module);
  // A blocked family may never have reached the checker. Its retained
  // declarations still open the inspector's diagnostic, without asking the
  // kernel for definitions that were not published.
  for (const group of groups) {
    const publication = publications.find(item => item.id === group.id);
    if (publication.state === "checked") continue;
    for (const declaration of group.declarations) {
      const name = declaration.name.text, binding = `${module}__${name}`;
      if (symbols[binding]) continue;
      const reason = publication.cause?.reason ?? `Generated family ${group.id} is ${publication.state}.`;
      const info = { name, binding, role: declaration.kind, verified: false,
        status: publication.state, reason, code: diagnosticCode(reason), definitionStart: declaration.start,
        ...(module === program.main ? {} : { sourceModule: module, sourceName: name }) };
      symbols[binding] = info;
      unavailable.set(binding, info);
    }
  }
  const identities = new Map(Object.keys(symbols).map(binding => [lexicalBinding(binding), binding]));
  const links = [];
  let source = ["// Frontend generation · " + module,
    "// Read-only expansion from the last check. Captured references use display names.",
    "// This view is not a standalone module or a checked-proof export.", "", ""].join("\n");
  const original = program.sources?.[module] ?? "", ast = program.sourceAsts.get(module);
  const originalLinks = module === program.main ? program.links ?? [] : importedSourceLinks(program, module, original, ast);
  function copy(start, end) {
    const offset = source.length - start;
    links.push(...originalLinks.filter(link => link.start >= start && link.end <= end)
      .map(link => ({ ...link, start: offset + link.start, end: offset + link.end })));
    source += original.slice(start, end);
  }
  let count = 0;
  const shown = new Set();
  function expansion(group) {
    shown.add(group);
    const publication = publications.find(item => item.id === group.id);
    source += `\n// ${group.id} · ${publication.state}\n`;
    if (publication.cause) source += comment(publication.cause.reason) + "\n";
    for (const declaration of group.declarations) {
      count++;
      try {
        // Resolve retained identities, never a captured reference's spelling.
        // Plain generated names can also refer to declarations, but a local
        // binder with that spelling must stay local.
        const bindings = new WeakMap();
        const { kind, params, type, value, body, result, constructors } = declaration;
        if (env) rewritten({ kind, params, type, value, body, result, constructors }, (node, bound) => {
          let binding;
          if (node.kind === "reference") binding = identities.get(node.binding);
          else if (node.kind === "name" && !bound.has(node.name.split(".")[0])) {
            const entry = env?.get(node.name);
            binding = entry?.tag === "DefRef" ? entry.name : entry?.binding;
          }
          if (symbols[binding]) bindings.set(node, binding);
          return node;
        });
        const localLinks = [];
        const text = generatedDeclaration(declaration, {
          resolve: node => node.kind === "declaration"
            ? symbols[`${module}__${node.name}`]?.binding : bindings.get(node),
          links: localLinks,
        });
        const offset = source.length;
        links.push(...localLinks.map(link => ({ ...unavailable.get(link.binding), ...link, generated: true,
          start: offset + link.start, end: offset + link.end })));
        source += text;
      } catch (error) {
        // A display limitation must neither hide a declaration nor change its
        // publication verdict, and must never make proof checking fail.
        source += comment(`${declaration.name.text}: display unavailable (${error.message})`) + "\n";
      }
    }
  }
  let cursor = 0;
  for (const declaration of ast?.declarations ?? []) {
    const replacements = groups.filter(group => !shown.has(group)
      && publications.find(item => item.id === group.id)?.owner === declaration.name.text
      && group.declarations[0]?.name.start === declaration.name.start);
    if (!replacements.length) continue;
    copy(cursor, declaration.start);
    // Keep the replaced source visible as comments. Existing comments inside
    // it keep their spelling; only its code lines need a comment prefix.
    const trailingComment = original.slice(declaration.end).match(/^[ \t]*\/\/[^\r\n]*/)?.[0] ?? "";
    const end = declaration.end + trailingComment.length;
    source += original.slice(declaration.start, end).split(/\r?\n/)
      .map(line => /^\s*\/\//.test(line) ? line : `// ${line}`).join("\n") + "\n";
    for (const group of replacements) expansion(group);
    cursor = end;
  }
  copy(cursor, original.length);
  // Retention can also be inspected without a source AST (for example, a
  // diagnostic fixture). Never silently drop an unmatched generated family.
  for (const group of groups) if (!shown.has(group)) expansion(group);
  if (!groups.length) source += "\n// No frontend-generated declarations in this module.\n";
  return { module, count, source, links };
}

const comment = text => String(text).split(/\r?\n/).map(line => `// ${line}`).join("\n");

// Imported modules retain elaboration references too, although the Read tab
// only receives links for the main source. Reuse those retained bindings for
// unchanged imported code, without elaborating or resolving names again.
function importedSourceLinks(program, module, source, ast) {
  const tokens = new Map(tokenize(source).map(token => [token.start, token]));
  const links = [];
  for (const declaration of ast?.declarations ?? []) {
    const binding = `${module}__${declaration.name.text}`, info = program.symbols?.[binding];
    if (info) links.push({ ...info, start: declaration.name.start, end: declaration.name.end });
    for (const reference of program.declarationReferences?.get(binding) ?? []) {
      const token = tokens.get(reference.start);
      const symbol = program.symbols?.[reference.binding] ?? program.localSymbols?.[reference.binding];
      if (token && symbol) links.push({ ...symbol, name: token.text, start: token.start, end: token.end });
    }
  }
  return links;
}

export function generatedDeclaration(declaration, { resolve = () => null, links = [] } = {}) {
  // Internal pattern binders contain primes, which Cubist does not accept.
  // Choose a consistent display name apart from every existing source name.
  const taken = new Set(), seen = new WeakSet();
  function collect(node) {
    if (!node || typeof node !== "object" || seen.has(node)) return;
    seen.add(node);
    for (const key of ["name", "text", "spelling"]) if (typeof node[key] === "string")
      for (const part of node[key].split(".")) taken.add(part);
    for (const [key, value] of Object.entries(node))
      if (!["theory", "generated", "scope", "value"].includes(key) || key === "value" && !node.tag && node.kind !== "instantiated") collect(value);
  }
  collect(declaration);
  const names = new Map();
  function name(value) {
    const text = typeof value === "string" ? value : value.text;
    if (!/[′'\u0000]/.test(text)) return text;
    if (!names.has(text)) {
      const stem = text.replace(/[^\p{L}\p{N}_]/gu, "_");
      let candidate = stem, suffix = 0;
      while (taken.has(candidate)) candidate = `${stem}_${++suffix}`;
      taken.add(candidate); names.set(text, candidate);
    }
    return names.get(text);
  }
  const displays = new Map();
  function display(text, binding, declaration = false) {
    if (!binding && !declaration) return text;
    let temporary = `generated_display_${displays.size}`;
    while (taken.has(temporary)) temporary += "_";
    taken.add(temporary); displays.set(temporary, { text, binding, declaration });
    return temporary;
  }
  let budget = 50000;
  const atom = node => ["name", "reference", "number", "literal", "binaryNumber", "call", "member", "projection"].includes(node.kind)
    ? expr(node) : `(${expr(node)})`;
  function parameters(params = []) {
    // Keep groups intact: a shared domain is outside all its binders.
    const groups = [];
    for (const p of params) {
      const previous = groups.at(-1);
      if (previous && p.group !== undefined && previous[0].group === p.group
          && previous[0].implicit === p.implicit && previous[0].type === p.type && previous[0].bound === p.bound) previous.push(p);
      else groups.push([p]);
    }
    const content = group => `${group.map(p => name(p.name)).join(", ")} ${group[0].bound ? "<" : ":"} ${expr(group[0].bound ?? group[0].type)}`;
    const implicit = groups.filter(group => group[0].implicit), explicit = groups.filter(group => !group[0].implicit);
    return (implicit.length ? `{{${implicit.map(content).join(", ")}}}` : "")
      + (explicit.length ? `(${explicit.map(content).join(", ")})` : "");
  }
  function pattern(node) {
    const head = name(node.constructor ?? node);
    const args = node.args?.map(arg => arg.kind === "pattern" ? pattern(arg) : name(arg));
    return head + (args ? `(${args.join(", ")})` : "")
      + (node.binders?.length ? ` ${node.binders.map(name).join(" ")}` : "")
      + (node.coordinates?.length ? ` @ ${node.coordinates.map(name).join(" @ ")}` : "")
      + (node.more?.length ? `, ${node.more.map(pattern).join(", ")}` : "");
  }
  function expr(node) {
    if (--budget < 0) throw new RangeError("generated syntax exceeds the display budget");
    if (!node) throw new TypeError("missing syntax");
    switch (node.kind) {
      case "name": return display(name(node.spelling ?? node.name), resolve(node));
      case "reference": return display(name(node.spelling), resolve(node));
      case "number": return node.text ?? String(node.value);
      case "binaryNumber": return node.spelling ?? `0b${node.digits}`;
      case "literal": return node.text;
      case "call": case "recursiveCall": return atom(node.fn) + (node.implicitArgs ? `{{${node.implicitArgs.map(expr).join(", ")}}}` : "")
        + (node.args.length ? `(${node.args.map(expr).join(", ")})` : "");
      case "namedArgument": return `${name(node.name)} := ${expr(node.value)}`;
      case "pair": return `(${expr(node.left)}, ${expr(node.right)})`;
      case "projection": return `${atom(node.value)}.${node.index}`;
      case "member": return `${atom(node.value)}.${name(node.field)}`;
      case "binary": case "pathApply": return `(${expr(node.left)} ${node.qualifier ? `${atom(node.qualifier)}.(${node.operator})` : node.operator} ${expr(node.right)})`;
      case "negation": return node.qualifier ? `${atom(node.qualifier)}.-${atom(node.operand)}` : `(-${atom(node.operand)})`;
      case "unary": return `${node.operator}${atom(node.operand)}`;
      case "select": return `${atom(node.model)}.(${expr(node.body)})`;
      case "operatorOf": return `${atom(node.model)}.(${node.operator})`;
      case "lambda": case "forall": case "exists": case "binderGroup": {
        const kind = node.binderKind ?? node.kind;
        const binders = (node.names ?? [node.name]).map(name).join(", ");
        const domain = node.bound ? ` < ${expr(node.bound)}` : node.domain ? ` : ${expr(node.domain)}` : "";
        return kind === "lambda" ? `fun ${domain ? `(${binders}${domain})` : binders} => ${expr(node.body)}`
          : `${kind} ${binders}${domain}. ${expr(node.body)}`;
      }
      case "pathLambda": return `<${name(node.dimension)}> ${expr(node.body)}`;
      case "along": return `along ${expr(node.family)} by ${expr(node.path)} from ${expr(node.value)}`;
      case "withUnfolding": return `with unfolding [${node.hints.map(name).join(", ")}] { ${expr(node.body)} }`;
      case "unpack": return `unpack ${expr(node.value)} as (${name(node.left)}, ${name(node.right)}) return ${expr(node.type)} { ${expr(node.body)}; }`;
      case "match": case "induction": {
        const clauses = node.clauses ?? (node.kind === "match" && node.left ? [
          {constructor:{text:"left"},binders:[node.left],body:node.leftBody},
          {constructor:{text:"right"},binders:[node.right],body:node.rightBody},
        ] : node.kind === "induction" && node.base ? [
          {constructor:{text:"zero"},body:node.base},
          {constructor:{text:"succ"},binders:[node.hypothesis],body:node.step},
        ] : null);
        if (!clauses) throw new TypeError("unsupported induction syntax");
        if (node.obligationsToken) throw new TypeError("explicit match obligations");
        return `${node.kind} ${(node.values ?? [node.value]).map(expr).join(", ")}`
          + (node.motiveName ?? node.index ? ` as ${name(node.motiveName ?? node.index)}` : "")
          + (node.type ? ` return ${expr(node.type)}` : "")
          + ` {\n${clauses.map(clause => `${pattern(clause)} => ${expr(clause.body)};`).join("\n")}\n}`;
      }
      case "instantiated": {
        // These arguments are the generator's own parameter names. Reconnect
        // them exactly as elaboration does, without kernel work, rather than
        // exposing the temporary lambda's fresh native variable names.
        let value = node.value;
        for (const arg of node.args) {
          if (arg.kind !== "name" || !["Lam", "LLam"].includes(value.tag)) throw new TypeError("unsupported instantiated argument");
          value = substituteTerm(value.body, value.name, T.variable(name(arg.name)));
        }
        const term = sourceText(value, {}, 10000);
        if (term.includes("…")) throw new RangeError("instantiated term exceeds the display budget");
        return term;
      }
      default: throw new TypeError(`unsupported ${node.kind} syntax`);
    }
  }
  const d = declaration;
  // Ordinary source cannot declare dotted generated names. As the generator
  // does for its templates, format with temporary declaration names, then
  // restore the names actually owned by the frontend.
  function declarationName(token) {
    return display(name(token), resolve({ kind: "declaration", name: token.text }), true);
  }
  const head = `${d.kind} ${declarationName(d.name)}${parameters(d.params)}`;
  let source;
  if (d.kind === "inductive") {
    const modifier = d.result.modifier;
    source = `${head} : ${modifier ? modifier.kind === "trunc" ? `trunc(${modifier.level}) ` : `${modifier.kind} ` : ""}${expr(d.result.universe)} {\n`
      + d.constructors.map(c => `  ${declarationName(c.name)}${parameters(c.params)}${c.type ? ` : ${expr(c.type)}` : ""};`).join("\n") + "\n}\n";
  } else if (d.kind === "def") {
    const value = d.value ?? (d.body?.length === 1 && d.body[0].kind === "exact" ? d.body[0].value : null);
    if (!value) throw new TypeError("unsupported generated proof block");
    source = `${head}${d.type ? ` : ${expr(d.type)}` : ""} := ${expr(value)};\n`;
  } else throw new TypeError(`unsupported ${d.kind} declaration`);
  // Formatting changes whitespace only. Track links by token index through
  // it, restoring references before formatting so their real widths count.
  // Declaration placeholders remain until afterward because dotted names
  // are not legal declaration syntax in an ordinary source module.
  const starts = new Map(), ends = new Map();
  let index = 0;
  for (const token of tokenize(source).slice(0, -1)) {
    const shown = displays.get(token.text);
    const length = shown && !shown.declaration ? tokenize(shown.text).length - 1 : 1;
    if (shown?.binding) {
      const link = { name: shown.text, binding: shown.binding };
      starts.set(index, link); ends.set(index + length - 1, link);
    }
    index += length;
  }
  source = source.replace(/\b[A-Za-z_][A-Za-z_0-9]*\b/g, token => {
    const shown = displays.get(token);
    return shown && !shown.declaration ? shown.text : token;
  });
  const formatted = formatCubist(source, { linearizeTuples: false });
  let output = "", cursor = 0;
  for (const [index, token] of tokenize(formatted).slice(0, -1).entries()) {
    output += formatted.slice(cursor, token.start);
    if (starts.has(index)) starts.get(index).start = output.length;
    output += displays.get(token.text)?.text ?? token.text;
    if (ends.has(index)) links.push({ ...ends.get(index), end: output.length });
    cursor = token.end;
  }
  return output + formatted.slice(cursor);
}
