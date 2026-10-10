import { formatCubist } from "./cubist/formatter.mjs";
import { sourceText } from "./cubical-source-text.mjs";
import { substituteTerm, T } from "./translator/core.mjs";

// A display of the retained frontend syntax, before reference lowering and
// kernel elaboration. This is not an export: captured bindings, public labels
// and generated capabilities cannot all be serialized as ordinary source.
// Never reconstruct an expansion from names or run the generator again.
export function generatedCubist(program, module = program.main) {
  const groups = program.generation.get(module) ?? [];
  const publications = program.publications.get(module) ?? [];
  const lines = ["// Frontend generation · " + module,
    "// Read-only expansion from the last check. Captured references use display names.",
    "// This view is not a standalone module or a checked-proof export."];
  const imports = program.sourceAsts.get(module)?.imports ?? [];
  if (imports.length) lines.push("", ...imports.map(name => `import ${name};`));
  let count = 0;
  for (const group of groups) {
    const publication = publications.find(item => item.id === group.id);
    lines.push("", `// ${group.id} · ${publication.state}`);
    if (publication.cause) lines.push(comment(publication.cause.reason));
    for (const declaration of group.declarations) {
      count++;
      try {
        const source = generatedDeclaration(declaration);
        lines.push(source.trimEnd());
      } catch (error) {
        // A display limitation must neither hide a declaration nor change its
        // publication verdict, and must never make proof checking fail.
        lines.push(comment(`${declaration.name.text}: display unavailable (${error.message})`));
      }
    }
  }
  if (!groups.length) lines.push("", "// No frontend-generated declarations in this module.");
  return { module, count, source: lines.join("\n") + "\n" };
}

const comment = text => String(text).split(/\r?\n/).map(line => `// ${line}`).join("\n");

export function generatedDeclaration(declaration) {
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
      case "name": return name(node.spelling ?? node.name);
      case "reference": return name(node.spelling);
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
  const declarations = new Map();
  function declarationName(token) {
    let temporary = `generated_display_${declarations.size}`;
    while (taken.has(temporary)) temporary += "_";
    taken.add(temporary); declarations.set(temporary, name(token));
    return temporary;
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
  let formatted = formatCubist(source, { linearizeTuples: false });
  formatted = formatted.replace(/\b[A-Za-z_][A-Za-z_0-9]*\b/g, token => declarations.get(token) ?? token);
  return formatted;
}
