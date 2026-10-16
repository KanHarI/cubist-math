import {formatCubist} from "./cubist/formatter.mjs";
import {tokenize} from "./cubist/parser.mjs";
import {bindingDisplay} from "./cubist/binding-display.mjs";
import {diagnosticCode} from "./diagnostics.mjs";

// A display of the retained frontend syntax, before reference lowering and
// kernel elaboration. This is not an export: captured bindings, public labels
// and generated capabilities cannot all be serialized as ordinary source.
// Never reconstruct an expansion from names or run the generator again.
export function generatedCubist(program, module = program.main) {
  const groups = program.generation.get(module) ?? [];
  const publications = program.publications.get(module) ?? [];
  const symbols = { ...program.symbols };
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
        status: publication.state, reason, code: diagnosticCode(reason), ...program.sourceSite(declaration,module),
        ...(module === program.main ? {} : { sourceModule: module, sourceName: name }) };
      symbols[binding] = info;
    }
  }
  const globals=new Map();
  for(const [key,{binding:record}] of program.compilationBindings.declarationEntries()) {
    if(!globals.has(record.id))globals.set(record.id,{name:record.label,module:record.origin.module,keys:[]});
    const global=globals.get(record.id);
    global.keys.push(key);
    if(symbols[key])global.binding=key;
    const inductive=program.checker.inductives.get(key);
    if(inductive)global.printing={constructors:inductive.constructors.map(c=>({order:c.order})),
      slots:inductive.slots.map(slot=>slot.level===undefined?"parameter":inductive.levels[slot.level].recorded?"recorded":"erased")};
    else if(symbols[key])global.printing={implicit:symbols[key].implicit,assumed:symbols[key].assumed};
  }
  const links = [], contextRanges = [];
  let source = ["// Frontend generation · " + module,
    "// Read-only expansion from the last check. Identity markers ⟦…⟧ denote annotated display syntax.",
    "// This view is not a standalone module or a checked-proof export.", "", ""].join("\n");
  const original = program.sources?.[module] ?? "", ast = program.sourceAsts.get(module);
  const originalLinks = module === program.main ? program.links ?? [] : importedSourceLinks(program, module, original, ast);
  function copy(start, end) {
    const offset = source.length - start;
    if(end>start)contextRanges.push({start:source.length,end:source.length+end-start,origin:{module,start,end}});
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
        const candidates=new Map();
        for(const item of program.declarationBindings.get(`${module}__${declaration.name.text}`)??[]) {
          const id=item.node.bindingId;
          if(!id)continue;
          if(!candidates.has(id))candidates.set(id,new Set());
          candidates.get(id).add(item.binding);
        }
        // A syntax binder can have several elaborated instances. Never pick
        // an arbitrary one; CB6's context selector presents those separately.
        const locals=new Map([...candidates].filter(([,items])=>items.size===1).map(([id,items])=>[id,[...items][0]]));
        const localLinks=[];
        const text=generatedDeclaration(declaration,{table:program.compilationBindings.table,globals,locals,links:localLinks});
        const offset = source.length;
        links.push(...localLinks.map(link => ({ ...symbols[link.binding], ...program.localSymbols[link.binding], ...link, generated: true,
          start: offset + link.start, end: offset + link.end })));
        const declarationId=declaration.name.bindingId;
        const header=localLinks.find(link=>link.bindingId===declarationId);
        if(declarationId)contextRanges.push({start:offset,end:offset+text.length,entry:offset+(header?.start??0),declarationId});
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
      && publications.find(item => item.id === group.id)?.owner === declaration.name.text);
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
  return { module, count, source, links, contextRanges };
}

const comment = text => String(text).split(/\r?\n/).map(line => `// ${line}`).join("\n");

// Imported modules retain elaboration references too, although the Read tab
// only receives links for the main source. Reuse those retained bindings for
// unchanged imported code, without elaborating or resolving names again.
function importedSourceLinks(program, module, source, ast) {
  const links = [];
  for (const declaration of ast?.declarations ?? []) {
    const binding = `${module}__${declaration.name.text}`, info = program.symbols?.[binding];
    if (info) links.push({ ...info, start: declaration.name.start, end: declaration.name.end });
    for (const reference of program.declarationReferences?.get(binding) ?? []) {
      const symbol = program.symbols?.[reference.binding] ?? program.localSymbols?.[reference.binding];
      if (reference.written && symbol) links.push({ ...symbol, name: reference.name, start: reference.start, end: reference.end });
    }
  }
  return links;
}

export function generatedDeclaration(declaration, options = {}) {
  const {links=[]}=options;
  const {tree:d,displays,annotations,declarationName}=bindingDisplay(declaration,options);
  const name=value=>typeof value==="string"?value:value.text??(value.kind?expr(value):value.name);
  let budget = 50000;
  const atom = node => node.kind === "notationArgument" ? atom(node.body)
    : ["name", "reference", "number", "literal", "binaryNumber", "call", "member", "projection",
      "binary", "pathApply", "pair", "transport", "lift"].includes(node.kind) || node.kind === "negation" && !node.qualifier
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
      + (node.hypotheses?.length ? ` with ${node.hypotheses.map(name).join(", ")}` : "")
      + (node.more?.length ? `, ${node.more.map(pattern).join(", ")}` : "");
  }
  const block=body=>`{\n${body.map(statement).join("\n")}\n}`;
  const rules=items=>`[${items.map(rule=>`${rule.reverse?"<- ":""}${expr(rule.value)}`).join(", ")}]`;
  const target=node=>node.kind==="pair"?`(${target(node.left)}, ${target(node.right)})`:name(node);
  const clauses=(items,proof)=>items.map(clause=>`${pattern(clause)} => ${proof?block(clause.body):expr(clause.body)+";"}`).join("\n");
  function obligations(node,proof) {
    if(node.obligations)return ` obligations {\n${clauses(node.obligations,proof)}\n}`;
    const by=node.obligationProof;
    return by?` obligations by ${by.kind==="term"?expr(by.value):by.kind==="block"?block(by.body):statement(by.body[0]).replace(/;$/," ").trim()}`:"";
  }
  function statement(node) {
    if(--budget<0)throw new RangeError("generated syntax exceeds the display budget");
    switch(node.kind) {
      case "exact": return `exact ${expr(node.value)};`;
      case "rfl": return "rfl;";
      case "intro": return `intro ${name(node.name)};`;
      case "ext": return `ext ${name(node.variable)};`;
      case "use": return `use ${expr(node.model)};`;
      case "let": case "obtain": return `${node.kind} ${target(node.target)}${node.type?` : ${expr(node.type)}`:""}`
        + (node.body?` ${block(node.body)}`:` := ${expr(node.value)};`);
      case "hlevel": return `hlevel${node.hints?.length?` with [${node.hints.map(expr).join(", ")}]`:""};`;
      case "rw": return `rw ${rules(node.rules)}${node.target?` at ${node.target}`:""}${node.occurrence!==1?` occurrence ${node.occurrence}`:""};`;
      case "simpOnly": case "simpaOnly": return `${node.kind==="simpOnly"?"simp":"simpa"}${node.only?" only":""} ${rules(node.rules)}`
        + (node.without?.length?` without [${node.without.map(name).join(", ")}]`:"")
        + (node.witnesses?.length?` with [${node.witnesses.map(name).join(", ")}]`:"")
        + (node.at?` at ${name(node.at)} as ${name(node.as)}`:"")+(node.using?` using ${expr(node.using)}`:"")+";";
      case "calc": return `calc {\n${node.steps.map(step=>`${atom(step.left)} = ${expr(step.right)} by `
        +(step.proof.kind==="block"?block(step.proof.body):expr(step.proof.value)+";")).join("\n")}\n}`;
      case "matchStatement": return `${node.induction?"induction":"match"} ${(node.values??[node.value]).map(expr).join(", ")} {\n${clauses(node.clauses,true)}\n}${obligations(node,true)}`;
      default: throw new TypeError(`unsupported ${node.kind} statement`);
    }
  }
  function expr(node) {
    if (--budget < 0) throw new RangeError("generated syntax exceeds the display budget");
    if (!node) throw new TypeError("missing syntax");
    switch (node.kind) {
      case "displaySource": return node.text;
      case "typed": return `typed(${expr(node.type)}, ${expr(node.value)})`;
      case "name": return node.name;
      case "number": return node.text ?? String(node.value);
      case "binaryNumber": return node.spelling ?? `0b${node.digits}`;
      case "literal": return node.text;
      case "call": case "recursiveCall": return atom(node.fn) + (node.implicitArgs ? `{{${node.implicitArgs.map(expr).join(", ")}}}` : "")
        + (node.args.length ? `(${node.args.map(expr).join(", ")})` : "");
      case "namedArgument": return `${name(node.name)} := ${expr(node.value)}`;
      case "pair": return `(${expr(node.left)}, ${expr(node.right)})`;
      case "projection": return `${atom(node.value)}.${node.index}`;
      case "member": return `${atom(node.value)}.${name(node.field)}`;
      case "binary": case "pathApply": return `(${atom(node.left)} ${node.qualifier ? `${atom(node.qualifier)}.(${node.operator})` : node.operator} ${expr(node.right)})`;
      case "negation": return node.qualifier ? `${atom(node.qualifier)}.-${atom(node.operand)}` : `(-${atom(node.operand)})`;
      case "unary": return `${node.operator}${atom(node.operand)}`;
      case "select": return `${atom(node.model)}.(${expr(node.body)})`;
      case "boundNotation": return `${atom(node.selection)}.(${expr(node.body)})`;
      case "notationArgument": return expr(node.body);
      case "operatorOf": return `${atom(node.model)}.(${node.operator})`;
      case "lambda": case "forall": case "exists": case "binderGroup": {
        const kind = node.binderKind ?? node.kind;
        const binders = (node.names ?? [node.name]).map(name).join(", ");
        const domain = node.bound ? ` < ${expr(node.bound)}` : node.domain ? ` : ${expr(node.domain)}` : "";
        return kind === "lambda" ? `fun ${domain ? `(${binders}${domain})` : binders} => ${expr(node.body)}`
          : `${kind} ${binders}${domain}. ${expr(node.body)}`;
      }
      case "pathLambda": return `path ${name(node.dimension)} => ${expr(node.body)}`;
      // In parentheses: the family would otherwise run on into an operator.
      case "transport": case "lift": return `(${node.kind} ${atom(node.value)} along ${atom(node.path)} in ${atom(node.family)})`;
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
        return `${node.kind} ${(node.values ?? [node.value]).map(expr).join(", ")}`
          + (node.motiveName ?? node.index ? ` as ${name(node.motiveName ?? node.index)}` : "")
          + (node.type ? ` return ${expr(node.type)}` : "")
          + ` {\n${clauses.map(clause => `${pattern(clause)} => ${expr(clause.body)};`).join("\n")}\n}${obligations(node,false)}`;
      }
      default: throw new TypeError(`unsupported ${node.kind} syntax`);
    }
  }
  const head = `${d.kind} ${declarationName(d.name)}${parameters(d.params)}`;
  let source;
  if (d.kind === "inductive") {
    const modifier = d.result.modifier;
    source = `${head} : ${modifier ? modifier.kind === "trunc" ? `trunc(${modifier.level}) ` : `${modifier.kind} ` : ""}${expr(d.result.universe)} {\n`
      + d.constructors.map(c => `  ${declarationName(c.name)}${parameters(c.params)}${c.type ? ` : ${expr(c.type)}` : ""};`).join("\n") + "\n}\n";
  } else if (d.kind === "def") {
    const value = d.value ?? (d.body?.length === 1 && d.body[0].kind === "exact" ? d.body[0].value : null);
    source = `${head}${d.type ? ` : ${expr(d.type)}` : ""}`+(value?` := ${expr(value)};\n`:` ${block(d.body)}\n`);
  } else throw new TypeError(`unsupported ${d.kind} declaration`);
  // Keep identity placeholders through formatting, then restore labels and
  // annotated markers. Marked syntax is intentionally not ordinary source.
  const formatted=formatCubist(source,{linearizeTuples:false});
  let output=annotations.length?annotations.map(text=>comment(text)).join("\n")+"\n":"",cursor=0;
  for(const token of tokenize(formatted).slice(0,-1)) {
    output+=formatted.slice(cursor,token.start);
    const shown=displays.get(token.text),start=output.length;
    output+=shown?.text??token.text;
    if(shown?.binding)links.push({name:shown.text,binding:shown.binding,bindingId:shown.bindingId,start,end:output.length});
    cursor=token.end;
  }
  return output+formatted.slice(cursor);
}
