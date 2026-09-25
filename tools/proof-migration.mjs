// Verify that edited library modules keep their checked meaning. The original
// and edited versions are checked in one native kernel: the edited module is
// loaded under a shadow name next to the original. Two levels are available:
// - "identical": every declaration's checked term and type are the same up to
//   the names of bound variables and generated helpers;
// - "types": every public type is the same by kernel conversion and every
//   declaration keeps the same assumptions. Proof witnesses may change.
// A template has no single checked term, so it is compared through a
// specialization at the least universe levels at which the original checks.
import { createHash } from "node:crypto";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { parse } from "../web/mathscript/parser.mjs";

const SHADOW = "__migration_check";
const termBinders = new Set(["Pi", "Lam", "Sigma", "W"]);
// Which fields a dimension binder scopes, matching the core syntax rules.
const dimensionScope = { Path: ["family"], PLam: ["family", "body"], Comp: ["family", "system"],
  HComp: ["system"], Trans: ["family"] };

// Hash checked syntax up to renaming of bound term variables and dimensions.
// Shared subterms are hashed once for each assignment of their free names, so
// a compact DAG is never expanded into a tree.
export function canonicalHasher({ definitionName = name => name } = {}) {
  const freeMemo = new WeakMap(), hashMemo = new WeakMap();
  const formulaNames = formula => formula.flat().map(literal => literal.slice(0, -2));
  function free(node) {
    if (!node || typeof node !== "object") return [];
    if (freeMemo.has(node)) return freeMemo.get(node);
    const names = new Set();
    const add = (values, except = null) => { for (const name of values) if (name !== except) names.add(name); };
    if (Array.isArray(node)) node.forEach(child => add(free(child)));
    else if (node.tag === "Var") names.add(`t:${node.name}`);
    else for (const [key, value] of Object.entries(node)) {
      // face and arg hold interval formulas, except App.arg, which is a term.
      if ((key === "face" || key === "arg") && Array.isArray(value)) { add(formulaNames(value).map(name => `d:${name}`)); continue; }
      if (!value || typeof value !== "object") continue;
      let except = null;
      if (termBinders.has(node.tag) && key === "body") except = `t:${node.name}`;
      if (dimensionScope[node.tag]?.includes(key)) except = `d:${node.dim}`;
      add(free(value), except);
    }
    const result = [...names].sort();
    freeMemo.set(node, result);
    return result;
  }
  // scope maps each bound name to the depth of its binder. A bound name is
  // hashed as its distance to that binder (a de Bruijn index), so a subterm's
  // hash depends only on the subterm and the indices of its free names.
  function hash(node, scope, depth) {
    if (node === null || typeof node !== "object") return JSON.stringify(node ?? null);
    const index = name => scope.has(name) ? `#${depth - 1 - scope.get(name)}` : null;
    const names = free(node), key = names.map(name => index(name) ?? name).join("\u0000");
    let byScope = hashMemo.get(node);
    if (!byScope) hashMemo.set(node, byScope = new Map());
    if (byScope.has(key)) return byScope.get(key);
    const digest = createHash("sha1");
    const inner = name => new Map(scope).set(name, depth);
    if (Array.isArray(node)) {
      digest.update("[");
      for (const child of node) digest.update(hash(child, scope, depth) + ",");
    } else {
      digest.update(node.tag ?? "{");
      for (const fieldName of Object.keys(node).sort()) {
        const value = node[fieldName];
        if (fieldName === "tag") continue;
        if ((termBinders.has(node.tag) && fieldName === "name") || (dimensionScope[node.tag] && fieldName === "dim")) continue;
        digest.update(`|${fieldName}=`);
        if (node.tag === "Var" && fieldName === "name") digest.update(index(`t:${value}`) ?? `free:${value}`);
        else if (node.tag === "DefRef" && fieldName === "name") digest.update(definitionName(value));
        else if ((fieldName === "face" || fieldName === "arg") && Array.isArray(value))
          digest.update(JSON.stringify(value.map(clause => clause.map(literal => {
            const name = literal.slice(0, -2);
            return `${index(`d:${name}`) ?? `free:${name}`}${literal.slice(-2)}`;
          }).sort()).sort()));
        else if (value && typeof value === "object") {
          let childScope = scope, childDepth = depth;
          if (termBinders.has(node.tag) && fieldName === "body") { childScope = inner(`t:${node.name}`); childDepth++; }
          if (dimensionScope[node.tag]?.includes(fieldName)) { childScope = inner(`d:${node.dim}`); childDepth++; }
          digest.update(hash(value, childScope, childDepth));
        } else digest.update(JSON.stringify(value));
      }
    }
    const result = digest.digest("hex");
    byScope.set(key, result);
    return result;
  }
  return term => hash(term, new Map(), 0);
}

const universeParameters = declaration => {
  let count = 0;
  for (const parameter of declaration.params) {
    if (parameter.type?.kind !== "name" || parameter.type.name !== "Universe") break;
    count++;
  }
  if (!declaration.params.length) for (let value = declaration.value; value?.domain?.kind === "name"
    && value.domain.name === "Universe"; value = value.body) count += value.names?.length ?? 1;
  return count;
};

// modules: names of edited library modules. readOriginal/readEdited return
// module source text. Returns one report per module; `failures` lists every
// declaration that does not meet the requested level.
export async function verifyMigration({ modules, readOriginal, readEdited, level = "identical",
  maxUniverse = 2 } = {}) {
  if (!["identical", "types"].includes(level)) throw new Error(`Unknown verification level: ${level}`);
  const program = new CubicalProgram(await createCubical(), readOriginal, { collectReferences: false });
  const checker = program.checker, views = checker.definitionViews;
  try {
    const reports = [];
    for (const module of modules) {
      const original = await program.check(`import ${module};`, `${module}${SHADOW}_original_root`);
      const shadow = `${module}${SHADOW}`;
      // A program reports every main module checked so far; keep this one's.
      const edited = await program.check(await readEdited(module), shadow);
      const editedOutputs = edited.outputs.filter(output => output.binding.startsWith(`${shadow}__`));
      const originalOutputs = Object.values(program.symbols).filter(symbol => symbol.sourceModule === module);
      const report = { module, identical: 0, typesPreserved: 0, templates: 0, failures: [] };
      reports.push(report);
      const fail = (name, reason) => report.failures.push({ name, reason });
      if (!original.complete && program.gaps.some(gap => gap.module === module))
        fail("(module)", "The original module does not fully check.");
      const originalNames = originalOutputs.map(symbol => symbol.name);
      const editedNames = editedOutputs.map(output => output.name);
      if (JSON.stringify(originalNames) !== JSON.stringify(editedNames))
        fail("(declarations)", `Declaration list changed: ${JSON.stringify(originalNames)} -> ${JSON.stringify(editedNames)}`);
      const rename = name => name.startsWith(`${shadow}__`) ? `${module}__${name.slice(shadow.length + 2)}` : name;
      // Generated unfolding helpers are named by a session serial; compare
      // their checked bodies instead of their names.
      let hashTerm;
      const helper = name => /__unfolding_\d+$/.test(name) && views.has(name);
      hashTerm = canonicalHasher({ definitionName: name => helper(name)
        ? `helper:${hashTerm(views.get(name).term)}` : rename(name) });
      const assumptions = binding => (program.symbols[binding]?.axioms ?? [])
        .map(name => checker.assumptionLabels.get(name) ?? name).sort().join(",");
      const compare = (name, before, after, originalBinding, editedBinding) => {
        if (!before || !after) return fail(name, "No checked definition to compare.");
        if (assumptions(originalBinding) !== assumptions(editedBinding))
          return fail(name, `Assumptions changed: ${assumptions(originalBinding)} -> ${assumptions(editedBinding)}`);
        if (hashTerm(before.term) === hashTerm(after.term) && hashTerm(before.type) === hashTerm(after.type)) {
          report.identical++; return;
        }
        if (level === "identical") return fail(name, "The checked term changed.");
        let same;
        try { same = checker.equal(before.type, after.type); }
        catch (error) { same = false; }
        if (same) report.typesPreserved++;
        else fail(name, "The public type changed.");
      };
      const source = parse(await readEdited(module));
      for (const symbol of originalOutputs) {
        const output = editedOutputs.find(item => item.name === symbol.name);
        if (!output) continue;
        if (symbol.verified && !output.verified) { fail(symbol.name, `No longer checks: ${output.reason}`); continue; }
        if (!symbol.verified && !symbol.template) continue;
        if (!symbol.template) {
          compare(symbol.name, views.get(symbol.binding), views.get(output.binding), symbol.binding, output.binding);
          continue;
        }
        // Specialize both versions at the least levels where the original checks.
        report.templates++;
        const declaration = source.declarations.find(item => item.name.text === symbol.name);
        const count = declaration ? universeParameters(declaration) : 1;
        let compared = false;
        for (let level = 0; level <= maxUniverse && !compared; level++) {
          const levels = Array(count).fill(`U${level}`).join(", ");
          const probe = `probe_${symbol.name}_${level}`;
          const beforeModule = `${module}${SHADOW}_probe_original_${symbol.name}_${level}`;
          const afterModule = `${module}${SHADOW}_probe_edited_${symbol.name}_${level}`;
          await program.check(`import ${module};\ndef ${probe} = ${symbol.name}(${levels});`, beforeModule);
          if (!program.symbols[`${beforeModule}__${probe}`]?.verified) continue;
          await program.check(`import ${shadow};\ndef ${probe} = ${symbol.name}(${levels});`, afterModule);
          compared = true;
          if (!program.symbols[`${afterModule}__${probe}`]?.verified) {
            fail(symbol.name, `Specialization at ${levels} no longer checks.`); break;
          }
          const key = `__${Array(count).fill(`U${level}`).join("_")}`;
          compare(symbol.name, views.get(`${symbol.binding}${key}`), views.get(`${shadow}__${symbol.name}${key}`),
            `${beforeModule}__${probe}`, `${afterModule}__${probe}`);
        }
        if (!compared) report.notes = [...(report.notes ?? []), `${symbol.name}: no specialization up to U${maxUniverse} checks; not compared.`];
      }
    }
    return reports;
  } finally { program.dispose(); }
}
