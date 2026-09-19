import { Builder } from "./builder.mjs";

function dependencySteps(steps, roots) {
  const byName = new Map(steps.map(step => [step.name, step])), needed = new Set(), pending = [...roots];
  while (pending.length) {
    const name = pending.pop();
    if (!name || needed.has(name)) continue;
    const step = byName.get(name);
    if (!step) throw new Error(`Unknown inspection premise: ${name}`);
    needed.add(name); pending.push(...step.args, ...step.free, step.context);
  }
  return steps.filter(step => needed.has(step.name));
}

export function exportInspection(checked, binding, side, folded = true) {
  if (!["expression", "type"].includes(side)) throw new Error("Unknown inspection side");
  if (!checked.kernel.bindings.has(binding)) throw new Error("Unknown inspection binding");
  const result = folded ? checkedFoldedView(checked, binding, { certificate: true }) : null;
  const evidence = result?.verified[side];
  if (!evidence) return { document: { format: "thth-workbench", version: 1,
    policy: { allowAxioms: checked.allowAxioms }, steps: dependencySteps(checked.kernel.steps, [binding]) },
    selection: { name: binding, side } };
  const target = side === "expression" ? result.inspectionBinding ?? evidence.candidate : evidence.candidate;
  const roots = [target, evidence.original, evidence.witness];
  if (side === "expression" && result.inspectionBinding) roots.push(result.verified.type.witness);
  const steps = dependencySteps(result.certificate.steps, roots);
  const originalNames = new Set(checked.kernel.bindings.keys()), used = new Set(steps.map(s => s.name));
  const document = { ...result.certificate, steps: steps.map(s => ({ ...s, hidden: originalNames.has(s.name) ? s.hidden : true })),
    folding: { ...result.certificate.folding, verified: { [side]: evidence } } };
  function nameResult(target, suggestion) {
    let name = suggestion, i = 0;
    while (used.has(name) || used.has(name + "_refl")) name = suggestion + "_" + (++i);
    used.add(name); used.add(name + "_refl");
    document.steps.push({ name: name + "_refl", op: "DefEqRefl", args: [target], free: [], context: null, hidden: true },
      { name, op: "DefEqExtR", args: [name + "_refl"], free: [], context: null, hidden: false });
    return name;
  }
  const name = nameResult(target, `${binding}_folded_${side}`);
  nameResult(evidence.witness, `${binding}_${side}_folding_equality`);
  return { document, selection: { name, side: "expression" } };
}

// Labels only annotate actual context-reference nodes. They do not replace
// expressions, and duplicate labels remain distinguished by kernel context IDs.
export function inspectionContextReferences(checked, kernel = checked.kernel) {
  const result = {};
  for (const local of checked.localViews ?? []) {
    const binding = kernel.bindings.get(local.binding);
    if (binding?.kind !== "judgement") continue;
    const tree = kernel.node(kernel.module._wb_view(kernel.handle, 0, binding.id, 0));
    if (["CRef", "UCRef"].includes(tree.kind) && !(tree.parameter in result))
      result[tree.parameter] = { name: local.name, binding: local.binding };
  }
  return result;
}

export function inspectionContextNames(checked, kernel = checked.kernel) {
  return Object.fromEntries(Object.entries(inspectionContextReferences(checked, kernel)).map(([id, ref]) => [id, ref.name]));
}

// Recognize notation only for the imported library axiom's actual AST identity.
// A user declaration that merely reuses the spelling lib_Trunc does not qualify.
export function inspectionAxiomNotation(checked, kernel = checked.kernel) {
  if (!checked.preludeAxioms?.includes("lib_Trunc")) return {};
  const binding = kernel.bindings.get("lib_Trunc");
  if (binding?.kind !== "judgement") return {};
  const term = kernel.node(kernel.module._wb_view(kernel.handle, 0, binding.id, 0));
  return term.kind === "Axiom" ? { [term.id]: "truncation" } : {};
}

// Read the contexts attached to this exact checked judgement. A source local
// supplies a label/navigation target only when its checked CRef has that ID.
export function checkedContextView(checked, view) {
  const kernel = checked.kernel, references = inspectionContextReferences(checked);
  const entries = view.assumptions.map(assumption => {
    const contextBinding = assumption.names[0];
    const reference = references[assumption.id] ?? { name: contextBinding ?? `c${assumption.id}`, binding: contextBinding };
    references[assumption.id] = reference;
    const type = kernel.tree(kernel.module._wb_view(kernel.handle, 1, assumption.id, 0), { left: 350, maxDepth: 40 });
    // Reuse a certified type already produced for the selected context variable.
    // Other rows show their actual stored type; clicking one certifies its own
    // folded view without eagerly replaying every context's dependency closure.
    const folded = reference.binding === view.name && view.folded?.verified.type && type.id === view.type?.id
      ? { type: view.folded.type, references: view.folded.references,
          contextNames: view.folded.contextNames, contextReferences: view.folded.contextReferences,
          declarations: view.folded.declarations, axiomNotation: view.folded.axiomNotation } : null;
    return { id: assumption.id, ...reference, contextBinding, type, folded };
  });
  return { entries, references };
}

// Source syntax only proposes a folded term. A separate kernel checks every
// constructor, definition alias, and a DefEq witness connecting the proposal
// to the original term. The display reads this kernel's AST, never the plan.
// The original proof engine and exported proof trace remain untouched.
export function checkedFoldedView(checked, binding, { certificate = false, expand = [] } = {}) {
  const output = [...checked.outputs, ...checked.imports, ...(checked.localViews ?? [])].find(o => o.binding === binding);
  if (!output?.mathscript?.foldingPlan) return null;
  const plan = output.mathscript.foldingPlan;
  const names = new Map([...(checked.symbols ?? []), ...checked.imports, ...checked.outputs, ...(checked.localViews ?? [])].map(o => [o.binding, o.name]));
  const b = new Builder(checked.kernel.module, { loadLibrary: false, allowAxioms: checked.allowAxioms,
    optimizations: { normalForms: true, instructions: true } });
  b.serial = 1000000000;
  b.opaque = true;
  try {
    const byName = new Map(checked.kernel.steps.map(step => [step.name, step]));
    const needed = new Set();
    function need(name) {
      const pending = [name];
      while (pending.length) {
        const next = pending.pop();
        if (!next || needed.has(next)) continue;
        const step = byName.get(next);
        if (!step) throw new Error(`Unknown folding premise: ${next}`);
        needed.add(next);
        pending.push(...step.args, ...step.free, step.context);
      }
    }
    function planBindings(node) {
      if (!node || typeof node !== "object") return;
      if (node.binding) need(node.binding);
      for (const value of Object.values(node)) {
        if (Array.isArray(value)) value.forEach(planBindings);
        else if (value && typeof value === "object") planBindings(value);
      }
    }
    need(output.binding); need(output.proposition); planBindings(plan);
    for (const step of checked.kernel.steps) if (needed.has(step.name)) b.k.apply(step);
    const references = {}, aliases = new Map(), aliasWitnesses = new Map(), types = new Map();
    let indexed = 0;
    function typeOf(term) {
      while (indexed < b.k.steps.length) {
        const step = b.k.steps[indexed++], value = b.k.bindings.get(step.name);
        if (value.kind !== "judgement" || b.view(step.name, 4)) continue;
        const sort = b.k.node(b.view(step.name, 1));
        if (["U", "UUOmega", "UUKappa", "UCRef"].includes(sort.kind))
          types.set(b.view(step.name, 0), step.name);
      }
      const found = types.get(b.view(term, 1));
      if (!found) throw new Error("No checked carrier available for folded equality");
      return found;
    }
    function reduceFocused(term) {
      for (let i = 0; i < 100; i++) {
        const next = b.emit("DefBetaReduceGrossKnuth", [term]);
        if (b.view(next, 0) === b.view(term, 0) && b.view(next, 1) === b.view(term, 1)) return next;
        term = next;
      }
      throw new Error("Folding comparison did not converge");
    }
    const normalType = term => b.emit("UnHigh", [reduceFocused(b.emit("HighType", [term]))]);
    function synth(node, scope = new Map()) {
      if (!node) throw new Error("No folding plan for this term");
      if (node.kind === "Name") {
        if (node.local) {
          if (!scope.has(node.name)) throw new Error(`Unbound display variable: ${node.name}`);
          return scope.get(node.name);
        }
        if (node.name === "Nat") return b.emit("NatForm");
        if (node.name === "Unit") return b.emit("UnitForm");
        if (node.name === "Void") return b.emit("VoidForm");
        if (node.name === "tt") return b.emit("UnitIntro");
        if (node.name === "Universe") return b.emit("UIntroOmega");
        if (!node.binding) throw new Error(`No checked definition for ${node.name}`);
        // Open local terms cannot be boxed as closed definitions. Reuse their
        // checked term, preserving its context, and certify the containing type.
        if (b.view(node.binding, 2)) return node.binding;
        if (!aliases.has(node.binding)) {
          const witness = b.emit("Def", [node.binding]);
          const alias = b.emit("DefEqExtL", [witness]);
          aliases.set(node.binding, alias);
          b.boxedDefinitions.add(b.view(alias, 0));
          aliasWitnesses.set(b.view(alias, 0), witness);
          references[b.view(alias, 0)] = { name: names.get(node.binding) ?? node.binding, binding: node.binding };
        }
        return aliases.get(node.binding);
      }
      if (node.kind === "Universe") {
        let U = b.emit("UIntro0");
        for (let i = 0; i < node.level; i++) U = b.emit("UIntro", [U]);
        return U;
      }
      if (node.kind === "Number") {
        let n = b.emit("NatIntroZ");
        for (let i = 0; i < node.value; i++) n = b.emit("NatIntroS", [n]);
        return n;
      }
      if (node.kind === "Induction") {
        const nat = b.emit("NatForm"), z = b.fresh(nat), k = b.fresh(nat);
        const motive = synth(node.type, new Map(scope).set(node.index, z.v));
        const hypothesis = b.fresh(b.subst(motive, z, k.v));
        const base = synth(node.base, scope);
        const step = synth(node.step, new Map(scope).set(node.index, k.v).set(node.hypothesis, hypothesis.v));
        const zero = b.emit("NatIntroZ"), successor = b.emit("NatIntroS", [k.v]);
        return b.emit("NatElim", [motive,
          b.coerceDefinitions(base, b.subst(motive, z, zero)),
          b.coerceDefinitions(step, b.subst(motive, z, successor)),
          normalType(synth(node.value, scope))], [z.c, k.c, hypothesis.c]);
      }
      if (["Pi", "Sigma", "Lambda"].includes(node.kind)) {
        const domain = synth(node.domain, scope);
        // Keep the folded domain in the displayed binder, but retain a checked
        // expanded carrier for later equalities on variables of an aliased type
        // (for example z : Complex(F), whose carrier is Sigma(F, F)).
        b.emit("UnHigh", [reduceFocused(b.emit("HighExp", [domain]))]);
        const x = b.fresh(domain);
        const body = synth(node.body, new Map(scope).set(node.name, x.v));
        return b.emit({ Pi: "PiForm", Sigma: "SigmaForm", Lambda: "PiIntro" }[node.kind], [domain, body], [x.c]);
      }
      if (["Product", "Arrow", "Sum"].includes(node.kind))
        return b.emit({ Product: "SigmaForm", Arrow: "PiForm", Sum: "SumForm" }[node.kind],
          [synth(node.left, scope), synth(node.right, scope)], node.kind === "Sum" ? [] : [null]);
      if (node.kind === "Call") {
        let fn = synth(node.fn, scope);
        for (const arg of node.args) {
          fn = normalType(fn);
          let value = normalType(synth(arg, scope));
          const fnType = b.k.node(b.view(fn, 1));
          if (fnType.kind !== "Pi") throw new Error("Folded application needs a Pi type");
          const expected = b.k.node(fnType.children[0]);
          let actual = b.k.node(b.view(value, 1));
          while (expected.kind === "U" && actual.kind === "U" && actual.parameter < expected.parameter) {
            value = b.emit("UCumul", [value]); actual = b.k.node(b.view(value, 1));
          }
          if (expected.kind === "UUOmega" && ["U", "UCRef"].includes(actual.kind))
            value = b.emit("UCumulOmega", [value]);
          fn = b.emit("PiElim", [fn, value]);
        }
        return fn;
      }
      if (["Equality", "Identity"].includes(node.kind)) {
        let left = synth(node.left, scope), right = synth(node.right, scope);
        const carrier = node.carrier ? synth(node.carrier, scope) : typeOf(left);
        if (node.carrier) {
          const target = b.k.node(b.view(carrier, 0));
          const lift = value => {
            let actual = b.k.node(b.view(value, 1));
            while (target.kind === "U" && actual.kind === "U" && actual.parameter < target.parameter) {
              value = b.emit("UCumul", [value]); actual = b.k.node(b.view(value, 1));
            }
            return value;
          };
          left = lift(left); right = lift(right);
        }
        // Restore the folded carrier by checked type conversion, without
        // unfolding the terms themselves or hiding an unverified annotation.
        if (b.view(left, 1) !== b.view(carrier, 0)) left = b.coerceDefinitions(left, carrier);
        if (b.view(right, 1) !== b.view(carrier, 0)) right = b.coerceDefinitions(right, carrier);
        return b.emit("EqForm", [carrier, left, right]);
      }
      throw new Error(`Unsupported folded constructor: ${node.kind}`);
    }
    function comparison(candidate, original) {
      const direct = aliasWitnesses.get(b.view(candidate, 0));
      if (direct && b.k.node(b.view(direct, 0)).children[1] === b.view(original, 0) && b.view(direct, 1) === b.view(original, 1))
        return { candidate, original, witness: direct };
      const targetSort = b.k.node(b.view(original, 1));
      let sort = b.k.node(b.view(candidate, 1));
      while (targetSort.kind === "U" && sort.kind === "U" && sort.parameter < targetSort.parameter) {
        candidate = b.emit("UCumul", [candidate]); sort = b.k.node(b.view(candidate, 1));
      }
      // Left sides retain the exact input terms; only right sides normalize.
      const witness = term => b.emit("UnHigh", [reduceFocused(b.emit("High1", [b.emit("HighExp", [b.emit("DefEqRefl", [normalType(term)])])]))]);
      const a = witness(candidate), c = witness(original);
      const an = b.k.node(b.view(a, 0)), cn = b.k.node(b.view(c, 0));
      if (an.children[1] !== cn.children[1] || b.view(a, 1) !== b.view(c, 1))
        throw new Error("Folded term is not definitionally equal to the stored term");
      const result = b.emit("UnHigh", [b.emit("HighSubs", [b.emit("High1", [b.emit("HighExp", [a])]), b.emit("DefEqSwp", [c])])]);
      const equation = b.k.node(b.view(result, 0));
      if (equation.kind !== "DefEq" || equation.children[0] !== b.view(candidate, 0) || equation.children[1] !== b.view(original, 0))
        throw new Error("Folding certificate does not connect the requested terms");
      return { candidate, original, witness: result };
    }
    function annotate(tree, hint) {
      if (!tree || tree.truncated || !hint) return tree;
      if (["Pi", "Sigma", "Lambda"].includes(tree.kind) && tree.kind === hint.kind) {
        tree.binderName = hint.name;
        if (tree.kind === "Lambda") annotate(tree.children[0], hint.body);
        else { annotate(tree.children[0], hint.domain); annotate(tree.children[1], hint.body); }
      } else if ((tree.kind === "Sigma" && hint.kind === "Product") || (tree.kind === "Pi" && hint.kind === "Arrow")) {
        tree.binderName = "_";
        annotate(tree.children[0], hint.left); annotate(tree.children[1], hint.right);
      } else if (tree.kind === "Ap" && hint.kind === "Call") {
        annotate(tree.children[0], hint.args.length === 1 ? hint.fn : { ...hint, args: hint.args.slice(0, -1) });
        annotate(tree.children[1], hint.args.at(-1));
      } else if (tree.kind === "Sum" && hint.kind === "Sum") {
        annotate(tree.children[0], hint.left); annotate(tree.children[1], hint.right);
      } else if (tree.kind === "IndNat" && hint.kind === "Induction") {
        tree.binderNames = [hint.index, hint.hypothesis];
        annotate(tree.children[0], hint.base); annotate(tree.children[1], hint.step);
        annotate(tree.children[2], hint.value);
      }
      return tree;
    }
    const result = { references, contextNames: inspectionContextNames(checked, b.k), contextReferences: inspectionContextReferences(checked, b.k), declarations: Object.fromEntries(b.k.declarations), axiomNotation: inspectionAxiomNotation(checked, b.k), verified: {}, expression: null, type: null, failures: {} };
    for (const [side, original] of [["expression", output.binding], ["type", output.proposition]]) {
      try {
        if (side === "type" && b.view(original, 0) !== b.view(output.binding, 1))
          throw new Error("Folding target is not the inspected judgement's stored type");
        const evidence = comparison(synth(plan[side]), original);
        const originalScope = b.k.list(b.view(original, 2)).map(item => item.id);
        const witnessScope = b.k.list(b.view(evidence.witness, 2)).map(item => item.id);
        if (originalScope.length !== witnessScope.length || witnessScope.some(id => !originalScope.includes(id)))
          throw new Error("Folding certificate changes the original assumptions");
        evidence.assumptions = originalScope;
        result.verified[side] = evidence;
        result[side] = annotate(b.k.tree(b.view(evidence.candidate, 0),
          expand.includes(side) ? { left: 65536, maxDepth: 256 } : { left: 350, maxDepth: 40 }), plan[side]);
      } catch (error) { result.failures[side] = error.message; }
    }
    // Exporting an expression should preserve its folded type too. This is a
    // checked type rewrite of the very same term, using the type's certificate.
    if (result.verified.expression && result.verified.type) {
      const candidate = result.verified.expression.candidate;
      const type = result.verified.type;
      if (b.view(candidate, 1) === b.view(type.original, 0)) {
        const retyped = b.emit("UnHigh", [b.emit("HighSubs", [b.emit("HighType", [candidate]), b.emit("DefEqSwp", [type.witness])])]);
        if (b.view(retyped, 0) === b.view(candidate, 0) && b.view(retyped, 1) === b.view(type.candidate, 0))
          result.inspectionBinding = retyped;
      }
    }
    if (certificate) result.certificate = { format: "thth-workbench", version: 1,
      policy: { allowAxioms: checked.allowAxioms }, steps: b.k.steps,
      folding: { binding, verified: result.verified, references, inspectionBinding: result.inspectionBinding } };
    return result;
  } finally { b.k.dispose(); }
}
