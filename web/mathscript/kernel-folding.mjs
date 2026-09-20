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
    policy: { allowAxioms: checked.allowAxioms }, steps: dependencySteps(checked.kernel.steps, [binding]),
    presentation: { names: Object.fromEntries([...(checked.symbols ?? []), ...checked.imports,
      ...checked.outputs, ...(checked.localViews ?? [])].map(o => [o.binding, o.name])) } },
    selection: { name: binding, side } };
  const target = side === "expression" ? result.inspectionBinding ?? evidence.candidate : evidence.candidate;
  const roots = [target, evidence.original, evidence.witness,
    ...(result.certificate.presentation?.contextTypes ?? []).flatMap(row => [row.variable, row.type, row.witness])];
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
  const label = document.presentation.names[binding] ?? binding;
  document.presentation.names[name] = side === "expression" ? label : `${label} (type)`;
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
const contextFoldingCache = new WeakMap();
export function checkedContextView(checked, view) {
  const kernel = checked.kernel, references = inspectionContextReferences(checked);
  let cache = contextFoldingCache.get(checked);
  if (!cache) contextFoldingCache.set(checked, cache = new Map());
  const entries = view.assumptions.map(assumption => {
    const contextBinding = assumption.names[0];
    const reference = references[assumption.id] ?? { name: contextBinding ?? `c${assumption.id}`, binding: contextBinding };
    references[assumption.id] = reference;
    const type = kernel.tree(kernel.module._wb_view(kernel.handle, 1, assumption.id, 0), { left: 350, maxDepth: 40 });
    // Every row uses a certificate for its own exact checked type, including
    // assumptions other than the selected variable. Keep a bounded cache for
    // this immutable compilation so navigating within a context is inexpensive.
    const binding = kernel.bindings.get(reference.binding);
    const sameType = binding?.kind === "judgement"
      && kernel.module._wb_view(kernel.handle, 0, binding.id, 1) === type.id;
    let folded = null;
    if (sameType) {
      if (!cache.has(reference.binding)) {
        const proposal = reference.binding === view.name && view.folded
          ? view.folded : checkedFoldedView(checked, reference.binding);
        const verified = proposal?.verified.type ? {
          type: proposal.type, references: proposal.references,
          contextNames: proposal.contextNames, contextReferences: proposal.contextReferences,
          declarations: proposal.declarations, axiomNotation: proposal.axiomNotation,
        } : null;
        if (cache.size >= 128) cache.delete(cache.keys().next().value);
        cache.set(reference.binding, verified);
      }
      folded = cache.get(reference.binding);
    }
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
      if (node.typeBinding) need(node.typeBinding);
      if (node.inferredTypeBinding) need(node.inferredTypeBinding);
      if (node.context) need(node.context);
      for (const value of Object.values(node)) {
        if (Array.isArray(value)) value.forEach(planBindings);
        else if (value && typeof value === "object") planBindings(value);
      }
    }
    need(output.binding); need(output.proposition); planBindings(plan);
    const contextLocals = [];
    if (certificate) {
      const scope = new Set(checked.kernel.inspect(output.binding).assumptions.map(a => a.id));
      for (const local of checked.localViews ?? []) {
        const value = checked.kernel.bindings.get(local.binding);
        if (value?.kind !== "judgement") continue;
        const term = checked.kernel.node(checked.kernel.module._wb_view(checked.kernel.handle, 0, value.id, 0));
        if (["CRef", "UCRef"].includes(term.kind) && scope.has(term.parameter)) {
          contextLocals.push(local); need(local.binding); need(local.proposition);
          planBindings(local.mathscript?.foldingPlan?.type);
        }
      }
    }
    for (const step of checked.kernel.steps) if (needed.has(step.name)) b.k.apply(step);
    const references = {}, aliases = new Map(), aliasWitnesses = new Map(), types = new Map(), terms = new Map();
    let indexed = 0;
    function indexTerms() {
      while (indexed < b.k.steps.length) {
        const step = b.k.steps[indexed++], value = b.k.bindings.get(step.name);
        if (value.kind !== "judgement" || b.view(step.name, 4)) continue;
        const termId = b.view(step.name, 0), previousTerm = terms.get(termId);
        if (!previousTerm || b.k.list(b.view(step.name, 2), true).length < b.k.list(b.view(previousTerm, 2), true).length)
          terms.set(termId, step.name);
        const sort = b.k.node(b.view(step.name, 1));
        if (["U", "UUOmega", "UUKappa", "UCRef"].includes(sort.kind))
          {
            const id = b.view(step.name, 0), previous = types.get(id);
            // Equal type expressions may have derivations carrying unrelated
            // assumptions. Prefer the smallest context, never the latest one.
            if (!previous || b.k.list(b.view(step.name, 2), true).length < b.k.list(b.view(previous, 2), true).length)
              types.set(id, step.name);
          }
      }
    }
    function termAt(id) {
      indexTerms();
      const term = terms.get(id);
      if (!term) throw new Error("No checked term available for an implicit argument");
      return term;
    }
    function typeOf(term) {
      indexTerms();
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
    function application(fn, args) {
      for (let value of args) {
        fn = normalType(fn); value = normalType(value);
        const fnType = b.k.node(b.view(fn, 1));
        if (fnType.kind !== "Pi") throw new Error("Folded application needs a Pi type");
        const expected = b.k.node(fnType.children[0]);
        let actual = b.k.node(b.view(value, 1));
        while (expected.kind === "U" && actual.kind === "U" && actual.parameter < expected.parameter) {
          value = b.emit("UCumul", [value]); actual = b.k.node(b.view(value, 1));
        }
        if (expected.kind === "UUOmega" && ["U", "UCRef"].includes(actual.kind)) value = b.emit("UCumulOmega", [value]);
        fn = b.emit("PiElim", [fn, value]);
      }
      return fn;
    }
    // Unbox only aliases introduced for this display. Expanding the original
    // theorem references can expose enormous proof bodies and is unnecessary:
    // both sides already share those same checked references.
    function reduceDisplayAliases(term) {
      const findAlias = (id, seen = new Set()) => {
        if (aliasWitnesses.has(id)) return [];
        if (seen.has(id)) return null;
        seen.add(id);
        const node = b.k.node(id);
        for (let i = 0; i < node.children.length; i++) {
          const path = findAlias(node.children[i], seen);
          if (path) return [i, ...path];
        }
        return null;
      };
      for (let i = 0; i < 4096; i++) {
        term = b.emit("High1", [b.emit("HighExp", [term])]);
        const next = b.emit("BetaReduceGrossKnuth", [term]);
        if (b.view(next, 0) !== b.view(term, 0)) { term = next; continue; }
        const right = b.k.node(b.view(next, 0)).children[1];
        const path = findAlias(right);
        if (!path) return b.emit("UnHigh", [next]);
        term = next;
        for (const child of path) term = b.emit(`High${child}`, [term]);
        term = b.emit("DefReducePointed", [term]);
      }
      throw new Error("Display alias comparison did not converge");
    }
    function coerce(term, type) {
      if (b.view(term, 1) === b.view(type, 0)) return term;
      try { return b.boxedDefinitions.size ? b.coerceDefinitions(term, type) : b.coerce(term, type); }
      catch (error) {
        if (error.message !== "Conversion types differ") throw error;
        // Application types may already have unfolded an original helper,
        // while the proposed carrier retains it below a display alias.
        // Normalize both types to the same depth, leaving the proof expression
        // untouched, then restore the requested carrier by a checked witness.
        const converted = normalType(term);
        const witness = b.emit("UnHigh", [reduceFocused(b.emit("High1", [
          b.emit("HighExp", [b.emit("DefEqRefl", [type])]),
        ]))]);
        const equation = b.k.node(b.view(witness, 0));
        if (equation.kind !== "DefEq" || b.view(converted, 1) !== equation.children[1]) throw error;
        return b.emit("UnHigh", [b.emit("HighSubs", [
          b.emit("HighType", [converted]), b.emit("DefEqSwp", [witness]),
        ])]);
      }
    }
    function synth(node, scope = new Map()) {
      if (!node) throw new Error("No folding plan for this term");
      if (node.kind === "Checked") {
        const parameters = node.parameters ?? [];
        const close = (term, bound) => {
          for (const p of [...bound].reverse()) term = b.emit("PiIntro", [p.typeBinding, term], [p.context]);
          return term;
        };
        let term = close(node.binding, parameters);
        const arguments_ = [];
        for (const p of parameters) {
          if (!scope.has(p.name)) throw new Error(`Unbound checked template variable: ${p.name}`);
          let domain = close(p.typeBinding, parameters.slice(0, arguments_.length));
          for (const arg of arguments_) domain = b.norm(b.emit("PiElim", [normalType(domain), normalType(arg)]));
          const value = b.view(scope.get(p.name), 1) === b.view(domain, 0)
            ? scope.get(p.name) : coerce(scope.get(p.name), domain);
          arguments_.push(value);
          term = b.emit("PiElim", [normalType(term), normalType(value)]);
        }
        return b.norm(term);
      }
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
        if (b.view(node.binding, 2)) {
          if (node.expansion) {
            try {
              const candidate = synth(node.expansion, scope);
              comparison(candidate, node.binding);
              return candidate;
            } catch { /* The original checked local term is always available. */ }
          }
          return node.binding;
        }
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
          coerce(base, b.subst(motive, z, zero)),
          coerce(step, b.subst(motive, z, successor)),
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
        return b.emit({ Pi: "PiForm", Sigma: "SigmaForm", Lambda: "PiIntro" }[node.kind], [normalType(domain), normalType(body)], [x.c]);
      }
      if (["Product", "Arrow", "Sum"].includes(node.kind))
        return b.emit({ Product: "SigmaForm", Arrow: "PiForm", Sum: "SumForm" }[node.kind],
          [normalType(synth(node.left, scope)), normalType(synth(node.right, scope))], node.kind === "Sum" ? [] : [null]);
      if (node.kind === "Call") {
        // refl is a language constructor, not a named library definition.
        // Build its actual kernel node while retaining the folded endpoint.
        if (node.fn.kind === "Name" && node.fn.name === "refl") {
          if (node.args.length !== 1) throw new Error("Folded refl needs one endpoint");
          return b.emit("EqIntro", [synth(node.args[0], scope)]);
        }
        const primitive = node.fn.kind === "Name" && {
          succ: ["NatIntroS", 1],
          Suspension: ["SuspForm", 1], north: ["SuspNorth", 1], south: ["SuspSouth", 1],
          meridian: ["SuspMerid", 2], apd: ["Apd", 4],
        }[node.fn.name];
        if (primitive) {
          if (node.args.length !== primitive[1]) throw new Error(`Wrong arity for folded ${node.fn.name}`);
          const args = node.args.map(arg => normalType(synth(arg, scope)));
          if (node.fn.name === "meridian") args[1] = coerce(args[1], args[0]);
          if (node.fn.name === "apd") args[3] = coerce(args[3], b.emit("EqForm", [typeOf(args[1]), args[1], args[2]]));
          return b.emit(primitive[0], args);
        }
        if (node.fn.kind === "Name" && node.fn.name === "Eq") {
          if (node.args.length !== 3) throw new Error("Folded Eq needs a carrier and two endpoints");
          return synth({ kind: "Identity", carrier: node.args[0], left: node.args[1], right: node.args[2] }, scope);
        }
        if (node.fn.kind === "Name" && node.fn.name === "transport") {
          if (node.args.length !== 5) throw new Error("Folded transport needs five arguments");
          const [family, from, to, path, value] = node.args.map(arg => normalType(synth(arg, scope)));
          const atFrom = b.emit("PiElim", [family, from]);
          const equality = b.emit("EqForm", [typeOf(from), from, to]);
          return b.emit("Transport", [family, from, to,
            coerce(path, equality), coerce(value, atFrom)]);
        }
        const principle = node.fn.kind === "Name" && {
          Truncate: "lib_Trunc", TruncateIntro: "lib_trunc_intro", TruncateProp: "lib_trunc_is_trunc",
          TruncateElim: "lib_trunc_elim", FunExt: "lib_funext", Univalence: "lib_univalence", ua: "lib_ua", idtoequiv: "lib_AreEquiv",
          UnivalenceBeta: "lib_ua_elim", UnivalenceEta: "lib_ua_unique",
        }[node.fn.name];
        if (principle) return application(principle, node.args.map(arg => synth(arg, scope)));
        if (node.fn.kind === "Name" && ["sym", "trans", "cong"].includes(node.fn.name)) {
          const name = node.fn.name, args = node.args.map(arg => synth(arg, scope));
          const path = normalType(args[name === "cong" ? 1 : 0]);
          const equality = b.k.node(b.view(path, 1));
          if (equality.kind !== "Eq") throw new Error("Folded path operation needs an identity type");
          const [A, x, y] = equality.children.map(termAt), U = typeOf(A);
          const operation = { sym: "inverse", trans: "concatenate", cong: "ap" }[name];
          const fn = synth({ kind: "Name", name: operation, binding: operation }, scope);
          if (name === "sym") return application(fn, [U, A, x, y, path]);
          if (name === "trans") {
            const other = normalType(args[1]), type = b.k.node(b.view(other, 1));
            if (type.kind !== "Eq") throw new Error("Folded concatenation needs two paths");
            return application(fn, [U, A, x, y, termAt(type.children[2]), path, other]);
          }
          const B = typeOf(normalType(application(args[0], [x])));
          return application(fn, [U, A, B, args[0], x, y, path]);
        }
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
        let left = normalType(synth(node.left, scope)), right = normalType(synth(node.right, scope));
        let carrier = node.carrier ? synth(node.carrier, scope) : typeOf(left);
        // An inferred carrier may spell projections of a record even when the
        // kernel has computed them to named context variables. Refold that
        // checked carrier and use it only after certifying the same type.
        try {
          const compact = foldKnownDefinitions(typeOf(left));
          if (b.k.node(b.view(compact, 0)).size < b.k.node(b.view(carrier, 0)).size) {
            comparison(compact, carrier);
            carrier = compact;
          }
        } catch { /* Keep the source proposal when no smaller certificate exists. */ }
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
        if (b.view(left, 1) !== b.view(carrier, 0)) left = coerce(left, carrier);
        if (b.view(right, 1) !== b.view(carrier, 0)) right = coerce(right, carrier);
        return b.emit("EqForm", [carrier, left, right]);
      }
      throw new Error(`Unsupported folded constructor: ${node.kind}`);
    }
    function comparison(candidate, original, openDefinition = false) {
      if (b.view(candidate, 0) === b.view(original, 0) && b.view(candidate, 1) === b.view(original, 1))
        return { candidate, original, witness: b.emit("DefEqRefl", [candidate]) };
      const direct = aliasWitnesses.get(b.view(candidate, 0));
      if (direct && b.k.node(b.view(direct, 0)).children[1] === b.view(original, 0) && b.view(direct, 1) === b.view(original, 1))
        return { candidate, original, witness: direct };
      const targetSort = b.k.node(b.view(original, 1));
      let sort = b.k.node(b.view(candidate, 1));
      while (targetSort.kind === "U" && sort.kind === "U" && sort.parameter < targetSort.parameter) {
        candidate = b.emit("UCumul", [candidate]); sort = b.k.node(b.view(candidate, 1));
      }
      // Left sides retain the exact input terms; only right sides normalize.
      const witness = (term, open) => {
        let equation = b.emit("DefEqRefl", [normalType(term)]);
        if (open && b.k.node(b.view(term, 0)).kind === "DRef") {
          // Inspecting an opaque definition's own body may open that one
          // definition. Its nested named references stay boxed as usual.
          equation = b.emit("UnHigh", [b.emit("DefReducePointed", [
            b.emit("High1", [b.emit("HighExp", [equation])]),
          ])]);
        }
        return reduceDisplayAliases(equation);
      };
      const a = witness(candidate, false), c = witness(original, openDefinition);
      const an = b.k.node(b.view(a, 0)), cn = b.k.node(b.view(c, 0));
      if (an.children[1] !== cn.children[1] || b.view(a, 1) !== b.view(c, 1))
        throw new Error("Folded term is not definitionally equal to the stored term");
      const result = b.emit("UnHigh", [b.emit("HighSubs", [b.emit("High1", [b.emit("HighExp", [a])]), b.emit("DefEqSwp", [c])])]);
      const equation = b.k.node(b.view(result, 0));
      if (equation.kind !== "DefEq" || equation.children[0] !== b.view(candidate, 0) || equation.children[1] !== b.view(original, 0))
        throw new Error("Folding certificate does not connect the requested terms");
      return { candidate, original, witness: result };
    }
    function foldKnownDefinitions(term) {
      const candidates = new Map();
      const refs = new Map((plan.sourceReferences ?? []).map(ref => [ref.binding, ref]));
      function referenced(node) {
        if (!node || typeof node !== "object") return;
        if (node.kind === "Name" && node.binding) refs.set(node.binding, node);
        for (const value of Object.values(node)) {
          if (Array.isArray(value)) value.forEach(referenced);
          else if (value && typeof value === "object") referenced(value);
        }
      }
      referenced(plan);
      for (const ref of refs.values()) {
        if (!ref.binding || b.view(ref.binding, 2)) continue;
        const body = b.view(ref.binding, 0), tree = b.k.node(body);
        if (tree.size <= 1 || candidates.has(body)) continue;
        const alias = synth({ kind: "Name", ...ref });
        candidates.set(body, { alias, witness: aliasWitnesses.get(b.view(alias, 0)) });
      }
      function find(id, seen = new Set()) {
        if (candidates.has(id)) return { path: [], ...candidates.get(id) };
        if (seen.has(id)) return null;
        seen.add(id);
        const node = b.k.node(id);
        for (let i = 0; i < node.children.length; i++) {
          const result = find(node.children[i], seen);
          if (result) return { ...result, path: [i, ...result.path] };
        }
        return null;
      }
      for (let i = 0; i < 4096; i++) {
        const match = find(b.view(term, 0));
        if (!match) return term;
        term = b.emit("HighExp", [term]);
        for (const child of match.path) term = b.emit(`High${child}`, [term]);
        term = b.emit("UnHigh", [b.emit("HighSubs", [term, b.emit("DefEqSwp", [match.witness])])]);
      }
      throw new Error("Structural folding did not converge");
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
        let candidate;
        try { candidate = synth(plan[side]); }
        catch (error) {
          if (side !== "type" || !plan.inferredTypeBinding) throw error;
          candidate = foldKnownDefinitions(plan.inferredTypeBinding);
        }
        let evidence;
        try { evidence = comparison(candidate, original, side === "expression" && b.k.node(b.view(candidate, 0)).kind !== "DRef"); }
        catch (error) {
          if (side !== "type" || !plan.inferredTypeBinding) throw error;
          evidence = comparison(foldKnownDefinitions(plan.inferredTypeBinding), original);
        }
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
    if (certificate) {
      const contextTypes = [];
      for (const local of contextLocals) {
        try {
          const evidence = comparison(synth(local.mathscript.foldingPlan.type), local.proposition);
          contextTypes.push({ variable: local.binding, type: evidence.candidate, witness: evidence.witness });
        } catch { /* Context rows can always show their stored checked type. */ }
      }
      const labels = Object.fromEntries([...names].filter(([name]) => b.k.bindings.has(name)));
      const axiomNames = { lib_Trunc: "Truncate", lib_trunc_intro: "TruncateIntro",
        lib_trunc_is_trunc: "TruncateProp", lib_trunc_elim: "TruncateElim", lib_funext: "FunExt",
        lib_univalence: "Univalence", lib_choice: "Choice", lib_lem: "LEM" };
      for (const name of checked.preludeAxioms ?? []) if (axiomNames[name]) labels[name] = axiomNames[name];
      for (const [original, alias] of aliases) labels[alias] = names.get(original) ?? original;
      result.certificate = { format: "thth-workbench", version: 1,
        policy: { allowAxioms: checked.allowAxioms }, steps: b.k.steps,
        presentation: { names: labels, contextTypes },
        folding: { binding, verified: result.verified, references, inspectionBinding: result.inspectionBinding } };
    }
    return result;
  } finally { b.k.dispose(); }
}
