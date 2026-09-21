import { CubicalKernel } from "./cubical-kernel.mjs";
import { NativeCubicalElaborator } from "./cubical-elaborator.mjs";
import { Translator } from "./dist/cubical-runtime/translate.mjs";
import { parse } from "./mathscript/parser.mjs";
import { leadingDocumentation } from "./mathscript/documentation.mjs";
import { foldedInspection } from "./cubical-inspection.mjs";
import { cubicalText } from "./cubical-notation.mjs";

// Imports are source, loaded on demand. Every module has its own environment;
// closed native definitions have qualified names so shadowing cannot retarget
// an earlier checked reference. Unsupported declarations never become axioms.
export class CubicalProgram {
  constructor(module, readSource, { onDeclarationStart, onDeclaration, collectReferences = true, optimizations = {} } = {}) {
    this.kernel = new CubicalKernel(module);
    this.kernel.setOptimizations(optimizations);
    this.checker = new NativeCubicalElaborator(this.kernel);
    this.readSource = readSource;
    this.onDeclarationStart = onDeclarationStart; this.onDeclaration = onDeclaration;
    this.collectReferences = collectReferences;
    this.localSymbols = {}; this.declarationBindings = new Map();
    this.modules = new Map(); this.symbols = {}; this.views = new Map();
    this.gaps = []; this.links = []; this.sources = {}; this.completed = 0;
  }
  dispose() { this.kernel.dispose(); }
  assumptionSymbols() {
    return Object.fromEntries([...this.checker.assumptions].map(([binding, type]) => [binding, {
      binding, name: this.checker.assumptionLabels.get(binding) ?? binding, kind: "axiom", role: "explicit axiom",
      verified: true, type: cubicalText(type, this.symbols), axioms: [binding],
      description: "An explicit logical assumption from the library. Its full signature is shown in the checked context.",
    }]));
  }
  async check(source, main = "current", onProgress = () => {}) {
    // Discover the source graph before checking. This only reads/parses source;
    // it does not run the mathematical library or count repeated imports twice.
    const prepared = new Map();
    let total = this.completed;
    const prepare = async (name, text = null) => {
      if (name === "prelude" || this.modules.has(name) || prepared.has(name)) return;
      try {
        text ??= await this.readSource(name);
        const ast = parse(text);
        prepared.set(name, { text, ast });
        total += ast.declarations.length;
        onProgress({ completed: this.completed, total: null, current: name,
          phase: "loading", unit: "declarations", instructions: this.checker.steps });
        for (const dependency of ast.imports) await prepare(dependency);
      } catch (error) { prepared.set(name, { error }); }
    };
    await prepare(main, source);
    const visiting = new Set();
    const load = async (name, text = null) => {
      if (name === "prelude") { const env = new Map(); this.modules.set(name, env); return env; }
      if (visiting.has(name)) throw new Error(`Cyclic source import: ${name}`);
      if (this.modules.has(name)) return this.modules.get(name);
      visiting.add(name);
      let ast;
      try {
        const entry = prepared.get(name);
        if (!entry) throw new Error(`Source was not discovered: ${name}`);
        if (entry.error) throw entry.error;
        ({ text, ast } = entry);
      }
      catch (error) {
        if (name === main) throw error;
        this.gaps.push({ module: name, reason: error.message });
        visiting.delete(name); return new Map();
      }
      this.sources[name] = text;
      let env = new Map();
      for (const dependency of ast.imports) env = new Map([...env, ...await load(dependency)]);
      const define = this.checker.define.bind(this.checker);
      const checker = Object.create(this.checker);
      checker.bindingName = local => `${name}__${local}`;
      checker.define = (local, term, type) => define(`${name}__${local}`, term, type);
      let pending = [];
      const translator = new Translator({ normalize: false, checker,
        onDeclarationStart: declaration => {
          this.onDeclarationStart?.(name, declaration);
          onProgress({ completed: this.completed, total,
          current: `${name}.${declaration.name.text}`, phase: "checking", unit: "declarations", instructions: checker.steps });
        },
        onReference: this.collectReferences ? (node, term, context, dimensions, aliases) => pending.push({ node, term, context, dimensions, aliases, unfoldingHints: [...this.kernel.unfoldingHints] }) : null,
        onDeclaration: (declaration, result) => {
          this.onDeclaration?.(name, declaration, result);
          this.completed++;
          if (result.status === "checked-native-cubical") {
            this.declarationBindings.set(`${name}__${result.name}`, pending.filter(item => item.node.isBinding));
            for (const item of pending) {
              if (!Number.isInteger(item.node.start)) continue;
              let head = item.term; while (head.tag === "App") head = head.fn;
              const source = item.aliases?.find(alias => alias.name === item.node.name && alias.term === item.term);
              const definition = head.tag === "DefRef" && !source;
              const binding = definition ? head.name : `${name}__local_${item.node.start}`;
              if (!definition && !this.views.has(binding)) this.views.set(binding, { ...item, module: name });
              if (!definition) this.localSymbols[binding] = { binding, name: item.node.name,
                role: item.node.role ?? (item.term.tag === "Var" ? "Local assumption" : "Local definition"), verified: true,
                expansion: item.node.expansion, description: item.node.description,
                definitionStart: source?.start ?? item.node.start,
                ...(name === main ? {} : { sourceModule: name, sourceName: declaration.name.text }) };
              if (name === main) this.links.push({ name: item.node.name, binding, start: item.node.start,
                end: item.node.end, definitionStart: source?.start, role: item.node.role ?? (definition ? "definition" : "local"),
                expansion: item.node.expansion, description: item.node.description });
            }
          }
          pending = [];
          onProgress({ completed: this.completed, total,
            current: `${name}.${result.name}`, phase: "checked", unit: "declarations", instructions: checker.steps });
        },
      });
      const result = translator.translate(text, env);
      this.checker.steps = checker.steps;
      const byName = new Map(ast.declarations.map(d => [d.name.text, d]));
      for (const d of result.declarations) {
        const syntax = byName.get(d.name), binding = `${name}__${d.name}`;
        const verified = d.status === "checked-native-cubical";
        const template = d.reason?.startsWith("Universe schema:") ?? false;
        const info = { name: d.name, binding, kind: syntax.kind, role: syntax.kind, verified, template,
          status: d.status, reason: d.reason, unfoldingHints: d.native?.unfoldingHints ?? [], axioms: d.native?.axioms ?? [], start: syntax.start, end: syntax.end,
          definitionStart: syntax.start, description: leadingDocumentation(text, syntax.start)?.text ?? "",
          ...(name === main ? {} : { sourceModule: name, sourceName: d.name }),
          type: verified ? cubicalText(d.type, { ...this.symbols, ...Object.fromEntries(
            (this.declarationBindings.get(binding) ?? []).filter(item => item.term.tag === "Var")
              .map(item => [item.term.name, { name: item.node.name }])) }) : d.reason };
        this.symbols[binding] = info;
        if (!verified && !template) this.gaps.push({ module: name, name: d.name, reason: d.reason });
        if (name === main) this.links.push({ ...info, start: syntax.name.start, end: syntax.name.end });
      }
      this.modules.set(name, result.env); visiting.delete(name);
      return result.env;
    };
    await load(main, source);
    const all = Object.values(this.symbols), outputs = all.filter(d => !d.sourceModule);
    this.main = main;
    return this.metadata = { backend: "cubical", mode: "mathematical", source, outputs,
      imports: all.filter(d => d.sourceModule), symbols: [...all, ...Object.values(this.assumptionSymbols())], assumptionLabels: Object.fromEntries(this.checker.assumptionLabels), declarations: outputs, links: this.links,
      steps: [], declarationCount: total, instructionCount: this.checker.steps, axiomCount: new Set(outputs.flatMap(d => d.axioms)).size, gaps: this.gaps,
      complete: outputs.length > 0 && outputs.every(d => d.verified || d.template), sources: this.sources };
  }
  generatedSymbols() {
    return Object.fromEntries([...this.kernel.definitions.keys()].filter(binding => !this.symbols[binding]).map(binding => [binding, {
      binding, name: binding.replace(/^builtin__(.*?)__(U\d+)$/, "$1[$2]"),
      role: "Derived kernel definition", verified: true,
      description: "An ordinary definition checked by cubical C. Its body is available below; it introduces no axiom.",
    }]));
  }
  inspect(binding, { normalize = false } = {}) {
    const info = this.symbols[binding], local = this.views.get(binding);
    if (info && !info.verified) throw new Error(info.reason);
    let term, expected = null, context = [], dimensions = new Map(), unfoldingHints = [];
    if (local) { term = local.term; context = [...local.context]; dimensions = local.dimensions; unfoldingHints = local.unfoldingHints ?? []; }
    else if (this.checker.assumptions.has(binding)) {
      term = { tag: "Var", name: binding }; expected = this.checker.assumptions.get(binding);
    } else {
      const reference = this.kernel.definitions.get(binding);
      if (!reference) throw new Error("No checked native definition for this name.");
      const definition = this.checker.definitionViews.get(binding);
      term = definition.term; expected = definition.type; unfoldingHints = definition.unfoldingHints;
    }
    const assumptions = this.checker.requiredAssumptions(term, expected, context.map(([, type]) => type));
    context = [...assumptions, ...context];
    const checked = this.kernel.withUnfoldingHints(unfoldingHints, () => this.checker.syntax.check(term, expected, context, dimensions));
    if (normalize) checked.term = this.checker.syntax.decode(this.kernel.normalize(checked.expression), dimensions);
    const bindings = this.declarationBindings.get(binding) ?? [];
    const aliases = (local?.aliases ?? []).map(alias => ({ ...alias, binding: `${local.module}__local_${alias.start}` }));
    const symbols = { ...this.symbols, ...this.localSymbols, ...this.generatedSymbols(), ...this.assumptionSymbols() };
    const variableNames = Object.fromEntries([
      ...bindings.map(item => ({ term: item.term, name: item.node.name, binding: `${info?.sourceModule ?? this.main}__local_${item.node.start}` })),
      ...aliases,
    ].filter(alias => alias.term.tag === "Var").reverse().map(alias => [alias.term.name, { name: alias.name, binding: alias.binding }]));
    for (const [name, value] of Object.entries(variableNames)) symbols[name] = { ...value, local: true };
    const view = { backend: "cubical", name: binding, unfoldingHints, expression: checked.term, type: checked.type,
      expressionText: cubicalText(checked.term, this.symbols), typeText: cubicalText(checked.type, this.symbols),
      dimensions: [...dimensions], context: context.map(([name, type]) => ({ name,
        label: variableNames[name]?.name ?? this.checker.assumptionLabels.get(name) ?? name,
        binding: variableNames[name]?.binding ?? (this.checker.assumptions.has(name) ? name : null), type })), symbols,
      checkingSteps: checked.checkingSteps, reductionSteps: checked.reductionSteps, axioms: [...assumptions.keys()] };
    view.sourceBinding = aliases.find(alias => alias.term === local?.term)?.binding;
    view.folded = foldedInspection(view, aliases);
    view.expressionText = cubicalText(view.folded.expression, symbols);
    view.typeText = cubicalText(view.folded.type, symbols);
    if (local && view.sourceBinding && local.term.tag !== "Var") view.folded.reference = {
      tag: "DisplayRef", name: this.localSymbols[binding]?.name, binding: view.sourceBinding,
    };
    if (info?.kind === "theorem") view.folded.reference = { tag: "DefRef", name: binding };
    view.locals = aliases.filter(alias => alias.term.tag !== "Var" && alias.binding !== binding && alias.binding !== view.sourceBinding)
      .map(({ name, binding }) => ({ name, binding }));
    return view;
  }
  export(binding = null, side = "expression") {
    const view = binding ? this.inspect(binding) : null;
    return { format: "thth-cubical", version: 1, main: this.main,
      source: this.metadata.source, sources: this.sources, binding, side,
      // Syntax is informational. Import must replay the supplied source first.
      ...(view ? { expression: view.expression, type: view.type, context: view.context } : {}) };
  }
}
