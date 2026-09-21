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
    this.sourceAsts = new Map();
    this.templates = new Map();
    this.templateSelections = new Map();
    this.gaps = []; this.links = []; this.sources = {}; this.completed = 0;
  }
  dispose() { this.kernel.dispose(); }
  assumptionSymbols() {
    return Object.fromEntries([...this.checker.assumptions].map(([binding, type]) => [binding, {
      binding, name: this.checker.assumptionLabels.get(binding) ?? binding, kind: "axiom", role: "explicit axiom",
      verified: true, type: cubicalText(type, this.symbols), axioms: [binding],
      description: "An explicit logical assumption from the library. Its full signature is shown in the checked context.",
      specialization: this.checker.assumptionOrigins.get(binding),
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
      this.sourceAsts.set(name, ast);
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
              const definition = head.tag === "DefRef" && !source && !item.node.schemaBinding;
              const binding = definition ? head.name : `${name}__local_${item.node.start}`;
              if (!definition && !this.views.has(binding)) this.views.set(binding, { ...item, module: name });
              if (!definition) this.localSymbols[binding] = { binding, name: item.node.name,
                role: item.node.role ?? (item.term.tag === "Var" ? "Local assumption" : "Local definition"), verified: true,
                expansion: item.node.expansion, description: item.node.description,
                schemaBinding: item.node.schemaBinding,
                universes: item.node.universes,
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
        if (template) {
          const schema = result.env.get(d.name);
          schema.parameterSite = syntax.value?.kind === "lambda" ? syntax.value.name : syntax.params[0].name;
          this.templates.set(binding, schema);
          info.templateParameters = [schema.parameter];
          let body = schema.body;
          while (body.kind === "lambda" && body.domain.kind === "name" && body.domain.name === "Universe") {
            info.templateParameters.push(body.name.text); body = body.body;
          }
          if (name === main && this.collectReferences) {
            const nodes = [], binders = new Set(info.templateParameters);
            const visit = node => {
              if (!node || typeof node !== "object") return;
              if (["let", "obtain"].includes(node.kind)) {
                const bind = pattern => {
                  if (!pattern || typeof pattern !== "object") return;
                  if (pattern.kind === "name") binders.add(pattern.name);
                  Object.values(pattern).forEach(bind);
                };
                bind(node.target);
              }
              if (node.kind === "name") nodes.push(node);
              if (node.name?.text && node !== syntax) {
                binders.add(node.name.text);
                nodes.push({ ...node.name, name: node.name.text });
              }
              Object.values(node).forEach(visit);
            };
            visit(syntax.value ?? syntax);
            const seen = new Set();
            for (const node of nodes) {
              if (!Number.isInteger(node.start) || seen.has(node.start) ||
                !(schema.env.has(node.name) || binders.has(node.name))) continue;
              seen.add(node.start);
              const reference = `${binding}__reference_${node.start}`;
              this.templateSelections.set(reference, { binding, offset: node.start });
              this.links.push({ name: node.name, binding: reference, start: node.start, end: node.end,
                role: "template reference", templateBinding: binding, templateOffset: node.start,
                templateParameters: info.templateParameters, definitionStart: node.start });
            }
          }
        }
        if (!verified && !template) this.gaps.push({ module: name, name: d.name, reason: d.reason });
        if (name === main) this.links.push({ ...info, start: syntax.name.start, end: syntax.name.end });
      }
      this.modules.set(name, result.env); visiting.delete(name);
      return result.env;
    };
    await load(main, source);
    for (const info of Object.values(this.localSymbols)) {
      const schema = this.symbols[info.schemaBinding];
      if (!schema) continue;
      info.definitionStart = schema.definitionStart;
      info.sourceName = schema.name;
      info.sourceModule = schema.sourceModule;
      info.templateBinding = info.schemaBinding;
      info.templateParameters = schema.templateParameters;
      for (const link of this.links) if (link.binding === info.binding) Object.assign(link, {
        sourceName: info.sourceName, sourceModule: info.sourceModule,
        definitionStart: info.definitionStart, description: info.description,
        templateBinding: info.templateBinding, templateParameters: info.templateParameters,
        universes: info.universes,
      });
    }
    const all = Object.values(this.symbols), outputs = all.filter(d => !d.sourceModule);
    this.main = main;
    return this.metadata = { backend: "cubical", mode: "mathematical", source, outputs,
      imports: all.filter(d => d.sourceModule), symbols: [...all, ...Object.values(this.assumptionSymbols())], assumptionLabels: Object.fromEntries(this.checker.assumptionLabels), declarations: outputs, links: this.links,
      steps: [], declarationCount: total, instructionCount: this.checker.steps, axiomCount: new Set(outputs.flatMap(d => d.axioms)).size, gaps: this.gaps,
      complete: outputs.length > 0 && outputs.every(d => d.verified || d.template), sources: this.sources };
  }
  generatedSymbols() {
    const specializations = new Map();
    for (const key of this.checker.schemaSpecializations.keys()) {
      const match = key.match(/^(.*)__((?:U\d+)(?:_U\d+)*)$/), schema = match && this.symbols[match[1]];
      if (schema?.template) specializations.set(key, {
        name: `${schema.name}_${match[2]}`,
        role: "universe specialization", templateBinding: schema.binding,
        templateParameters: schema.templateParameters, universes: match[2].split("_").map(level => Number(level.slice(1))),
        sourceModule: schema.sourceModule, sourceName: schema.name, definitionStart: schema.definitionStart,
      });
    }
    return Object.fromEntries([...this.kernel.definitions.keys()].filter(binding => !this.symbols[binding]).map(binding => [binding, {
      binding, name: binding.replace(/^builtin__(.*?)__(U\d+)$/, "$1[$2]"),
      role: "Derived kernel definition", verified: true,
      description: "An ordinary definition checked by cubical C. Its body is available below; it introduces no axiom.",
      ...specializations.get(binding),
    }]));
  }
  inspect(binding, { normalize = false, universes, offset } = {}) {
    if (this.templateSelections.has(binding)) {
      const selection = this.templateSelections.get(binding);
      return this.inspect(selection.binding, { normalize, universes, offset: selection.offset });
    }
    const info = this.symbols[binding], local = this.views.get(binding);
    if (info?.template) {
      const parameters = info.templateParameters;
      const levels = universes ?? parameters.map(() => 0);
      if (!Array.isArray(levels) || levels.length !== parameters.length ||
        !levels.every(level => Number.isInteger(level) && level >= 0 && level <= 3))
        throw new Error("Select U0, U1, U2, or U3 for each universe parameter.");
      const instance = `${binding}__inspect_${levels.map(level => `U${level}`).join("_")}`;
      if (!this.views.has(instance)) {
        const references = [];
        const translator = new Translator({ normalize: false, checker: this.checker,
          onReference: (node, term, context, dimensions, aliases) => references.push({ node, term, context, dimensions, aliases }) });
        translator.source = this.sources[info.sourceModule ?? this.main];
        const schema = this.templates.get(binding), scope = new Map(schema.env);
        scope.set(schema.parameter, { tag: "U", level: levels[0] });
        references.push({ node: { ...schema.parameterSite, name: schema.parameter, role: "universe argument" },
          term: { tag: "U", level: levels[0] }, context: new Map(), dimensions: new Map(), aliases: [] });
        let body = schema.body;
        for (let i = 1; i < levels.length; i++) {
          references.push({ node: { ...body.name, name: body.name.text, role: "universe argument" },
            term: { tag: "U", level: levels[i] }, context: new Map(), dimensions: new Map(), aliases: [] });
          scope.set(body.name.text, { tag: "U", level: levels[i] }); body = body.body;
        }
        const term = translator.term(body, new Map(), scope, null);
        // Inspection must check even a specialization never used by a proof.
        this.checker.infer(term);
        this.declarationBindings.set(instance, references.filter(item => item.node.isBinding));
        this.views.set(instance, { term, context: new Map(), dimensions: new Map(), aliases: [], referencePrefix: instance,
          module: info.sourceModule ?? this.main, templateInspection: { binding, universes: [...levels] } });
        this.localSymbols[instance] = { binding: instance, name: `${info.name}_${levels.map(level => `U${level}`).join("_")}`,
          role: "universe specialization", verified: true, sourceModule: info.sourceModule,
          sourceName: info.name, definitionStart: info.definitionStart,
          templateBinding: binding, templateParameters: parameters, universes: [...levels] };
        for (const item of references) {
          if (!Number.isInteger(item.node.start)) continue;
          const name = `${instance}__local_${item.node.start}`;
          this.views.set(name, { ...item, module: info.sourceModule ?? this.main, referencePrefix: instance,
            templateInspection: { binding, universes: [...levels], offset: item.node.start } });
          const target = this.symbols[item.node.schemaBinding] ?? (item.term.tag === "DefRef" ? this.symbols[item.term.name] : null);
          this.localSymbols[name] = { binding: name, name: item.node.name,
            role: item.node.role ?? (item.term.tag === "Var" ? "Local assumption" : "Local definition"), verified: true,
            sourceModule: target?.sourceModule ?? info.sourceModule, sourceName: target?.name ?? info.name,
            definitionStart: target?.definitionStart ?? item.node.start,
            templateBinding: binding, templateParameters: parameters, universes: [...levels], templateOffset: item.node.start };
        }
      }
      if (offset !== undefined && !this.views.has(`${instance}__local_${offset}`))
        throw new Error("No checked term is available for this position in the selected specialization.");
      return this.inspect(offset === undefined ? instance : `${instance}__local_${offset}`, { normalize });
    }
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
    const aliases = (local?.aliases ?? []).map(alias => ({ ...alias, binding: `${local.referencePrefix ?? local.module}__local_${alias.start}` }));
    const symbols = { ...this.symbols, ...this.localSymbols, ...this.generatedSymbols(), ...this.assumptionSymbols() };
    const variableNames = Object.fromEntries([
      ...[...(this.checker.schemaSourceNames.get(binding) ?? [])].map(([variable, name]) => ({ term: { tag: "Var", name: variable }, name })),
      ...bindings.map(item => ({ term: item.term, name: item.node.name, binding: `${local?.referencePrefix ?? info?.sourceModule ?? this.main}__local_${item.node.start}` })),
      ...aliases,
    ].filter(alias => alias.term.tag === "Var").reverse().map(alias => [alias.term.name, { name: alias.name, binding: alias.binding }]));
    for (const [name, value] of Object.entries(variableNames)) symbols[name] = { ...value, local: true };
    const view = { backend: "cubical", name: binding, templateInspection: local?.templateInspection,
      unfoldingHints, expression: checked.term, type: checked.type,
      expressionText: cubicalText(checked.term, this.symbols), typeText: cubicalText(checked.type, this.symbols),
      dimensions: [...dimensions], context: context.map(([name, type]) => ({ name,
        label: variableNames[name]?.name ?? this.checker.assumptionLabels.get(name) ?? name,
        binding: variableNames[name]?.binding ?? (this.checker.assumptions.has(name) ? name : null), type })), symbols,
      checkingSteps: checked.checkingSteps, reductionSteps: checked.reductionSteps, axioms: [...assumptions.keys()] };
    // Origin is explanatory metadata, kept separate from checked term syntax.
    // Record only literal calls in parsed source; these links do not claim to
    // represent the kernel's dependency graph or every generic instantiation.
    const origin = this.checker.assumptionOrigins.get(binding);
    if (origin) {
      const mentions = [];
      for (const [module, source] of Object.entries(this.sources)) {
        for (const declaration of this.sourceAsts.get(module).declarations) {
          const seen = new WeakSet();
          const visit = node => {
            if (!node || typeof node !== "object" || seen.has(node)) return;
            seen.add(node);
            if (node.kind === "call" && node.fn?.kind === "name" && node.fn.name === origin.schema
              && node.args.length && source.slice(node.args[0].start, node.args[0].end) === origin.universe) {
              mentions.push({ module, declaration: declaration.name.text,
                expression: source.slice(node.start, node.end),
                universe: source.slice(node.args[0]?.start, node.args[0]?.end) });
              return;
            }
            Object.values(node).forEach(visit);
          };
          visit(declaration);
        }
      }
      view.specialization = { ...origin, binding, mentions };
    }
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
      ...(view ? { expression: view.expression, type: view.type, context: view.context,
        templateInspection: view.templateInspection } : {}) };
  }
}
