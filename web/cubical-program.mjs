import { sourceStatement } from "./cubical-statement.mjs";
import { CubicalKernel } from "./cubical-kernel.mjs";
import { NativeCubicalElaborator } from "./cubical-elaborator.mjs";
import { Translator } from "./dist/cubical-runtime/translate.mjs";
import { Scope } from "./dist/cubical-runtime/elaboration.mjs";
import {emptySimpRegistry,mergeSimpRegistries} from "./dist/cubical-runtime/simp-registry.mjs";
import { parse } from "./mathscript/parser.mjs";
import { leadingDocumentation } from "./mathscript/documentation.mjs";
import { foldedInspection } from "./cubical-inspection.mjs";
import { cubicalText, cubicalTextParts, cubicalMathTree } from "./cubical-notation.mjs";
import { checkReduction, simplifyTypeApplications } from "./cubical-reduction.mjs";
import { CubicalDeclarationTransaction } from "./cubical-transaction.mjs";

const expansionSuffix = (role,index) => index ? `_${role.replaceAll(" ","_")}_${index}` : "";

// Imports are source, loaded on demand. Every module has its own environment;
// closed native definitions have qualified names so shadowing cannot retarget
// an earlier checked reference. Unsupported declarations never become axioms.
export class CubicalProgram {
  constructor(module, readSource, { onDeclarationStart, onDeclaration, collectReferences = true, optimizations = {}, manageTransactions = true } = {}) {
    this.kernel = new CubicalKernel(module);
    this.kernel.setOptimizations(optimizations);
    this.checker = new NativeCubicalElaborator(this.kernel);
    this.readSource = readSource;
    this.onDeclarationStart = onDeclarationStart; this.onDeclaration = onDeclaration;
    this.collectReferences = collectReferences;
    this.manageTransactions = manageTransactions;
    this.localSymbols = {}; this.declarationBindings = new Map();
    this.declarationReferences = new Map();
    this.modules = new Map(); this.symbols = {}; this.views = new Map();
    this.sourceAsts = new Map();
    this.simpRegistries = new Map();
    this.templates = new Map();
    this.templateSelections = new Map();
    this.gaps = []; this.evaluations = []; this.links = []; this.sources = {}; this.completed = 0;
  }
  dispose() { this.kernel.dispose(); }
  assumptionSymbols() {
    return Object.fromEntries([...this.checker.assumptions].map(([binding, type]) => [binding, {
      binding, name: this.checker.assumptionLabels.get(binding) ?? binding, kind: "axiom", role: "explicit axiom",
      verified: true, type: cubicalText(type, this.symbols), axioms: [binding],
      description: "An explicit logical assumption from the library. Its full signature is shown in the Axioms section.",
      specialization: this.checker.assumptionOrigins.get(binding),
    }]));
  }
  async check(source, main = "current", onProgress = () => {}) {
    // Discover the source graph before checking. This only reads/parses source;
    // it does not run the mathematical library or count repeated imports twice.
    const prepared = new Map();
    let total = this.completed;
    const prepare = async (name, text = null) => {
      if (this.modules.has(name) || prepared.has(name)) return;
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
      let env = new Map(),simpRegistry=emptySimpRegistry();
      for (const dependency of ast.imports) {
        env = new Map([...env, ...await load(dependency)]);
        simpRegistry=mergeSimpRegistries(simpRegistry,this.simpRegistries.get(dependency));
      }
      const define = this.checker.define.bind(this.checker);
      const checker = Object.create(this.checker);
      checker.bindingName = local => `${name}__${local}`;
      checker.define = (local, term, type) => define(`${name}__${local}`, term, type);
      let pending = [];
      let transaction = null;
      const translator = new Translator({ normalize: false, checker,simpRegistry,moduleName:name,
        onDeclarationStart: declaration => {
          if (this.manageTransactions) transaction = new CubicalDeclarationTransaction(this.kernel,this.checker);
          try {
            this.onDeclarationStart?.(name, declaration, checker);
            onProgress({ completed: this.completed, total,
              current: `${name}.${declaration.name.text}`, phase: "checking", unit: "declarations", instructions: checker.steps });
          } catch(error) {
            transaction?.finish(false);
            transaction=null;
            throw error;
          }
        },
        onReference: this.collectReferences ? (node, term, context, dimensions, aliases) => pending.push({ node, term, context, dimensions, aliases, unfoldingHints: [...this.kernel.unfoldingHints] }) : null,
        onDeclaration: (declaration, result) => {
          try {this.onDeclaration?.(name, declaration, result, checker);}
          catch(error) {
            transaction?.finish(false);
            transaction=null;
            throw error;
          }
          if (transaction) {
            transaction.finish(result.status === "checked-native-cubical");
            transaction = null;
          }
          this.completed++;
          if (result.status === "checked-native-cubical") {
            this.declarationBindings.set(`${name}__${result.name}`, pending.filter(item => item.node.isBinding));
            const references = [];
            const declarationLinks = [];
            this.declarationReferences.set(`${name}__${result.name}`, references);
            for (const item of pending) {
              if (!Number.isInteger(item.node.start)) continue;
              let head = item.term; while (head.tag === "App") head = head.fn;
              const source = item.aliases?.find(alias => alias.name === item.node.name && alias.term === item.term);
              const definition = head.tag === "DefRef" && !source && !item.node.schemaBinding && !item.node.expressionSite;
              const binding = definition ? head.name : `${name}__local_${item.node.start}${
                expansionSuffix(item.node.role,item.node.expansionIndex)}`;
              references.push({ start: item.node.start, binding });
              if (!definition && !this.views.has(binding)) this.views.set(binding, { ...item, module: name });
              if (!definition) this.localSymbols[binding] = { binding, name: item.node.name,
                role: item.node.role ?? (item.term.tag === "Var" ? "Local assumption" : "Local definition"), verified: true,
                expansion: item.node.expansion, description: item.node.description,
                schemaBinding: item.node.schemaBinding,
                universes: item.node.universes,
                definitionStart: source?.start ?? item.node.start,
                ...(name === main ? {} : { sourceModule: name, sourceName: declaration.name.text }) };
              if (name === main) {
                const link={ name: item.node.name, binding, start: item.node.start,
                end: item.node.end, definitionStart: source?.start, role: item.node.role ?? (definition ? "definition" : "local"),
                expansion: item.node.expansion, description: item.node.description,
                freeze:item.node.freeze,traceParent:item.node.traceParent };
                this.links.push(link);declarationLinks.push(link);
              }
            }
            for(const link of declarationLinks)if(link.role==="simplification witness")
              link.rewriteSteps=declarationLinks.filter(step=>step.role==="simplification step"
                &&step.traceParent===link.start).map(step=>({name:step.name,binding:step.binding,
                  role:step.role,description:step.description,start:step.start,end:step.end}));
          }
          pending = [];
          onProgress({ completed: this.completed, total,
            current: `${name}.${result.name}`, phase: "checked", unit: "declarations", instructions: checker.steps });
        },
      });
      const result = translator.translate(text, env);
      this.simpRegistries.set(name,result.simpRegistry);
      for(const directive of result.directives??[]) {
        if(directive.status!=="checked")
          this.gaps.push({module:name,name:`${directive.kind} ${directive.name}`,
            reason:directive.reason,directive:true});
        else if(directive.kind==="evaluate")
          this.evaluations.push({module:name,name:directive.name,value:directive.normalText});
      }
      this.checker.steps = checker.steps;
      const byName = new Map(ast.declarations.map(d => [d.name.text, d]));
      for (const d of result.declarations) {
        const syntax = byName.get(d.name), binding = `${name}__${d.name}`;
        const verified = d.status === "checked-native-cubical";
        const template = !!d.template;
        const info = { name: d.name, binding, kind: syntax.kind, role: syntax.kind, verified, template,
          status: d.status, reason: d.reason, errorStart: d.errorStart, errorEnd: d.errorEnd,
          rewriteWork: d.rewriteWork,
          unfoldingHints: d.native?.unfoldingHints ?? [], axioms: d.native?.axioms ?? [], start: syntax.start, end: syntax.end,
          definitionStart: syntax.start, description: leadingDocumentation(text, syntax.start)?.text ?? "",
          ...(name === main ? {} : { sourceModule: name, sourceName: d.name }),
          type: verified ? cubicalText(d.type, { ...this.symbols, ...Object.fromEntries(
            (this.declarationBindings.get(binding) ?? []).filter(item => item.term.tag === "Var")
              .map(item => [item.term.name, { name: item.node.name }])) }) : d.reason };
        this.symbols[binding] = info;
        if (template) {
          const schema = result.env.get(d.name);
          schema.parameterSite = syntax.value?.kind === "lambda" ? syntax.value.name
            : syntax.value?.kind === "binderGroup" ? syntax.value.names[0]
            : syntax.params[0].name;
          this.templates.set(binding, schema);
          info.templateParameters = [schema.parameter];
          let body = schema.body;
          while (body?.kind === "lambda" && body.domain?.kind === "name" && body.domain.name === "Universe") {
            info.templateParameters.push(body.name.text); body = body.body;
          }
          if (name === main && this.collectReferences) {
            const nodes = [], binders = new Set(info.templateParameters);
            const visit = node => {
              if (!node || typeof node !== "object") return;
              const tactic = {calc:"calculation witness",rw:"rewrite witness",
                simp:"simplification witness",simpOnly:"simplification witness",
                simpa:"simplification witness",simpaOnly:"simplification witness"}[node.kind];
              if (tactic) {
                const keyword = node.kind.replace("Only","");
                nodes.push({name:keyword,start:node.start,end:node.start+keyword.length,
                  selectionOffset:node.start,role:tactic});
                // The same `by` site as the elaborator's step reference.
                if (node.kind === "calc") node.steps.forEach((step,index) => {
                  nodes.push({name:`calc step ${index+1}`,start:step.by.start,end:step.by.end,
                    selectionOffset:step.by.start,role:"calculation step",
                    expansion:{role:"calculation step",index:index+1}});
                });
              }
              if (["let", "obtain"].includes(node.kind)) {
                const bind = pattern => {
                  if (!pattern || typeof pattern !== "object") return;
                  if (pattern.kind === "name") binders.add(pattern.name);
                  Object.values(pattern).forEach(bind);
                };
                bind(node.target);
              }
              if (node.kind === "name") nodes.push(node);
              if (node.kind === "binderGroup") for (const name of node.names) {
                binders.add(name.text);
                nodes.push({ ...name, name: name.text });
              }
              // Proof tactics bind names outside the ordinary lambda/name fields.
              for (const name of [node.kind === "ext" ? node.variable : null,
                node.kind === "simpOnly" ? node.as : null]) if (name?.text) {
                binders.add(name.text);
                nodes.push({ ...name, name: name.text });
              }
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
                !(node.role || schema.env.has(node.name) || binders.has(node.name))) continue;
              seen.add(node.start);
              const reference = `${binding}__reference_${node.start}`;
              const selectedOffset = node.selectionOffset ?? node.start;
              this.templateSelections.set(reference, { binding, offset: selectedOffset,
                expansion:node.expansion });
              this.links.push({ name: node.name, binding: reference, start: node.start, end: node.end,
                role: node.role ?? "template reference", templateBinding: binding,
                templateOffset: selectedOffset, ...(node.expansion ? {templateExpansion:node.expansion} : {}),
                templateParameters: info.templateParameters, definitionStart: node.start });
            }
          }
        }
        if (!verified && !template) this.gaps.push({ module: name, name: d.name,
          reason: d.reason, start: d.errorStart, end: d.errorEnd });
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
      evaluations: this.evaluations,
      complete: outputs.length > 0 && outputs.every(d => d.verified || d.template)
        && !this.gaps.some(gap=>gap.directive), sources: this.sources };
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
  inspect(binding, { normalize = false, universes, offset, expansion } = {}) {
    if (this.templateSelections.has(binding)) {
      const selection = this.templateSelections.get(binding);
      return this.inspect(selection.binding, { normalize, universes, offset: selection.offset,
        expansion:selection.expansion });
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
        const schema = this.templates.get(binding);
        // A template edit is never offered (see freeze:null below), so skip
        // the simplification replays that would compute one.
        const translator = new Translator({ normalize: false, checker: this.checker,
          simpRegistry:schema.simpRegistry,moduleName:schema.moduleName,freezeSuggestions:false,
          onReference: (node, term, context, dimensions, aliases) => references.push({ node, term, context, dimensions, aliases }) });
        const scope = new Map(schema.env);
        scope.set(schema.parameter, { tag: "U", level: levels[0] });
        references.push({ node: { ...schema.parameterSite, name: schema.parameter, role: "universe argument" },
          term: { tag: "U", level: levels[0] }, context: new Map(), dimensions: new Map(), aliases: [] });
        let body = schema.body;
        for (let i = 1; i < levels.length; i++) {
          references.push({ node: { ...body.name, name: body.name.text, role: "universe argument" },
            term: { tag: "U", level: levels[i] }, context: new Map(), dimensions: new Map(), aliases: [] });
          scope.set(body.name.text, { tag: "U", level: levels[i] }); body = body.body;
        }
        const unit = translator.unit({ source: this.sources[info.sourceModule ?? this.main] });
        const term = translator.term(body, new Scope(unit, new Map(), scope), null);
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
          const name = `${instance}__local_${item.node.start}${expansionSuffix(item.node.role,item.node.expansionIndex)}`;
          const expansion=item.node.expansionIndex
            ? {role:item.node.role,index:item.node.expansionIndex} : undefined;
          this.views.set(name, { ...item, module: info.sourceModule ?? this.main, referencePrefix: instance,
            templateInspection: { binding, universes: [...levels], offset: item.node.start,
              ...(expansion ? { expansion } : {}) } });
          const target = this.symbols[item.node.schemaBinding] ?? (item.term.tag === "DefRef" ? this.symbols[item.term.name] : null);
          this.localSymbols[name] = { binding: name, name: item.node.name,
            role: item.node.role ?? (item.term.tag === "Var" ? "Local assumption" : "Local definition"), verified: true,
            // A template edit changes every universe specialization. Its
            // witness here was checked only at the selected level, so it
            // cannot certify a source-wide simplification edit.
            description:item.node.description,freeze:null,
            traceParent:item.node.traceParent,
            sourceModule: target?.sourceModule ?? info.sourceModule, sourceName: target?.name ?? info.name,
            definitionStart: target?.definitionStart ?? item.node.start,
            templateBinding: binding, templateParameters: parameters, universes: [...levels],
            templateOffset: item.node.start, ...(expansion ? {templateExpansion:expansion} : {}) };
        }
        for (const item of references) if (item.node.role === "simplification witness") {
          const witness = this.localSymbols[`${instance}__local_${item.node.start}`];
          witness.rewriteSteps = references.filter(step => step.node.role === "simplification step"
            && step.node.traceParent === item.node.start).map(step => {
            const symbol = this.localSymbols[`${instance}__local_${step.node.start}${
              expansionSuffix(step.node.role,step.node.expansionIndex)}`];
            return {name:symbol.name,binding:symbol.binding,role:symbol.role,
              description:symbol.description,start:step.node.start,end:step.node.end,
              templateBinding:binding,templateParameters:parameters,universes:[...levels],
              templateOffset:step.node.start,templateExpansion:symbol.templateExpansion};
          });
        }
      }
      if (expansion && (!Number.isInteger(offset) || typeof expansion.role !== "string"
        || !Number.isSafeInteger(expansion.index) || expansion.index < 1))
        throw new Error("Invalid template expansion selection.");
      const selected = offset === undefined ? instance
        : `${instance}__local_${offset}${expansionSuffix(expansion?.role,expansion?.index)}`;
      if (offset !== undefined && !this.views.has(selected))
        throw new Error("No checked term is available for this position in the selected specialization.");
      return this.inspect(selected, { normalize });
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
    const simplifiedType = simplifyTypeApplications(view.type);
    const presentation = simplifiedType === view.type ? view
      : checkReduction(this, view, "type", simplifiedType).view;
    view.folded = foldedInspection(presentation, aliases);
    view.expressionText = cubicalText(view.folded.expression, symbols);
    view.typeText = cubicalText(view.folded.type, symbols);
    if (info?.verified && !local) {
      const module = info.sourceModule ?? this.main;
      const declaration = this.sourceAsts.get(module)?.declarations.find(d => d.name.text === info.name);
      if (declaration) view.statement = sourceStatement(this.sources[module], declaration, this.declarationReferences.get(binding));
      // Keep proof blocks compact, with their checked bodies available to inspect.
      if (declaration?.body) view.folded.reference = { tag: "DefRef", name: binding };
      if (!view.statement) {
        let conclusion = cubicalMathTree(view.folded.type, symbols), raw = view.folded.type;
        const parameters = [];
        while (conclusion.kind === "Pi") {
          parameters.push({ name: [{ text: conclusion.name, binding: symbols[raw.name]?.binding }], type: cubicalTextParts(conclusion.domain) });
          conclusion = conclusion.body;
          raw = raw.body;
        }
        view.statement = { inferred: true, conclusion: cubicalTextParts(conclusion), parameters };
      }
    }
    if (local && view.sourceBinding && local.term.tag !== "Var") view.folded.reference = {
      tag: "DisplayRef", name: this.localSymbols[binding]?.name, binding: view.sourceBinding,
    };
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
