import { sourceStatement } from "./cubical-statement.mjs";
import { CubicalKernel } from "./cubical-kernel.mjs";
import { NativeCubicalElaborator } from "./cubical-elaborator.mjs";
import { Translator } from "./dist/cubical-runtime/translate.mjs";
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
    this.gaps = []; this.evaluations = []; this.links = []; this.sources = {}; this.completed = 0;
    // Proof statements of each checked module, with their goals (see steps()).
    this.moduleSteps = new Map();
    this.failedImports = new Map();
  }
  dispose() { this.kernel.dispose(); }
  assumptionSymbols() {
    return Object.fromEntries([...this.checker.assumptions].map(([binding, type]) => [binding, {
      binding, name: this.checker.assumptionLabels.get(binding) ?? binding, kind: "axiom", role: "explicit axiom",
      verified: true, type: cubicalText(type, this.symbols), axioms: [binding],
      description: "An explicit logical assumption from the library. Its full signature is shown in the Axioms section.",
    }]));
  }
  async check(source, main = "current", onProgress = () => {}) {
    // Discover the source graph before checking. This only reads/parses source;
    // it does not run the mathematical library or count repeated imports twice.
    const prepared = new Map();
    let total = this.completed;
    // The reader is told which module imports each name, since where a module
    // lives decides where its imports are found (module-resolution.mjs). A
    // reader may refuse a module whose import this check already holds under
    // another file; a check holds one module per name.
    const prepare = async (name, text = null, importer = null) => {
      if (this.modules.has(name) || prepared.has(name)) return;
      try {
        text ??= await this.readSource(name, importer);
        const ast = parse(text);
        prepared.set(name, { text, ast });
        total += ast.declarations.length;
        onProgress({ completed: this.completed, total: null, current: name,
          phase: "loading", unit: "declarations", instructions: this.checker.steps });
        for (const dependency of ast.imports) await prepare(dependency, null, name);
        const refused = await this.readSource.checkImports?.(name, ast.imports);
        if (refused) prepared.set(name, { error: new Error(refused) });
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
        this.failedImports.set(name, error.message);
        visiting.delete(name); return new Map();
      }
      this.sources[name] = text;
      this.sourceAsts.set(name, ast);
      let env = new Map(),simpRegistry=emptySimpRegistry();
      for (const dependency of ast.imports) {
        env = new Map([...env, ...await load(dependency)]);
        simpRegistry=mergeSimpRegistries(simpRegistry,this.simpRegistries.get(dependency));
      }
      // A declaration that fails after an import failed names that import:
      // its missing names are usually the import's.
      const failedImport = ast.imports.find(dependency => this.failedImports.has(dependency));
      // The note goes before a trailing source position, which stays last.
      const failure = reason => failedImport && reason ? reason.replace(/(?: at \d+:\d+)?$/,
        position => ` (import ${failedImport} failed: ${this.failedImports.get(failedImport)})${position}`) : reason;
      const define = this.checker.define.bind(this.checker);
      const checker = Object.create(this.checker);
      checker.bindingName = local => `${name}__${local}`;
      checker.define = (local, term, type) => define(`${name}__${local}`, term, type);
      let pending = [];
      let transaction = null;
      const statements = [];
      let current = null;
      const translator = new Translator({ normalize: false, checker,simpRegistry,moduleName:name,
        onStep: step => statements.push({ ...step, declaration: current }),
        onDeclarationStart: declaration => {
          current = declaration.name.text;
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
              let head = item.term; while (head.tag === "App" || head.tag === "LApp") head = head.fn;
              const source = item.aliases?.find(alias => alias.name === item.node.name && alias.term === item.term);
              const definition = head.tag === "DefRef" && !source && !item.node.expressionSite;
              const binding = definition ? head.name : `${name}__local_${item.node.start}${
                expansionSuffix(item.node.role,item.node.expansionIndex)}`;
              references.push({ start: item.node.start, binding });
              if (!definition && !this.views.has(binding)) this.views.set(binding, { ...item, module: name });
              if (!definition) this.localSymbols[binding] = { binding, name: item.node.name,
                role: item.node.role ?? (item.term.tag === "Var" ? "Local assumption" : "Local definition"), verified: true,
                expansion: item.node.expansion, description: item.node.description,
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
        const reason = verified ? d.reason : failure(d.reason);
        const info = { name: d.name, binding, kind: syntax.kind, role: syntax.kind, verified,
          status: d.status, reason, errorStart: d.errorStart, errorEnd: d.errorEnd,
          rewriteWork: d.rewriteWork,
          unfoldingHints: d.native?.unfoldingHints ?? [], axioms: d.native?.axioms ?? [], start: syntax.start, end: syntax.end,
          definitionStart: syntax.start, description: leadingDocumentation(text, syntax.start)?.text ?? "",
          ...(name === main ? {} : { sourceModule: name, sourceName: d.name }),
          // A universe variable's source name stands for U(x): it names x.
          type: verified ? cubicalText(d.type, { ...this.symbols, ...Object.fromEntries(
            (this.declarationBindings.get(binding) ?? []).map(item => [item.term.tag === "Var" ? item.term.name
              : item.term.tag === "U" && item.term.level?.tag === "Var" ? item.term.level.name : null, { name: item.node.name }])
              .filter(([variable]) => variable)) }) : reason };
        this.symbols[binding] = info;
        if (!verified) this.gaps.push({ module: name, name: d.name,
          reason, start: d.errorStart, end: d.errorEnd });
        if (name === main) this.links.push({ ...info, start: syntax.name.start, end: syntax.name.end });
      }
      this.moduleSteps.set(name, statements);
      this.modules.set(name, result.env); visiting.delete(name);
      return result.env;
    };
    await load(main, source);
    const all = Object.values(this.symbols), outputs = all.filter(d => !d.sourceModule);
    this.main = main;
    // Goals are shown on demand; posting the result to the page reads them.
    let steps = null;
    const program = this;
    return this.metadata = {
      get steps() { return steps ??= program.steps(main); }, backend: "cubical", mode: "mathematical", source, outputs,
      imports: all.filter(d => d.sourceModule), symbols: [...all, ...Object.values(this.assumptionSymbols())], assumptionLabels: Object.fromEntries(this.checker.assumptionLabels), declarations: outputs, links: this.links,
      declarationCount: total, instructionCount: this.checker.steps, axiomCount: new Set(outputs.flatMap(d => d.axioms)).size, gaps: this.gaps,
      evaluations: this.evaluations,
      complete: outputs.length > 0 && outputs.every(d => d.verified)
        && !this.gaps.some(gap=>gap.directive), sources: this.sources };
  }
  // Each proof statement of a module: where it is, the goal it faced, with the
  // names in scope, and the term it built. The rest of the block's proof
  // shows as a hole ?, so each statement shows only its own part.
  steps(module, declaration = null) {
    const records = (this.moduleSteps.get(module) ?? [])
      .filter(record => Number.isInteger(record.statement?.start) && (!declaration || record.declaration === declaration));
    const proofOf = new Map(records.map(record => [record.statement, record.proof]));
    const hole = { tag: "Var", name: "?" };
    const without = (term, part, seen = new WeakMap()) => {
      if (term === part) return hole;
      if (!term || typeof term !== "object") return term;
      if (seen.has(term)) return seen.get(term);
      const copy = Array.isArray(term) ? [] : {};
      seen.set(term, copy);
      for (const [key, value] of Object.entries(term)) copy[key] = without(value, part, seen);
      return copy;
    };
    return records.map(record => {
      const rest = record.next && proofOf.get(record.next);
      const built = rest ? without(record.proof, rest) : record.proof;
      return { start: record.statement.start, end: record.statement.end, kind: record.statement.kind,
        declaration: record.declaration, closes: !record.next,
        ...this.checker.displayGoal(record.goal.scope.context, record.goal.target, built) };
    }).sort((a, b) => a.start - b.start);
  }
  // Check one more module on top of the loaded ones, as a REPL entry does,
  // and report only what it added. The program keeps presenting its main
  // module: inspection, export and metadata are unchanged.
  async checkEntry(source, name) {
    const kept = { main: this.main, metadata: this.metadata, links: this.links.length,
      gaps: this.gaps.length, evaluations: this.evaluations.length };
    try {
      await this.check(source, name);
      const declarations = Object.values(this.symbols).filter(info => !info.sourceModule && info.binding.startsWith(`${name}__`));
      for (const info of declarations) Object.assign(info, { sourceModule: name, sourceName: info.name });
      return { declarations, evaluations: this.evaluations.slice(kept.evaluations), gaps: this.gaps.slice(kept.gaps) };
    } finally {
      Object.assign(this, { main: kept.main, metadata: kept.metadata });
      this.links.length = kept.links; this.gaps.length = kept.gaps; this.evaluations.length = kept.evaluations;
    }
  }
  generatedSymbols() {
    return Object.fromEntries([...this.kernel.definitions.keys()].filter(binding => !this.symbols[binding]).map(binding => [binding, {
      binding, name: binding.replace(/^builtin__/, ""),
      role: "Derived kernel definition", verified: true,
      description: "An ordinary definition checked by cubical C. Its body is available below; it introduces no axiom.",
    }]));
  }
  inspect(binding, { normalize = false } = {}) {
    // An inspection elaborates outside any declaration's transaction: its
    // instructions start from a driver of their own.
    this.kernel.instructionDriver = null;
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
    const checked = this.checker.checkView(term, expected, context, dimensions);
    if (normalize) checked.term = this.checker.syntax.decode(this.kernel.normalize(checked.expression), dimensions);
    const bindings = this.declarationBindings.get(binding) ?? [];
    const aliases = (local?.aliases ?? []).map(alias => ({ ...alias, binding: `${local.referencePrefix ?? local.module}__local_${alias.start}` }));
    const symbols = { ...this.symbols, ...this.localSymbols, ...this.generatedSymbols(), ...this.assumptionSymbols() };
    const variableNames = Object.fromEntries([
      ...bindings.map(item => ({ term: item.term, name: item.node.name, binding: `${local?.referencePrefix ?? info?.sourceModule ?? this.main}__local_${item.node.start}` })),
      ...aliases,
    // A universe variable's source name stands for the universe U(x), so it
    // names the level variable x.
    ].map(alias => ({ ...alias, variable: alias.term.tag === "Var" ? alias.term.name
      : alias.term.tag === "U" && alias.term.level?.tag === "Var" ? alias.term.level.name : null }))
      .filter(alias => alias.variable).reverse().map(alias => [alias.variable, { name: alias.name, binding: alias.binding }]));
    for (const [name, value] of Object.entries(variableNames)) symbols[name] = { ...value, local: true };
    const view = { backend: "cubical", name: binding,
      unfoldingHints, expression: checked.term, type: checked.type,
      expressionText: cubicalText(checked.term, this.symbols), typeText: cubicalText(checked.type, this.symbols),
      dimensions: [...dimensions], context: context.map(([name, type]) => ({ name,
        label: variableNames[name]?.name ?? this.checker.assumptionLabels.get(name) ?? name,
        binding: variableNames[name]?.binding ?? (this.checker.assumptions.has(name) ? name : null), type })), symbols,
      checkingSteps: checked.checkingSteps, reductionSteps: checked.reductionSteps, axioms: [...assumptions.keys()] };
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
        while (conclusion.kind === "Pi" || conclusion.kind === "LevelPi") {
          const level = conclusion.kind === "LevelPi";
          parameters.push({ name: [{ text: conclusion.name, binding: symbols[raw.name]?.binding }], relation: level ? "<" : ":",
            type: level ? [{ text: "UU0" }] : cubicalTextParts(conclusion.domain) });
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
      ...(view ? { expression: view.expression, type: view.type, context: view.context } : {}) };
  }
}
