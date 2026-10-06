import { sourceStatement } from "./cubical-statement.mjs";
import { CubicalKernel } from "./cubical-kernel.mjs";
import { NativeCubicalElaborator, printedLabels } from "./cubical-elaborator.mjs";
import { Translator } from "./translator/translate.mjs";
import {emptySimpRegistry,mergeSimpRegistries} from "./translator/simp-registry.mjs";
import { substituteTerm, T } from "./translator/core.mjs";
import { localName, printedForms, printsAsItself } from "./translator/names.mjs";
import { parse } from "./cubist/parser.mjs";
import { lint } from "./cubist/lint.mjs";
import { diagnosticCode } from "./diagnostics.mjs";
import { leadingDocumentation } from "./cubist/documentation.mjs";
import { foldedInspection } from "./cubical-inspection.mjs";
import { cubicalText, cubicalTextParts, cubicalMathTree } from "./cubical-notation.mjs";
import { checkReduction, simplifyTypeApplications } from "./cubical-reduction.mjs";
import { CubicalDeclarationTransaction } from "./cubical-transaction.mjs";
import naturalSource from "./translator/nat-source.mjs";

const expansionSuffix = (role,index) => index ? `_${role.replaceAll(" ","_")}_${index}` : "";

// Imports are source, loaded on demand. Every module has its own environment;
// closed native definitions have qualified names so shadowing cannot retarget
// an earlier checked reference. Unsupported declarations never become axioms.
export class CubicalProgram {
  constructor(module, readSource, { onDeclarationStart, onDeclaration, collectReferences = true, optimizations = {}, manageTransactions = true,
    searchFuel, declarationFuel, experimental, representation, bundledNat = true, prelude } = {}) {
    // The representation map τ to declared counterparts was the differential
    // fixtures' (H1 specification, 7.4), retired with them.
    if (representation !== undefined)
      throw Error("The representation option was removed with the differential fixtures: Nat, W and pushouts are source declarations.");
    // Declared types (H1) are on by default since their release; the option
    // that admitted them experimentally is gone.
    if (experimental !== undefined)
      throw Error("H1 is no longer experimental: declared types are on by default, so drop the experimental option.");
    // Fuel limits (web/translator/fuel.mjs), for a measurement or a test; the defaults otherwise.
    this.fuelLimits = { searchFuel, declarationFuel };
    this.kernel = new CubicalKernel(module);
    this.kernel.setOptimizations(optimizations);
    this.checker = new NativeCubicalElaborator(this.kernel);
    this.readSource = readSource;
    // Nothing is imported automatically. A module that uses the natural
    // numbers imports nat, which a reader with no library can still load from
    // its bundled source unless bundledNat is false.
    if (prelude !== undefined)
      throw Error("The prelude option was removed: no module is imported automatically, so a module imports nat itself; bundledNat controls nat's bundled source.");
    this.bundledNat=bundledNat;
    this.onDeclarationStart = onDeclarationStart; this.onDeclaration = onDeclaration;
    this.collectReferences = collectReferences;
    this.manageTransactions = manageTransactions;
    this.localSymbols = {}; this.declarationBindings = new Map();
    this.declarationReferences = new Map();
    this.modules = new Map(); this.symbols = {}; this.views = new Map();
    this.sourceAsts = new Map();
    this.simpRegistries = new Map();
    this.gaps = []; this.evaluations = []; this.prints = []; this.links = []; this.sources = {}; this.completed = 0;
    // What each directive (evaluate, print, simp_rule, simp_set) spent (fuel.mjs).
    this.directiveFuel = [];
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
  // Read and parse a module and, before it, its imports, into
  // `discovery.prepared`, counting their declarations into `discovery.total`.
  // The reader is told which module imports each name, since where a module
  // lives decides where its imports are found (module-resolution.mjs). A
  // reader may refuse a module whose import this check already holds under
  // another file; a check holds one module per name. Each check reads afresh,
  // so a failed read is retried.
  async discover(discovery, name, text, importer, onProgress) {
    const { prepared } = discovery;
    if (this.modules.has(name) || prepared.has(name)) return;
    try {
      if(text===null) {
        try { text=await this.readSource(name,importer); }
        catch(error) {if(name!=="nat"||!this.bundledNat)throw error;}
        // Readers with no standard library (such as an exported inspection)
        // can still load nat's bundled source.
        if(name==="nat"&&this.bundledNat&&!text)text=naturalSource;
      }
      const ast = parse(text);
      prepared.set(name, { text, ast });
      discovery.total += ast.declarations.length;
      onProgress({ completed: this.completed, total: null, current: name,
        phase: "loading", unit: "declarations", instructions: this.checker.steps });
      for (const dependency of ast.imports) await this.discover(discovery, dependency, null, name, onProgress);
      const refused = await this.readSource.checkImports?.(name, ast.imports);
      if (refused) prepared.set(name, { error: new Error(refused) });
    } catch (error) { prepared.set(name, { error }); }
  }
  // The references a checked declaration's elaboration reported: its local
  // bindings and their views, each name's binding, and, in the checked
  // module, its source links.
  recordReferences(name, main, declaration, result, pending) {
    this.declarationBindings.set(`${name}__${result.name}`, pending.filter(item => item.node.isBinding));
    const references = [];
    const declarationLinks = [];
    this.declarationReferences.set(`${name}__${result.name}`, references);
    for (const item of pending) {
      if (!Number.isInteger(item.node.start)) continue;
      let head = item.term; while (head.tag === "App" || head.tag === "LApp") head = head.fn;
      const source = item.aliases?.find(alias => alias.name === item.node.name && alias.term === item.term);
      const declared = !source && !item.node.expressionSite && item.node.declarationBinding;
      const definition = !!declared || head.tag === "DefRef" && !source && !item.node.expressionSite;
      const binding = definition ? declared || head.name : `${name}__local_${item.node.start}${
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
        end: item.node.end, definitionStart: source?.start, role: item.node.role ?? (declared ? "inductive" : definition ? "definition" : "local"),
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
  // A module's results: its simplification rules, its directives' fuel and
  // gaps, and each declaration's symbol, gap and, in the checked module, link.
  // `failure` adds a failed import's note to a reason.
  recordModule(name, main, text, ast, result, failure) {
    this.simpRegistries.set(name,result.simpRegistry);
    for(const directive of result.directives??[]) {
      this.directiveFuel.push({ module: name, kind: directive.kind, name: directive.name, searchFuel: directive.searchFuel ?? null });
      if(directive.status!=="checked")
        this.gaps.push({module:name,name:`${directive.kind} ${directive.name}`,
          reason:directive.reason,code:diagnosticCode(directive.reason),directive:true,start:directive.start});
      else if(directive.kind==="evaluate")
        this.evaluations.push({module:name,name:directive.name,value:directive.normalText});
      else if(directive.kind==="print")
        this.prints.push({module:name,name:directive.name,text:directive.text,start:directive.start});
    }
    const byName = new Map(ast.declarations.map(d => [d.name.text, d]));
    for (const d of result.declarations) {
      // A theory's declarations bring their generated syntax (theories.mjs).
      const syntax = d.syntax ?? byName.get(d.name), binding = `${name}__${d.name}`;
      const verified = d.status === "checked-native-cubical";
      const reason = verified ? d.reason : failure(d.reason);
      const info = { name: d.name, binding, kind: syntax.kind, role: syntax.kind, verified,
        status: d.status, reason, ...(verified ? {} : { code: diagnosticCode(reason) }), errorStart: d.errorStart, errorEnd: d.errorEnd,
        rewriteWork: d.rewriteWork, searchFuel: d.searchFuel, failure: d.failure ?? null,
        axioms: d.native?.axioms ?? [],
        // Kernel extensions under review that the result relies on, shown
        // apart from assumptions; computable accepts them. None is under
        // review since H1's release, so this list is empty.
        extensions: d.native?.extensions ?? [], start: syntax.start, end: syntax.end,
        definitionStart: syntax.start, description: leadingDocumentation(text, syntax.start)?.text ?? "",
        ...(name === main ? {} : { sourceModule: name, sourceName: d.name }),
        // A universe variable's source name stands for U(x): it names x.
        type: verified ? cubicalText(d.type, { ...this.symbols, ...Object.fromEntries(
          (this.declarationBindings.get(binding) ?? []).map(item => [item.term.tag === "Var" ? item.term.name
            : item.term.tag === "U" && item.term.level?.tag === "Var" ? item.term.level.name : null, { name: item.node.name }])
            .filter(([variable]) => variable)) }) : reason };
      this.symbols[binding] = info;
      if (!verified) this.gaps.push({ module: name, name: d.name,
        reason, code: info.code, start: d.errorStart, end: d.errorEnd });
      // A theory's name links to its models' type, a field's to its projection.
      if (name === main && syntax.generated?.role !== "make")
        this.links.push({ ...info, start: syntax.name.start, end: syntax.name.end });
    }
  }
  async check(source, main = "current", onProgress = () => {}) {
    // Discover the source graph before checking. This only reads and parses
    // source; it does not run the mathematical library or count repeated
    // imports twice.
    this.readSource.beginCheck?.();
    const discovery = { prepared: new Map(), total: this.completed };
    await this.discover(discovery, main, source, null, onProgress);
    const { prepared } = discovery;
    let total = discovery.total;
    // Imports that failed in this check, used or not: any makes it incomplete.
    const failedHere = new Set();
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
        this.gaps.push({ module: name, reason: error.message, code: diagnosticCode(error.message) });
        this.failedImports.set(name, error.message);
        failedHere.add(name);
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
      checker.define = (local, term, type, parameters) => define(`${name}__${local}`, term, type, parameters);
      let pending = [];
      let transaction = null;
      const statements = [];
      let current = null;
      const translator = new Translator({ normalize: false, checker,simpRegistry,moduleName:name,
        inspectSignature: binding => this.signatureText(binding),
        ...Object.fromEntries(Object.entries(this.fuelLimits).filter(([, limits]) => limits)),
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
        onReference: this.collectReferences ? (node, term, context, dimensions, aliases) => pending.push({ node, term, context, dimensions, aliases }) : null,
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
          if (result.status === "checked-native-cubical") this.recordReferences(name, main, declaration, result, pending);
          pending = [];
          onProgress({ completed: this.completed, total,
            current: `${name}.${result.name}`, phase: "checked", unit: "declarations", instructions: checker.steps });
        },
      });
      const result = translator.translate(text, env);
      this.checker.steps = checker.steps;
      this.recordModule(name, main, text, ast, result, failure);
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
      evaluations: this.evaluations, prints: this.prints, directiveFuel: this.directiveFuel,
      // Unused bindings that can be removed, in the checked module only; a
      // fresh parse, since elaboration annotates the syntax it checks.
      warnings: lint(source),
      complete: outputs.length > 0 && outputs.every(d => d.verified)
        && !this.gaps.some(gap=>gap.directive) && failedHere.size === 0, sources: this.sources };
  }
  // A declared type's signature as the kernel admitted it (the H1
  // specification's 6.5): its former, h-level, recorded universe parameters,
  // each constructor's normal form, with its data, positions and dimensions,
  // and the eliminator's clause types. Null for a name that is not a
  // declared type.
  signature(binding) {
    const record = this.kernel.signatures.get(binding);
    if (!record) return null;
    const info = this.kernel.signature(record.index), syntax = this.checker.syntax;
    const symbols = info.symbols.map(symbol => this.kernel.symbolName(symbol));
    // The sort and the earlier constructors appear in constructor types as
    // the admission's variables. They are shown as the sort and constructors
    // they stand for, which print by their declared names: a variable named
    // S1 would print as its stem S.
    // Within the check that declares it, before its symbols are recorded, a
    // type is named without its module.
    const name = this.symbols[binding]?.name ?? localName(binding);
    const sort = T.sort(binding);
    const shown = [[info.sort, sort], ...info.constructors.map((c, index) =>
      [c.symbol, T.constructor(index, sort, record.constructors[index])])]
      .map(([symbol, term]) => [this.kernel.symbolName(symbol), term]);
    const display = term => shown.reduce((t, [from, to]) => substituteTerm(t, from, to), syntax.decode(term));
    // Universe parameters by their names in the declaration, where the
    // elaborator declared the type; the kernel's own symbols otherwise.
    const slots = this.checker.inductives?.get(binding)?.slots.filter(slot => slot.level !== undefined);
    const levelNames = slots?.length === info.levels ? slots.map(slot => slot.source) : symbols.slice(0, info.levels);
    return { name, binding, former: syntax.decode(info.former),
      modifier: info.modifier === 0 ? "type" : info.modifier === 1 ? "prop" : info.modifier === 2 ? "set" : `trunc(${info.modifier - 2})`,
      recorded: levelNames.filter((_, j) => info.recorded >> j & 1),
      extensions: info.experimental ? ["H1"] : [],
      constructors: info.constructors.map((c, index) => ({ name: record.constructors[index], type: display(c.type),
        data: c.data, positions: c.positions, dimensions: c.dimensions, generated: c.generated })),
      eliminator: this.eliminator(binding, name) };
  }
  // The generated eliminator (the H1 specification's 3.6), for a motive P
  // over the type at its own parameters: each clause's type as the kernel
  // computes it (ClauseType_k), given a variable for each earlier clause, as
  // a later clause's boundary mentions them. The kernel work is rolled back.
  eliminator(binding, source) {
    const inductive = this.checker.inductives?.get(binding);
    if (!inductive) return null;
    // Computed once per admitted signature: the kernel's symbol registries
    // keep the names a computation uses, which a rollback does not take back.
    this.eliminators ??= new WeakMap();
    if (this.eliminators.has(inductive.record)) return this.eliminators.get(inductive.record);
    const view = this.computeEliminator(binding, source, inductive);
    this.eliminators.set(inductive.record, view);
    return view;
  }
  computeEliminator(binding, source, inductive) {
    const names = inductive.record.constructors;
    // The names are new to everything the view shows: the type, its
    // constructors and parameters, and every type, constructor, definition
    // and variable their types mention, in each form the display may print
    // them (printedForms). And the display prints the new names as they are
    // (printsAsItself), so no numbered name the display makes is one of them.
    // No assumption occurs in these types, so none of the labels the display
    // shows assumptions by needs avoiding: the kernel admits a signature
    // only from closed judgements, in a context of the signature's own
    // entries (the H1 specification's 5.2), and refuses one that mentions
    // an assumption (tests/inductive-declarations.test.mjs).
    const used = new Set([source, ...names, ...inductive.slots.map(slot => slot.source)].flatMap(printedForms));
    const syntax = this.checker.syntax, info = this.kernel.signature(inductive.record.index);
    for (const term of [info.former, ...info.constructors.map(c => c.type)].map(handle => syntax.decode(handle))) {
      for (const label of printedLabels(term)) used.add(label);
      const visit = (t, seen = new WeakSet()) => {
        if (!t || typeof t !== "object" || seen.has(t)) return;
        seen.add(t);
        if (typeof t.name === "string") for (const form of printedForms(t.name)) used.add(form);
        Object.values(t).forEach(value => visit(value, seen));
      };
      visit(term);
    }
    for (const parameter of inductive.parameters) for (const label of printedLabels(parameter.type)) used.add(label);
    // A candidate that ends in a digit, or is U's and an underscore, does
    // not print as itself. So the rounds of suffixes are "", "_", then "_a",
    // "_b", …: never a digit, nor a second underscore, which with the first
    // would name a module.
    const letters = n => (n >= 26 ? letters(Math.floor(n / 26) - 1) : "") + String.fromCharCode(97 + n % 26);
    const pick = candidates => {
      // No candidate has a run of underscores or one at its end, as c_case
      // for a constructor c_: from the third round on, every candidate prints
      // as itself, so one not yet used is found.
      const stems = candidates.map(name => name.replace(/_{2,}/g, "_").replace(/_+$/, "") || "x");
      for (let round = 0; ; round++) {
        const suffix = round === 0 ? "" : round === 1 ? "_" : `_${letters(round - 2)}`;
        for (const candidate of stems.map(name => name + suffix))
          if (printsAsItself(candidate) && !used.has(candidate)) { used.add(candidate); return candidate; }
      }
    };
    const context = new Map(), parameters = [], levels = [];
    for (const slot of inductive.slots) {
      if (slot.level !== undefined) {
        context.set(slot.name, T.bound);
        if (inductive.levels[slot.level].recorded) levels.push(T.variable(slot.name));
      } else {
        context.set(slot.name, inductive.parameters[slot.parameter].type);
        parameters.push(T.variable(slot.name));
      }
    }
    const instance = T.sort(binding, parameters, levels);
    const universe = pick(["U", "V", "W", "X", "Y"]), motive = pick(["P", "Q", "M", "R"]), z = pick(["z", "w", "v"]);
    const motiveType = T.pi(z, instance, T.universe(T.variable(universe)));
    context.set(universe, T.bound);
    context.set(motive, motiveType);
    const clauses = [];
    const transaction = new CubicalDeclarationTransaction(this.kernel, this.checker);
    try {
      names.forEach((constructor, k) => {
        const shown = info.constructors[k].generated ? `${source}.squash` : constructor;
        const variable = pick([`${constructor}_case`, `${constructor}_clause`]);
        const type = this.checker.nextClauseType(T.variable(motive), clauses.map(clause => T.variable(clause.name)), context);
        context.set(variable, type);
        clauses.push({ constructor: shown, name: variable, type });
      });
      return { universe, motive, motiveType, clauses };
    } catch (error) {
      return { universe, motive, motiveType, clauses, error: error.message };
    } finally { transaction.finish(false); }
  }
  // The same, as display text, for the CLI's inspect and the workbench:
  // whole, as a clause's boundary comes at the end of its type, and with one
  // naming for the whole view, so a parameter has one name in every type.
  signatureView(binding) {
    const signature = this.signature(binding);
    if (!signature) return null;
    const { eliminator } = signature;
    const terms = [signature.former, ...signature.constructors.map(c => c.type),
      ...(eliminator ? [eliminator.motiveType, ...eliminator.clauses.map(c => c.type)] : [])];
    const texts = this.checker.displayTexts(this.qualifyGenerated(terms), Infinity, 1000000);
    let next = 0;
    const text = () => texts[next++];
    return { ...signature, former: text(),
      constructors: signature.constructors.map(c => ({ ...c, name: c.generated ? `${signature.name}.squash` : c.name, type: text() })),
      eliminator: eliminator && { motive: `${eliminator.motive} : ${text()}`,
        universe: eliminator.universe, error: eliminator.error ?? null,
        clauses: eliminator.clauses.map(c => ({ constructor: c.constructor, name: c.name, type: text() })) } };
  }
  // A declared type's signature on one line, as `print(inspect(T));` shows
  // it: what the CLI's inspect shows, each constructor and clause ended by `;`.
  signatureText(binding) {
    const view = this.signatureView(binding);
    if (!view) return null;
    const counted = (n, word) => `${n} ${word}${n === 1 ? "" : "s"}`;
    const constructors = view.constructors.map(c => `${c.name} : ${c.type} [${c.data} data, `
      + `${counted(c.positions, "position")}, ${counted(c.dimensions, "dimension")}${c.generated ? ", generated" : ""}];`);
    const eliminator = view.eliminator && [`eliminator for ${view.eliminator.motive} {`,
      ...view.eliminator.clauses.map(c => `${c.name} : ${c.type};`),
      ...(view.eliminator.error ? [`the remaining clause types could not be computed: ${view.eliminator.error}`] : []), "}"];
    return [`inductive ${view.name} : ${view.former} (${[view.modifier, ...view.recorded.length ? [`recorded ${view.recorded.join(", ")}`] : []].join(", ")})`,
      "{", ...constructors, "}", ...eliminator ?? [],
      ...view.extensions.length ? [`kernel extensions: ${view.extensions.join(", ")}`] : []].join(" ");
  }
  // A signature's generated constructor as the source writes it, T.squash:
  // a user constructor may be named squash too.
  qualifyGenerated(term) {
    const generated = new Map(), copies = new WeakMap();
    const generatedOf = signature => {
      if (!generated.has(signature)) {
        const record = this.kernel.signatures.get(signature);
        generated.set(signature, record ? this.kernel.signature(record.index).constructors.findIndex(c => c.generated) : -1);
      }
      return generated.get(signature);
    };
    const visit = t => {
      if (!t || typeof t !== "object") return t;
      if (copies.has(t)) return copies.get(t);
      const copy = Array.isArray(t) ? [] : {};
      copies.set(t, copy);
      for (const [key, value] of Object.entries(t)) copy[key] = visit(value);
      const signature = t.tag === "Con" ? t.sort?.signature : null;
      if (typeof signature === "string" && t.index === generatedOf(signature))
        copy.name = `${this.symbols[signature]?.name ?? localName(signature)}.squash`;
      return copy;
    };
    return visit(term);
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
        ...this.checker.displayGoal(record.goal.scope.shownContext([record.goal.target, built]), record.goal.target, built, 400, null, true,
          { selection: record.goal.scope.env.get("\u0000selection")?.name ?? null }) };
    }).sort((a, b) => a.start - b.start);
  }
  // Check one more module on top of the loaded ones, as a REPL entry does,
  // and report only what it added. The program keeps presenting its main
  // module: inspection, export and metadata are unchanged.
  // What a module's top-level `use` statements select at its end, as their
  // source text: a REPL entry after the module reads in them (L2.10j).
  selectionsAfter(name) {
    const ast = this.sourceAsts.get(name), text = this.sources[name];
    return (ast?.items ?? []).filter(item => item.kind === "use").map(item => text.slice(item.model.start, item.model.end));
  }
  async checkEntry(source, name) {
    const kept = { main: this.main, metadata: this.metadata, links: this.links.length,
      gaps: this.gaps.length, evaluations: this.evaluations.length, prints: this.prints.length };
    try {
      await this.check(source, name);
      const declarations = Object.values(this.symbols).filter(info => !info.sourceModule && info.binding.startsWith(`${name}__`));
      for (const info of declarations) Object.assign(info, { sourceModule: name, sourceName: info.name });
      return { declarations, evaluations: this.evaluations.slice(kept.evaluations), prints: this.prints.slice(kept.prints),
        gaps: this.gaps.slice(kept.gaps) };
    } finally {
      Object.assign(this, { main: kept.main, metadata: kept.metadata });
      this.links.length = kept.links; this.gaps.length = kept.gaps; this.evaluations.length = kept.evaluations;
      this.prints.length = kept.prints;
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
    let term, expected = null, context = [], dimensions = new Map();
    if (local) { term = local.term; context = [...local.context]; dimensions = local.dimensions; }
    else if (this.checker.assumptions.has(binding)) {
      term = { tag: "Var", name: binding }; expected = this.checker.assumptions.get(binding);
    } else {
      const reference = this.kernel.definitions.get(binding);
      if (!reference) throw new Error("No checked native definition for this name.");
      const definition = this.checker.definitionViews.get(binding);
      term = definition.term; expected = definition.type;
    }
    const assumptions = this.checker.requiredAssumptions(term, expected, context.map(([, type]) => type));
    context = [...assumptions, ...context];
    const checked = this.checker.checkView(term, expected, context, dimensions);
    // The kernel extensions of the term as checked: a normal form may no
    // longer mention the declared type it computed through.
    const extensions = this.checker.extensionsOf(checked.term, checked.type, ...context.map(([, type]) => type));
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
      expression: checked.term, type: checked.type,
      expressionText: cubicalText(checked.term, this.symbols), typeText: cubicalText(checked.type, this.symbols),
      dimensions: [...dimensions], context: context.map(([name, type]) => ({ name,
        label: variableNames[name]?.name ?? this.checker.assumptionLabels.get(name) ?? name,
        binding: variableNames[name]?.binding ?? (this.checker.assumptions.has(name) ? name : null), type })), symbols,
      checkingSteps: checked.checkingSteps, reductionSteps: checked.reductionSteps, axioms: [...assumptions.keys()],
      // The kernel extensions the inspected term relies on, apart from assumptions.
      extensions };
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
