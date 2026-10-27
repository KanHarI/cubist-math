import { sourceStatement } from "./cubical-statement.mjs";
import { CubicalKernel } from "./cubical-kernel.mjs";
import { NativeCubicalElaborator, printedLabels } from "./cubical-elaborator.mjs";
import {SourceUnit} from "./translator/elaboration.mjs";
import { Translator } from "./translator/translate.mjs";
import { selectionName } from "./translator/theories.mjs";
import {notationForScope} from "./translator/notation-context.mjs";
import {emptySimpRegistry,mergeSimpRegistries} from "./translator/simp-registry.mjs";
import { substituteTerm, T } from "./translator/core.mjs";
import { localName, printedForms, printsAsItself } from "./translator/names.mjs";
import { parse } from "./cubist/parser.mjs";
import {requireTestMode} from "./cubist/test-pragmas.mjs";
import { lint } from "./cubist/lint.mjs";
import {ownsSource} from "./cubist/link-sites.mjs";
import { diagnosticCode } from "./diagnostics.mjs";
import { leadingDocumentation } from "./cubist/documentation.mjs";
import { foldedInspection } from "./cubical-inspection.mjs";
import { cubicalText, cubicalTextParts, cubicalMathTree } from "./cubical-notation.mjs";
import { checkReduction, simplifyTypeApplications } from "./cubical-reduction.mjs";
import { CubicalPublication } from "./cubical-publication.mjs";
import { CubicalDeclarationTransaction } from "./cubical-transaction.mjs";
import { ScopePoints } from "./translator/scope-points.mjs";
import {CompilationBindings} from "./translator/compilation-bindings.mjs";
import { ReplayInputs, kernelReplayPolicy, applyKernelReplayPolicy } from "./cubical-replay-inputs.mjs";
import naturalSource from "./translator/unat-source.mjs";

// A property computed when first read, and then kept as a plain value.
function whenRead(object, key, compute) {
  const keep = (target, value) => Object.defineProperty(target, key, { value, writable: true, enumerable: true, configurable: true });
  return Object.defineProperty(object, key, { enumerable: true, configurable: true,
    get() { const value = compute(); keep(this, value); return value; }, set(value) { keep(this, value); } });
}

// Imports are source, loaded on demand. Every module has its own environment;
// closed native definitions have qualified names so shadowing cannot retarget
// an earlier checked reference. Unsupported declarations never become axioms.
export class CubicalProgram {
  constructor(module, readSource, options = {}) {
    const {onDeclarationStart,onDeclaration,collectReferences=true,collectScopes=false,collectGeneration=false,optimizations={},manageTransactions=true,
      searchFuel,declarationFuel,experimental,representation,bundledUNat=true,prelude,runtimeEvaluation=true}=options;
    this.options={...options};
    if(collectScopes&&!manageTransactions)throw new TypeError("Scope collection requires declaration transactions.");
    // The representation map τ to declared counterparts was the differential
    // fixtures' (H1 specification, 7.4), retired with them.
    if (representation !== undefined)
      throw Error("The representation option was removed with the differential fixtures: Nat, W and pushouts are source declarations.");
    // Declared types (H1) are on by default since their release; the option
    // that admitted them experimentally is gone.
    if (experimental !== undefined)
      throw Error("H1 is no longer experimental: declared types are on by default, so drop the experimental option.");
    // Fuel limits (web/translator/fuel.mjs), for a measurement or a test; the defaults otherwise.
    this.fuelLimits = Object.freeze(Object.fromEntries(Object.entries({searchFuel,declarationFuel}).map(([kind,limits])=>
      [kind,limits?Object.freeze({...limits}):undefined])));
    Object.assign(this.options,this.fuelLimits);
    this.kernel = new CubicalKernel(module);
    this.kernel.setOptimizations(optimizations);
    this.checker = new NativeCubicalElaborator(this.kernel);
    // Value forms are observed by the runtime unless this is false, which
    // leaves them to the kernel's head queries alone, for a comparison.
    this.checker.runtimeEvaluation = runtimeEvaluation;
    this.readSource = readSource;
    // Nothing is imported automatically. Structural unary clients import
    // unat, which a reader with no library can still load from
    // its bundled source unless bundledUNat is false.
    if (prelude !== undefined)
      throw Error("The prelude option was removed: no module is imported automatically, so a module imports unat itself; bundledUNat controls unat's bundled source.");
    this.bundledUNat=bundledUNat;
    this.onDeclarationStart = onDeclarationStart; this.onDeclaration = onDeclaration;
    this.collectReferences = collectReferences;
    this.collectScopes = collectScopes;
    this.collectGeneration = collectGeneration;
    this.compilationBindings=new CompilationBindings(options.scopeRevision??globalThis.crypto.randomUUID());
    this.checker.compilationBindings=this.compilationBindings;
    this.scopePoints = new Map();
    this.scopeRevision = null;
    this.scopeRecorder = null;
    this.scopeReady = false;
    this.manageTransactions = manageTransactions;
    this.localSymbols = {}; this.declarationBindings = new Map();
    this.declarationReferences = new Map();
    // The program's declarations by binding, and nothing else: whatever
    // looks a declaration up reads this table. An assumption is no
    // declaration. What a rendered text calls each name is `displaySymbols`:
    // a declaration as here, and an assumption by its label, as the
    // checker's displays show it. Only rendering reads that table.
    const checker = this.checker, symbols = this.symbols = {};
    this.displaySymbols = new Proxy(symbols, { get: (declarations, name) => typeof name === "string" && checker.assumptionLabels.has(name)
      ? { binding: name, name: checker.assumptionLabels.get(name), kind: "axiom" } : declarations[name] });
    this.modules = new Map(); this.views = new Map();
    this.publications = new Map();
    this.generation = new Map();
    this.sourceAsts = new Map();
    this.simpRegistries = new Map();
    this.gaps = []; this.evaluations = []; this.prints = []; this.links = []; this.sources = {}; this.completed = 0;
    // What each directive (evaluate, print, simp_rule, simp_set) spent (fuel.mjs).
    this.directiveFuel = [];
    // Proof statements of each checked module, with their goals (see steps()).
    this.moduleSteps = new Map();
    this.failedImports = new Map();
    // Whether each module checked is the library's, imports included.
    this.libraryModules = new Map();
  }
  dispose() { this.scopeReady=false; this.kernel.dispose(); }
  assumptionSymbols() {
    return Object.fromEntries([...this.checker.assumptions].map(([binding, type]) => [binding, {
      binding, name: this.checker.assumptionLabels.get(binding) ?? binding, kind: "axiom", role: "explicit axiom",
      verified: true, type: cubicalText(type, this.displaySymbols, { dimensions: [] }), axioms: [binding],
      description: "An explicit logical assumption: a name with a type and no computation rule. Its full signature is shown in the Axioms section.",
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
    if (prepared.has(name) || discovery.reuseModules && this.modules.has(name)) return;
    try {
      if(text===null) {
        try { text=await this.readSource(name,importer); }
        catch(error) {if(name!=="unat"||!this.bundledUNat)throw error;}
        // Readers with no standard library (such as an exported inspection)
        // can still load unat's bundled source.
        if(name==="unat"&&this.bundledUNat&&!text)text=naturalSource;
      }
      let ast;
      try {ast=parse(text);requireTestMode(ast,this.options.testMode&&!discovery.reuseModules);}
      catch(error) {
        error.kind??="parse";
        throw new SourceUnit({checker:this.checker,source:text,moduleName:name}).locate(error,null);
      }
      // Provenance only names axioms: a module whose provenance cannot be
      // read, as when library/ is unreachable, is the text it is, with
      // qualified labels, and is never lost for it.
      let own = false;
      try { own = await this.readSource.fromLibrary?.(name, text) ?? false; } catch { own = false; }
      const entry = { text, ast, library: false };
      prepared.set(name, entry);
      if(!this.modules.has(name))discovery.total += ast.declarations.length;
      onProgress({ completed: this.completed, total: null, current: name,
        phase: "loading", unit: "declarations", instructions: this.checker.steps });
      for (const dependency of ast.imports) await this.discover(discovery, dependency, null, name, onProgress);
      // Whether it is the library's, as library/ holds it, and so is every
      // module it reads, transitively: only then do its axioms take their
      // bare names as labels, since an axiom's statement is read through its
      // imports.
      entry.library = own && ast.imports.every(dependency => prepared.get(dependency)?.library
        ?? this.libraryModules.get(dependency) ?? false);
      const refused = await this.readSource.checkImports?.(name, ast.imports);
      if (refused) prepared.set(name, { error: new Error(refused) });
    } catch (error) { prepared.set(name, { error }); }
  }
  // The references a checked declaration's elaboration reported: its local
  // bindings and their views, each name's binding, and, in the checked
  // module, its source links.
  prepareReferences(name, main, declaration, result, pending) {
    const binders=[],locals=new Map(),localKey=alias=>JSON.stringify([alias.key,alias.start]);
    const references=[],declarationLinks=[];
    const record={binding:`${name}__${result.name}`,binders,references,links:declarationLinks,views:new Map(),localSymbols:{}};
    // Generated syntax stands at its declaration's name, a theory's or an
    // initial/free model's, and its links, and the marks elaboration builds
    // for it, would hide the name's own. Syntax written elsewhere, as an
    // initial/free header's parameters, theory and generator type, links as
    // written; synthetic syntax, as what a theory's expansion places at its
    // name, links nowhere.
    const generated = declaration.generated ? declaration.name : null;
    const written = node => !node.synthetic && ownsSource(node,name) && !(generated && node.start >= generated.start && node.start < generated.end);
    for (const [index,item] of pending.entries()) {
      if (!Number.isInteger(item.node.start)) continue;
      let head = item.term; while (head.tag === "App" || head.tag === "LApp") head = head.fn;
      const source = item.aliases?.find(alias => alias.key === item.node.localBindingKey);
      const declared = !source && !item.node.expressionSite && item.node.declarationBinding;
      const definition = !!declared || head.tag === "DefRef" && !source && !item.node.expressionSite;
      const binding = definition ? declared || head.name : JSON.stringify(["view",name,result.name,index]);
      if(item.node.isBinding) {
        binders.push({...item,binding});
        if(source)locals.set(localKey(source),binding);
      }
      const aliases=item.aliases?.map(alias=>({...alias,binding:locals.get(localKey(alias))}));
      const origin=source?.origin??item.node.origin,sourceModule=origin?.module??name;
      references.push({start:item.node.start,end:item.node.end,name:item.node.name,binding,written:written(item.node)});
      if (!definition) record.views.set(binding, { ...item,aliases,module:name,
        sourceBinding:source?locals.get(localKey(source)):null });
      if (!definition) record.localSymbols[binding] = { binding, name: item.node.name,
        role: item.node.role ?? (item.term.tag === "Var" ? "Local assumption" : "Local definition"), verified: true,
        expansion: item.node.expansion, description: item.node.description,
        definitionStart: source?.start ?? item.node.start,
        ...(origin?{origin}:{}),
        ...(sourceModule === main ? {} : { sourceModule,sourceName:this.sourceAsts.get(sourceModule)?.declarations
          .find(d=>d.start<=(source?.start??item.node.start)&&(source?.start??item.node.start)<d.end)?.name.text }) };
      if (name === main && written(item.node)) {
        const link={ name: item.node.name, binding, start: item.node.start,
        end: item.node.end, definitionStart: source?.start, role: item.node.role ?? (declared ? "inductive" : definition ? "definition" : "local"),
        expansion: item.node.expansion, description: item.node.description,
        freeze:item.node.freeze,traceParent:item.node.traceParent };
        declarationLinks.push(link);
      }
    }
    for(const link of declarationLinks)if(link.role==="simplification witness")
      link.rewriteSteps=declarationLinks.filter(step=>step.role==="simplification step"
        &&step.traceParent===link.start).map(step=>({name:step.name,binding:step.binding,
          role:step.role,description:step.description,start:step.start,end:step.end}));
    return record;
  }
  publishReferences(record) {
    this.declarationBindings.set(record.binding,record.binders);
    this.declarationReferences.set(record.binding,record.references);
    for(const [key,value] of record.views)this.views.set(key,value);
    Object.assign(this.localSymbols,record.localSymbols);
    for(const link of record.links)this.links.push(link);
  }
  // Authored location is independent of the module publishing a declaration.
  // Both checked symbols and blocked generated families use this target.
  sourceSite(syntax,declaring) {
    const module=syntax.origin?.module??syntax.name?.origin?.module??declaring;
    const start=syntax.start,end=syntax.end;
    const name=this.sourceAsts.get(module)?.declarations.find(d=>d.start<=start&&start<d.end)?.name.text;
    return {definitionStart:start,definitionSite:{module,start,end,name},
      description:leadingDocumentation(this.sources[module]??"",start)?.text??""};
  }
  // A module's results: its simplification rules, its directives' fuel and
  // gaps, and each declaration's symbol, gap and, in the checked module, link.
  // `failure` adds a failed import's note to a reason.
  recordModule(name, main, ast, result, failure) {
    this.simpRegistries.set(name,result.simpRegistry);
    this.publications.set(name,result.publications??[]);
    if(this.collectGeneration)this.generation.set(name,result.generation??[]);
    for(const directive of result.directives??[]) {
      this.directiveFuel.push({ module: name, kind: directive.kind, name: directive.name, start:directive.start, searchFuel: directive.searchFuel ?? null });
      if(directive.status!=="checked")
        this.gaps.push({module:name,name:`${directive.kind} ${directive.name}`,
          reason:directive.reason,code:diagnosticCode(directive.reason),directive:true,
          start:directive.errorStart??directive.start,end:directive.errorEnd,declarationStart:directive.start,
          ...(directive.blockedBy?{blockedBy:directive.blockedBy}:{}),...(directive.cause?{cause:directive.cause}:{}),
          ...(directive.failure?{failure:directive.failure}:{}),...(directive.diagnostic?{diagnostic:directive.diagnostic}:{})});
      else if(directive.kind==="evaluate")
        this.evaluations.push({module:name,name:directive.name,value:directive.normalText,start:directive.start});
      else if(directive.kind==="print")
        this.prints.push({module:name,name:directive.name,text:directive.text,start:directive.start,axioms:directive.axioms??[],
          ...(directive.valueForm?{valueForm:directive.valueForm}:{})});
    }
    const byName = new Map(ast.declarations.map(d => [d.name.text, d]));
    for (const d of result.declarations) {
      if (d.duplicate) {
        this.gaps.push({module:name,name:d.name,duplicate:true,reason:d.reason,code:diagnosticCode(d.reason),
          start:d.errorStart,end:d.errorEnd,declarationStart:d.syntax.start,declarationEnd:d.syntax.end,
          ...(d.diagnostic?{diagnostic:d.diagnostic}:{})});
        continue; // The original symbol and its inspection data still own the name.
      }
      // A theory's declarations bring their generated syntax (theories.mjs).
      const syntax = d.syntax ?? byName.get(d.name), binding = `${name}__${d.name}`;
      const verified = d.status === "checked-native-cubical";
      const reason = verified ? d.reason : failure(d.reason);
      const info = { name: d.name, binding, kind: syntax.kind, role: syntax.kind, verified,
        status: d.status, reason, ...(verified ? {} : { code: diagnosticCode(reason) }), errorStart: d.errorStart, errorEnd: d.errorEnd,
        rewriteWork: d.rewriteWork, searchFuel: d.searchFuel, failure: d.failure ?? null,
        ...(d.diagnostic?{diagnostic:d.diagnostic}:{}),
        ...(d.blockedBy?{blockedBy:d.blockedBy}:{}),...(d.failedMember?{failedMember:d.failedMember}:{}),...(d.cause?{cause:d.cause}:{}),
        axioms: d.native?.axioms ?? [],
        // Kernel extensions under review that the result relies on, shown
        // apart from assumptions; computable accepts them. None is under
        // review since H1's release, so this list is empty.
        extensions: d.native?.extensions ?? [], start: syntax.start, end: syntax.end,
        ...this.sourceSite(syntax,name),
        ...(name === main ? {} : { sourceModule: name, sourceName: d.name }) };
      const notationPrinting=this.checker.notationPrinting;
      Object.defineProperty(info,"printing",{get:()=>notationPrinting.get(binding)});
      // Like printing metadata, a checked selection belongs to this session;
      // its identity must not leak into serialized declaration results.
      Object.defineProperty(info,"notation",{value:d.notation??{selection:null,selectionIdentity:null}});
      // The type's text, written when first read: the pages and the
      // inspector show it, a check does not. Its names are the program's
      // symbols' and the declaration's own for its variables; none of the
      // program's is a local one, so they are read through rather than
      // copied, which each declaration did, all of them.
      if (verified) {
        // A universe variable's source name stands for U(x): it names x.
        const symbols = this.displaySymbols, variables = Object.fromEntries((this.declarationBindings.get(binding) ?? [])
          .map(item => [item.term.tag === "Var" ? item.term.name
            : item.term.tag === "U" && item.term.level?.tag === "Var" ? item.term.level.name : null, { name: item.node.name }])
          .filter(([variable]) => variable));
        whenRead(info, "type", () => cubicalText(d.type, Object.assign(Object.create(symbols), variables), { dimensions: [] }));
      } else info.type = reason;
      this.symbols[binding] = info;
      if (!verified) this.gaps.push({ module: name, name: d.name,
        reason, code: info.code, start: d.errorStart, end: d.errorEnd,
        ...(d.diagnostic?{diagnostic:d.diagnostic}:{}) });
      // A theory's name links to its models' type, a field's to its projection.
      // An initial/free name links to its declared type, whose generated
      // syntax this is. The generated definitions remain symbols, inspectable
      // by name and at their written uses.
      if (name === main && ownsSource(syntax.name,name) && syntax.generated?.role !== "make" && !(syntax.generated?.initial && syntax.kind !== "inductive"))
        this.links.push({ ...info, start: syntax.name.start, end: syntax.name.end });
    }
  }
  // Corpus clients choose their ordered entry modules and keep ownership of
  // this program, its readers, observers and resource limits.
  checkModules(modules, main, onProgress) {
    return this.check(modules.map(name => `import ${name};`).join("\n"), main, onProgress);
  }
  async check(source, main = "current", onProgress = () => {}, {reuseModules=false} = {}) {
    // A module's name is an identifier, as an import's is, since
    // module::name spells each of its declarations
    // (reference/first-proof.html#qualified-names); a file's is
    // moduleOfFile's (tools/module-sources.mjs).
    if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(main)) throw new TypeError(`A module's name is an identifier, as my_proof is: ${JSON.stringify(main)} is not.`);
    // Discover the source graph before checking. This only reads and parses
    // source; it does not run the mathematical library or count repeated
    // imports twice.
    // Scope instances describe a complete ordered source check. The module
    // REPL's cached, in-memory extensions keep that source snapshot intact;
    // their own entries do not publish source scope points.
    const collectScopes=this.collectScopes&&!reuseModules;
    if(collectScopes)this.scopeReady=false;
    if(collectScopes&&!this.manageTransactions)throw new TypeError("Scope collection requires declaration transactions.");
    this.readSource.beginCheck?.();
    const discovery = { prepared: new Map(), total: this.completed, reuseModules };
    await this.discover(discovery, main, source, null, onProgress);
    const { prepared } = discovery;
    // Rechecking an edited module invalidates every dependent artifact and
    // native handle. The discovered source graph, rather than aliases or a
    // cached successful module, determines whether the session is reusable.
    const invalidated=(collectScopes&&this.modules.size>0)||[...prepared].some(([name,entry])=>{
      if(this.modules.has(name))return entry.error||entry.text!==this.sources[name];
      // A failed read must be retried through its importers. An interrupted
      // load may also have committed declarations before the active group.
      return !reuseModules&&(this.failedImports.has(name)||this.sources[name]!==undefined);
    });
    if(invalidated) {
      const policy=kernelReplayPolicy(this.kernel);
      const replacement=new CubicalProgram(this.kernel.module,this.readSource,this.options);
      this.dispose(); Object.assign(this,replacement);
      applyKernelReplayPolicy(this.kernel,policy);
      discovery.total=[...prepared.values()].reduce((sum,entry)=>sum+(entry.ast?.declarations.length??0),0);
      onProgress({completed:0,total:discovery.total,current:main,phase:"loading",unit:"declarations",instructions:0});
    }
    if(collectScopes) {
      this.scopeRevision=this.compilationBindings.revision;
      this.scopePoints=new Map();
      this.scopeSources=Object.freeze(Object.fromEntries([...prepared].filter(([,entry])=>typeof entry.text==="string")
        .map(([name,entry])=>[name,entry.text])));
      this.scopeRecorder=new ScopePoints(this.scopeRevision,{onPoint:point=>this.scopePoints.set(point.id,point),
        probe:this.options.scopeProbe??null,target:this.options.scopeTarget??null,compilation:this.compilationBindings});
      this.scopeReplay=new ReplayInputs({revision:this.scopeRevision,main,prepared,readSource:this.readSource,
        fuelLimits:this.fuelLimits,kernel:this.kernel,collectReferences:this.collectReferences,testMode:!!this.options.testMode});
    }
    const scopeRecorder=collectScopes?this.scopeRecorder:null;
    let total = discovery.total;
    // Imports that failed in this check, used or not: any makes it incomplete.
    const failedHere = new Set();
    const visiting = new Set();
    const load = async (name, text = null) => {
      if (visiting.has(name)) throw new Error(`Cyclic source import: ${name}`);
      if (this.modules.has(name)) return this.modules.get(name);
      visiting.add(name);
      let ast, library;
      try {
        const entry = prepared.get(name);
        if (!entry) throw new Error(`Source was not discovered: ${name}`);
        if (entry.error) throw entry.error;
        ({ text, ast, library } = entry);
        this.libraryModules.set(name, library);
      }
      catch (error) {
        if (name === main) throw error;
        this.gaps.push({ module: name, reason: error.message, code: diagnosticCode(error.message),
          ...(Number.isInteger(error.offset)?{start:error.offset,end:error.sourceEnd}:{}),
          ...(error.diagnostic?{diagnostic:error.diagnostic}:{}) });
        this.failedImports.set(name, error.message);
        failedHere.add(name);
        visiting.delete(name); return new Map();
      }
      this.sources[name] = text;
      this.failedImports.delete(name);
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
      const checker = this.checker;
      let pending = [];
      const publication=new CubicalPublication(this);
      let current = null;
      // A module of a revision before L2.10j, as the migration verifier reads
      // one, keeps its name-based operators and numerals (translate.mjs).
      const translator = new Translator({ normalize: false, checker,definitionModule:name,libraryModule:library,testMode:!!this.options.testMode,simpRegistry,moduleName:name,sources:this.sources,collectGeneration:this.collectGeneration,
        scopePoints:scopeRecorder,compilationBindings:this.compilationBindings,
        onDirectiveStart:collectScopes?directive=>{
          this.onDirectiveStart?.(name,directive);
          this.scopeReplay.record("directive-start",name,directive,this.kernel);
        }:null,
        onDirective:collectScopes?(directive,result)=>{
          this.onDirective?.(name,directive,result);
          this.scopeReplay.record("directive-end",name,directive,this.kernel,result);
        }:null,
        nameBased: collectScopes?this.scopeReplay.modules[name].nameBased:this.readSource.nameBased?.(name)??false,
        inspectSignature: binding => this.signatureText(binding, checker.notation),
        ...Object.fromEntries(Object.entries(this.fuelLimits).filter(([, limits]) => limits)),
        onStep: step => publication.statements.push({ ...step, declaration: current }),
        onPublicationStart: () => publication.begin(true),
        onPublicationEnd: (_group,accept) => publication.finish(accept),
        // A theory's expansion adds declarations the source does not write,
        // and a failed type of models takes the rest of its theory off: the
        // total follows both, so that it is never below what is done and
        // ends at it. Each change is reported, as the last event may be one,
        // when a theory whose type of models fails ends the source.
        onQueued: change => {
          total += change;
          onProgress({ completed: this.completed, total, current: current && `${name}.${current}`,
            phase: "checked", unit: "declarations", instructions: checker.steps });
        },
        onDeclarationStart: declaration => {
          current = declaration.name.text;
          publication.beginDeclaration();
          this.onDeclarationStart?.(name, declaration, checker);
          onProgress({ completed: this.completed, total,
            current: `${name}.${declaration.name.text}`, phase: "checking", unit: "declarations", instructions: checker.steps });
          if(collectScopes)this.scopeReplay.record("start",name,declaration,this.kernel);
        },
        onReference: this.collectReferences ? (node, term, context, dimensions, aliases) => pending.push({ node, term, context, dimensions, aliases }) : null,
        onDeclaration: (declaration, result) => {
          this.onDeclaration?.(name, declaration, result, checker);
          const accepted=result.status === "checked-native-cubical";
          this.completed++;
          if(accepted)publication.records.push(this.prepareReferences(name,main,declaration,result,pending));
          pending = [];
          onProgress({ completed: this.completed, total,
            current: `${name}.${result.name}`, phase: "checked", unit: "declarations", instructions: checker.steps });
          if(collectScopes)this.scopeReplay.record("end",name,declaration,this.kernel,result);
          publication.endDeclaration(accepted);
        },
      });
      let result;
      try {result=translator.translate(text,env);}
      catch(error) { publication.abort(); throw error; }
      this.recordModule(name, main, ast, result, failure);
      this.moduleSteps.set(name, publication.statements);
      this.modules.set(name, result.env); visiting.delete(name);
      return result.env;
    };
    await load(main, source);
    if(collectScopes)this.scopeReady=true;
    const all = Object.values(this.symbols), outputs = all.filter(d => !d.sourceModule);
    // A check is complete when every declaration of every module it holds
    // checks, an import's as the main module's, every directive does, and
    // every import loads.
    const held = new Set(prepared.keys()), checked = all.every(d => d.verified || !held.has(d.sourceModule ?? main));
    this.main = main;
    // Goals are shown on demand; posting the result to the page reads them.
    let steps = null;
    const program = this;
    return this.metadata = {
      get steps() { return steps ??= program.steps(main); }, backend: "cubical", mode: "mathematical", source, outputs,
      imports: all.filter(d => d.sourceModule), symbols: [...all, ...Object.values(this.assumptionSymbols())], assumptionLabels: Object.fromEntries(this.checker.assumptionLabels), declarations: outputs, links: this.links,
      declarationCount: total, instructionCount: this.checker.steps, axiomCount: new Set(outputs.flatMap(d => d.axioms)).size, gaps: this.gaps,
      evaluations: this.evaluations, prints: this.prints, directiveFuel: this.directiveFuel,
      publications:Object.fromEntries(this.publications),
      // Unused bindings that can be removed, in the checked module only; a
      // fresh parse, since elaboration annotates the syntax it checks.
      warnings: lint(source),
      complete: outputs.length > 0 && outputs.every(d => d.verified) && checked
        && !this.gaps.some(gap=>gap.directive||gap.duplicate) && failedHere.size === 0, sources: this.sources };
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
  // By default it prints in the checked selection at its declaration.
  signatureView(binding, notation = this.symbols[binding]?.notation ?? {selection:null,selectionIdentity:null}) {
    const signature = this.signature(binding);
    if (!signature) return null;
    const { eliminator } = signature;
    const terms = [signature.former, ...signature.constructors.map(c => c.type),
      ...(eliminator ? [eliminator.motiveType, ...eliminator.clauses.map(c => c.type)] : [])];
    const texts = this.checker.displayTexts(this.qualifyGenerated(terms), [], { width: Infinity, limit: 1000000, notation });
    let next = 0;
    const text = () => texts[next++];
    return { ...signature, former: text(),
      constructors: signature.constructors.map(c => ({ ...c, name: c.generated ? `${signature.name}.squash` : c.name, type: text() })),
      eliminator: eliminator && { motive: `${eliminator.motive} : ${text()}`,
        universe: eliminator.universe, error: eliminator.error ?? null,
        clauses: eliminator.clauses.map(c => ({ constructor: c.constructor, name: c.name, type: text() })) } };
  }
  // A declared type's signature on one line, as `print(inspect(T));` shows
  // it: what the CLI's inspect shows, each constructor and clause ended by `;`,
  // in the notation selected where it is shown.
  signatureText(binding, notation) {
    const view = this.signatureView(binding, notation);
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
        ...this.checker.displayGoal(record.goal.scope.shownContext([record.goal.target, built]), record.goal.scope.dimensions,
          record.goal.target, built, { width: 400, notation: notationForScope(record.goal.scope) }) };
    }).sort((a, b) => a.start - b.start);
  }
  // Check one more module on top of the loaded ones, as a REPL entry does,
  // and report only what it added. The program keeps presenting its main
  // module: inspection, export and metadata are unchanged.
  // The notation a module's declaration prints in: what the file-level uses
  // before it select (L2.10j).
  selectionOf(module, name) {
    return selectionName(this.sourceAsts.get(module)?.declarations.find(d => d.name.text === name)?.uses);
  }
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
      // A REPL entry extends its immutable session snapshot; its previous
      // entries are in-memory modules, not files to reload from the reader.
      await this.check(source, name, () => {}, {reuseModules:true});
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
    else if (this.checker.assumptions.has(this.checker.axioms.get(binding) ?? binding)) {
      // An axiom definition is inspected as the assumption it states.
      const name = this.checker.axioms.get(binding) ?? binding;
      term = { tag: "Var", name }; expected = this.checker.assumptions.get(name);
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
    // A normal form on request, stuck definitions folded (folded-normal-forms.md).
    if (normalize) checked.term = this.checker.syntax.decode(this.kernel.normalizeFolded(checked.expression), dimensions);
    const bindings = this.declarationBindings.get(binding) ?? [];
    const aliases = local?.aliases ?? [];
    const symbols = { ...this.symbols, ...this.localSymbols, ...this.generatedSymbols(), ...this.assumptionSymbols() };
    const variableNames = Object.fromEntries([
      ...bindings.map(item => ({ term: item.term, name: item.node.name, binding: item.binding })),
      ...aliases,
    // A universe variable's source name stands for the universe U(x), so it
    // names the level variable x.
    ].map(alias => ({ ...alias, variable: alias.term.tag === "Var" ? alias.term.name
      : alias.term.tag === "U" && alias.term.level?.tag === "Var" ? alias.term.level.name : null }))
      .filter(alias => alias.variable).reverse().map(alias => [alias.variable, { name: alias.name, binding: alias.binding }]));
    for (const [name, value] of Object.entries(variableNames)) symbols[name] = { ...value, local: true };
    const view = { backend: "cubical", name: binding,
      expression: checked.term, type: checked.type,
      expressionText: cubicalText(checked.term, this.displaySymbols, { dimensions }), typeText: cubicalText(checked.type, this.displaySymbols, { dimensions }),
      dimensions: [...dimensions], context: context.map(([name, type]) => ({ name,
        label: variableNames[name]?.name ?? this.checker.assumptionLabels.get(name) ?? name,
        binding: variableNames[name]?.binding ?? (this.checker.assumptions.has(name) ? name : null), type })), symbols,
      checkingSteps: checked.checkingSteps, reductionSteps: checked.reductionSteps, axioms: [...assumptions.keys()],
      // The kernel extensions the inspected term relies on, apart from assumptions.
      extensions };
    view.sourceBinding = local?.sourceBinding;
    view.contextEntry = local ? {module:local.module,scope:local.node.contextScope??null} : null;
    const simplifiedType = simplifyTypeApplications(view.type);
    const presentation = simplifiedType === view.type ? view
      : checkReduction(this, view, "type", simplifiedType).view;
    view.folded = foldedInspection(presentation, aliases);
    view.expressionText = cubicalText(view.folded.expression, symbols, { dimensions: [...dimensions.keys()] });
    view.typeText = cubicalText(view.folded.type, symbols, { dimensions: [...dimensions.keys()] });
    // The declaration a view states: a declaration's own, in its module, or
    // an assumption's axiom definition, by the origin the checker recorded,
    // never by a label.
    const origin = this.checker.assumptionOrigins.get(binding);
    const stated = local ? null : info?.verified ? { module: info.sourceModule ?? this.main, name: info.name, binding }
      : origin?.kind === "axiom" ? { module: origin.module, name: origin.declaration, binding: origin.binding } : null;
    if (stated) {
      const { module } = stated;
      const declaration = this.sourceAsts.get(module)?.declarations.find(d => d.name.text === stated.name);
      if (declaration) view.statement = sourceStatement(this.sources[module], declaration, this.declarationReferences.get(stated.binding));
      // Keep proof blocks compact, with their checked bodies available to inspect.
      if (declaration?.body) view.folded.reference = { tag: "DefRef", name: binding };
      if (!view.statement) {
        let conclusion = cubicalMathTree(view.folded.type, symbols, undefined, { dimensions }), raw = view.folded.type;
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
    // A parameter shows its source name, as in the statement and the context.
    view.boundary = this.squareBoundary(view.type, dimensions, new Map(Object.entries(variableNames).map(([variable, { name }]) => [variable, name])));
    return view;
  }
  // A square's boundary, for the inspector (L2.8): where a type, under its
  // parameters, is Square(a0_, a1_, a_0, a_1) of library/squares, its
  // four edges and four corners, as messages show them in the context of
  // `dimensions`, with the free variables `names` gives shown by those
  // names; or null.
  squareBoundary(type, dimensions, names = new Map()) {
    let body = type;
    while (body?.tag === "Pi" || body?.tag === "LPi") body = body.body;
    const args = [];
    for (; body?.tag === "App"; body = body.fn) args.unshift(body.arg);
    if (body?.tag !== "LApp" || body.fn?.tag !== "DefRef" || body.fn.name !== "squares__Square" || args.length !== 9) return null;
    const [, a00, a01, a10, a11, left, right, bottom, top] = args;
    const [corner00, corner01, corner10, corner11, ...edges] = this.checker.displayTexts([a00, a01, a10, a11, left, right, bottom, top], dimensions, { width: 120, names });
    return { corners: { a00: corner00, a01: corner01, a10: corner10, a11: corner11 },
      edges: { left: edges[0], right: edges[1], bottom: edges[2], top: edges[3] } };
  }
  export(binding = null, side = "expression") {
    const view = binding ? this.inspect(binding) : null;
    return { format: "thth-cubical", version: 1, main: this.main,
      source: this.metadata.source, sources: this.sources, binding, side,
      // Syntax is informational. Import must replay the supplied source first.
      ...(view ? { expression: view.expression, type: view.type, context: view.context } : {}) };
  }
}
