// A contextual session retains source and binding correspondence only.
// Every request reconstructs the full ordered prefix in a new kernel, runs
// synchronously at the selected entry, then unwinds and disposes that kernel.
import { isResourceLimit } from "./resource-limits.mjs";
import {CubicalProgram} from "./cubical-program.mjs";
import {replayReader,replayPolicyCallbacks,kernelReplayPolicy,applyKernelReplayPolicy} from "./cubical-replay-inputs.mjs";
import {parse,reservedReferences} from "./cubist/parser.mjs";
import {BindingAdapter,bindingResolution} from "./cubist/bindings.mjs";
import {bindingInputs,sourceSimpSets} from "./translator/binding-module.mjs";
import {declaredIn,qualifiedLexical} from "./translator/qualified-names.mjs";
import {resolveBindingSyntax,lowerBindingSyntax,lowerBindingReference} from "./cubist/binding-syntax.mjs";
import {NameSupply} from "./translator/names.mjs";
import {syntaxGraphBudget} from "./translator/syntax-graph.mjs";
import {ElaborationStop} from "./translator/control.mjs";
import {RECURSIVE} from "./translator/match.mjs";
import {notationContextKey} from "./translator/notation-context.mjs";
import {T,freeNames} from "./translator/core.mjs";
import {assumptionNote} from "./axiom-labels.mjs";
import {Goal} from "./translator/proof-goals.mjs";
import {Scope} from "./translator/elaboration.mjs";
import {replStatements} from "./repl-session.mjs";

const freeze=value=>{
  if(value&&typeof value==="object"&&!Object.isFrozen(value)) {
    Object.values(value).forEach(freeze);Object.freeze(value);
  }
  return value;
};
const failure=(kind,error,extra={})=>({kind,text:error.message??String(error),failure:error.kind??"other",...extra});
// The line that reports what a result relies on: every assumption its terms
// use, and every one the types of the local values and hypotheses they
// mention use (web/axiom-labels.mjs), or null for none.
function reliedOn(scope,subject,...terms) {
  const context=scope.context,pending=[...terms],types=[],seen=new Set();
  while(pending.length)for(const name of freeNames(pending.pop()))if(!seen.has(name)&&context.has(name)) {
    seen.add(name);types.push(context.get(name));pending.push(context.get(name));
  }
  return assumptionNote([...scope.checker.requiredAssumptions(...terms,...types).keys()],scope.checker.assumptionLabels,subject);
}
const unavailable=text=>({kind:"unavailable",text,failure:"context"});
const measure=kernel=>({time:performance.now(),work:kernel.work()});
const spent=(kernel,start)=>({elapsedMs:performance.now()-start.time,work:Object.fromEntries(
  Object.entries(kernel.work()).map(([key,value])=>[key,value-start.work[key]]))});
const help=[
  "TERM;                 evaluate a term in the selected context",
  "typeof TERM;          the checked type of a term",
  "evaluate TERM;        normalize a term, which may remain symbolic",
  "print(inspect(TERM)); inspect the checked term in kernel notation",
  "witness TERM;         read a closed truncation's witness and type",
  "let NAME := TERM;     add a checked scratch binding to this session",
  "/locals               visible and shadowed local bindings, types and origins",
  "/goal                 the active proof goal, or the expected expression type",
  "/prove { ... }        check a proof block against a scratch copy of the goal",
  "/clear                clear the console log",
  "/restart              forget this session's scratch bindings",
  "/help                 this list",
].join("\n");

function parsedEntry(entry) {
  const source=entry.replace(/^(\s*\/\/[^\n]*(\n|$))+/,"").trim().replace(/;\s*$/,"");
  if(["/locals","/goal","/help","help"].includes(source))return {kind:source.replace(/^\//,""),text:source,tree:[]};
  if(/^\/prove\s*\{/.test(source)) {
    const text=`def contextual_entry : Unit ${source.replace(/^\/prove\s*/,"")}`,ast=parse(text);
    if(ast.imports.length||ast.declarations.length!==1||(ast.items??ast.declarations).length!==1||!ast.declarations[0].body)
      throw new TypeError("Expected one proof block: /prove { ... }");
    return {kind:"prove",text,tree:ast.declarations[0].body};
  }
  if(source.startsWith("/"))throw new TypeError(`Unknown contextual command ${source.split(/\s/)[0]}. /help lists the commands.`);
  if(/^let\s/.test(source)) {
    // Parse the actual statement grammar, including annotations/local proofs.
    // A one-statement sequence gives its binder an identity without putting
    // that binder in scope in its own initializer.
    const ending=replStatements(source).rest?";":"";
    const text=`def contextual_entry : Unit { ${source}${ending} exact tt; }`;
    const ast=parse(text);
    if(ast.imports.length||ast.declarations.length!==1||(ast.items??ast.declarations).length!==1)
      throw new TypeError("Expected one scratch let.");
    const statements=ast.declarations[0].body;
    if(statements.length!==2||statements[0].kind!=="let")throw new TypeError("Expected one scratch let.");
    return {kind:"let",text,tree:[statements[0]]};
  }
  if(/^print\s*\(/.test(source)) {
    const text=source+";",ast=parse(text),items=ast.items??ast.declarations;
    if(ast.imports.length||items.length!==1||items[0].kind!=="print"||!["typeof","evaluate","inspect","witness"].includes(items[0].show))
      throw new TypeError("Expected print(typeof(...)), print(evaluate(...)), print(inspect(...)) or print(witness(...)).");
    // This console shows a term's weak head in its context; demand marks
    // ask a closed evaluation for more or less.
    if(items[0].mark)throw new TypeError("A demand mark asks a closed evaluation, in a file or the REPL; this console shows a term's weak head in its context.");
    return {kind:items[0].show,text,tree:items[0].value};
  }
  const termCommand=/^(typeof|evaluate|inspect|witness)\s+([\s\S]+)$/.exec(source);
  const text=termCommand?termCommand[2]:source;
  return {kind:termCommand?.[1]??"evaluate",text,tree:parse(text,true)};
}

// List actual introductions, not every value retained for captures. Resolution
// through the selected branch decides visibility; an older row remains an
// inspectable identity but never becomes a new source alias.
function localBindings(translator,scope,lexical,adapter,table) {
  const candidates=[],seen=new Set(),localRoles=new Set(["local","parameter","universe","dimension","pattern"]);
  for(const [label,resolution] of lexical.snapshot()) {
    if(label&&resolution.tag==="binding") {
      const binding=table.get(resolution.id);
      if(localRoles.has(binding.role))candidates.push({label,resolution,binding});
    } else if(resolution.tag==="opening-frame") {
      const activation=scope.slotOutcomes.activation(resolution.id),binding=table.get(resolution.id);
      for(const [label,resolution] of activation?.members??[])candidates.push({label,resolution,binding});
    }
  }
  const rows=[];
  for(const {label,resolution,binding} of candidates) {
    const resolved=scope.slotOutcomes.resolve(resolution),identity=JSON.stringify([label,resolved]);
    if(seen.has(identity))continue;
    seen.add(identity);
    const visible=JSON.stringify(scope.slotOutcomes.resolve(lexical.lookup(label)))===JSON.stringify(resolved);
    const entry={label,resolution:resolved,origin:binding.origin,visible,type:null};
    if(resolved.tag==="failure"||resolved.tag==="missing") {
      rows.push({...entry,reason:resolved.message??"This binding is unavailable."});continue;
    }
    const node=lowerBindingReference({kind:"bindingReference",resolution:resolved},adapter,scope.slotOutcomes);
    const value=node.kind==="name"?scope.env.get(node.name):null;
    if(value?.tag==="SourceOperand") {
      entry.deferred=true;entry.reason="Lazy notation operand; checked when used.";
    } else if(value?.tag==="Dimension")entry.type="Interval";
    else {
      const term=translator.term(node,scope);
      entry.type=translator.shownIn(scope.infer(term).type,scope);
      entry.value=translator.shownIn(term,scope);
    }
    rows.push(entry);
  }
  const group=visible=>rows.filter(row=>row.visible===visible).map(row=>
    `${row.label} : ${row.type??row.reason}${row.value&&row.value!==row.label?` := ${row.value}`:""}`
    +` (${row.origin.module}:${row.origin.start}-${row.origin.end})`);
  const visible=group(true),shadowed=group(false);
  return {kind:"locals",bindings:rows,text:["Visible locals:",...(visible.length?visible:["(none)"]),
    "Shadowed locals:",...(shadowed.length?shadowed:["(none)"])].join("\n")};
}

function copiedScope(scope,unit,names=null) {
  // SourceOperand and scoped syntax form a DAG of caller scopes. Copy their
  // values and recursion permissions together, but never their compiler units.
  // Every lazy evaluation spends this query's fuel and uses its name supply.
  // These copies exist only inside the synchronous isolated replay callback.
  const copies=new WeakMap(),budget=syntaxGraphBudget({maxVisits:names?250000:500000,
    checkDeadline:()=>unit.checker.kernel?.checkDeadline()});
  const copy=value=>{
    budget.tick();
    if(typeof value==="string")names?.add(value.replace(/:[01]$/,""));
    if(value===null||typeof value!=="object") {
      if(typeof value==="function")throw new TypeError("A contextual query cannot copy a compiler callback.");
      return value;
    }
    if(copies.has(value))return copies.get(value);
    let result;
    if(value instanceof Scope) {
      const caller=value===scope?unit:unit.with({source:value.unit.source,moduleName:value.unit.moduleName,
        bindingAdapter:value.unit.bindingAdapter,declaring:value.unit.declaring,blameSite:value.unit.blameSite});
      result=value.with({unit:caller,context:copy(value.context),env:copy(value.env),dimensions:copy(value.dimensions),
        sourceBindings:copy(value.sourceBindings),localSources:copy(value.localSources),evidence:copy(value.evidence),
        inheritedDefinitions:copy(value.inheritedDefinitions)});
      copies.set(value,result);return result;
    }
    if(value instanceof Map) {
      result=new Map();copies.set(value,result);
      for(const [key,entry] of value)result.set(copy(key),copy(entry));
    } else if(value instanceof Set) {
      result=new Set();copies.set(value,result);
      for(const entry of value)result.add(copy(entry));
    } else {
      if(!Array.isArray(value)&&![Object.prototype,null].includes(Object.getPrototypeOf(value)))
        throw new TypeError("A contextual query cannot copy an unknown live value.");
      result=Array.isArray(value)?[]:{};copies.set(value,result);
      for(const [key,entry] of Object.entries(value)) {
        // Match continuation syntax is not a recursive-call permission.
        if(value.tag==="Recursive"&&key==="site")continue;
        result[key]=copy(entry);
      }
    }
    return result;
  };
  return copy(scope);
}

function queryEnvironment(live,adapter,unit) {
  const env=new Map();
  for(const [id,value] of live.values)env.set(adapter.key(id),value);
  for(const [id,context] of live.contexts)env.set(notationContextKey(adapter.key(id)),context);
  const selected=live.contexts.get(live.lexical.selectedNotation());
  for(const [key,value] of selected??[])env.set(key,value);
  // These are translator permissions, never a destination spelling lookup.
  for(const key of [RECURSIVE,"\u0000superseded"])if(live.scope.env.has(key))env.set(key,live.scope.env.get(key));
  const scope=copiedScope(live.scope.with({env,sourceBindings:new Map()}),unit);
  const recursive=scope.env.get(RECURSIVE);
  if(recursive) {
    const key=live.keys.get(recursive.key??recursive.source);
    if(key)recursive.key=adapter.key(key);
    // Permissions refer to environment keys, not labels. Compiler-private
    // aliases are not callable from the query and carry no lexical binding.
    if(recursive.destructed)recursive.destructed=new Map([...recursive.destructed].flatMap(([key,value])=>{
      const id=live.keys.get(key),target=id&&adapter.key(id);
      // Source calls require the permission's alias to be the current value.
      // Several keys can name one ID; an obsolete alias must not overwrite
      // the introduced key's valid permission when those keys collapse.
      return target&&value.alias===scope.env.get(target)?[[target,value]]:[];
    }));
  }
  const localSources=new Map([...live.scope.localSources].flatMap(([key,source])=>live.keys.has(key)
    ?[[adapter.key(live.keys.get(key)),{...source,key:adapter.key(live.keys.get(key)),bindingId:live.keys.get(key)}]]:[]));
  return scope.with({localSources});
}

export class ContextualSession {
  #program;
  #registry;
  #point;
  #inputs;
  #history=[];
  #serial=globalThis.crypto.randomUUID();
  #closed=false;
  #queue=Promise.resolve();

  constructor(program,pointId) {
    const point=program.scopePoints.get(pointId);
    if(!program.scopeReady||!point)throw new TypeError("Select a scope from a completed source check.");
    this.#program=new WeakRef(program);
    this.#registry=new WeakRef(program.scopePoints);
    this.#point=point;
    this.#inputs=program.scopeReplay.snapshot();
  }
  get point() {return this.#point;}
  get accepted() {return Object.freeze([...this.#history]);}
  dispose() {this.#closed=true;}
  #stale() {
    const program=this.#program.deref();
    return this.#closed||!program?.kernel.handle||!program.scopeReady||program.scopePoints!==this.#registry.deref();
  }
  run(input) {
    const work=this.#queue.then(async()=>{
      const {statements,rest}=replStatements(input);
      if(rest)statements.push(rest);
      const results=[];
      // Each result, then the assumptions it relies on, if any.
      for(const entry of statements) {
        const {assumes,...answer}=await this.#request(entry);
        results.push(freeze(answer));
        if(assumes)results.push(freeze({kind:"info",text:assumes}));
      }
      return results;
    });
    this.#queue=work.catch(()=>{});
    return work;
  }
  async #request(entry) {
    if(this.#stale())return freeze(unavailable("This contextual session is stale or disposed. Open a context from the current check."));
    if(!this.#point.available)return freeze(unavailable(this.#point.reason));
    const original=this.#program.deref(),inputs=this.#inputs;
    let replay,answer=null,accepted=null;
    const costs={prefix:null,validation:null,history:null,query:null};
    replay=new CubicalProgram(original.kernel.module,replayReader(inputs),{...inputs.fuelLimits,
      bundledUNat:false,testMode:inputs.testMode,collectReferences:inputs.collectReferences,collectScopes:true,scopeRevision:inputs.revision,scopeTarget:this.#point.id,
      scopeProbe:(point,live)=>{
        if(point.id!==this.#point.id)return;
        costs.prefix=spent(replay.kernel,prefix);
        if(this.#stale())throw new ElaborationStop(unavailable("The source check changed while replay was loading."));
        if(JSON.stringify(point)!==JSON.stringify(this.#point))
          throw new ElaborationStop(unavailable("The selected scope did not reproduce its recorded context."));
        const table=replay.scopeRecorder.table,adapter=new BindingAdapter(table);
        const translator=live.translator.forkScope(live.scope,{normalize:false,...inputs.fuelLimits});
        const {sets:simpSets,captures}=sourceSimpSets(table,live.scope.unit.simpRegistry);
        const selectedPolicy=kernelReplayPolicy(replay.kernel);
        let scope,lexical=live.lexical;
        const validation=measure(replay.kernel);
        try {
          applyKernelReplayPolicy(replay.kernel,selectedPolicy);
          scope=queryEnvironment(live,adapter,translator.unit().declaration(translator.declarationFuel));
          scope=scope.aliases(structuredClone([...captures].map(([id,value])=>[adapter.key(id),value])));
          // Inferring even Unit derives every local type in order through
          // contextScope. A recorded lambda domain is not typing authority.
          scope.infer(T.unit);
          for(const target of [live.goal,live.expected].filter(Boolean))
            if(scope.nf(scope.infer(target).type).tag!=="U")throw new TypeError("The scope's target is not a checked type.");
        } catch(error) {
          throw new ElaborationStop(failure("unavailable",error,{stage:"validation"}));
        } finally {scope?.unit.fuel?.close();costs.validation=spent(replay.kernel,validation);}

        // The scope's module, for why a qualified name is available nowhere.
        const module=this.#point.origin.module,ast=replay.sourceAsts.get(module);
        const scopeModule={current:module,declaredHere:ast?declaredIn(ast):new Set(),imports:new Set(ast?.imports??[])};
        const execute=(source,index)=>{
          applyKernelReplayPolicy(replay.kernel,selectedPolicy);
          const parsed=parsedEntry(source),reserved=reservedReferences(parsed.text);
          // The entry's qualified names, from the scope's available values.
          const {adapter:entryAdapter,context,constructors}=bindingInputs(table,live.values,{reserved,
            lexical:[...lexical.snapshot(),...qualifiedLexical(parsed.tree,live.values,table,lexical.notations(),scopeModule)]});
          const owner=["contextual-session",this.#serial,"entry",String(index)],moduleName=owner.join("/");
          const syntax=resolveBindingSyntax(parsed.tree,{table,owner,context,constructors,simpSets,
            source:{revision:inputs.revision,module:moduleName}});
          const tree=lowerBindingSyntax(syntax,entryAdapter);
          const used=new Set();
          const names=new NameSupply({taken:name=>used.has(name)||scope.checker.assumptions.has(name)});
          const unit=translator.unit({source:parsed.text,moduleName,bindingAdapter:entryAdapter,names,
            declaring:live.scope.unit.declaring}).declaration(translator.declarationFuel);
          let current,result,extension=null;
          try {
            current=copiedScope(scope,unit,used);
            if(parsed.kind==="help")result={kind:"help",text:help};
            else if(parsed.kind==="locals")result=localBindings(translator,current,lexical,entryAdapter,table);
            else if(parsed.kind==="goal") {
              const goal=live.goal?translator.shownIn(live.goal,current):null;
              const expected=live.expected?translator.shownIn(live.expected,current):null;
              result={kind:"goal",goal,expected,text:goal?`Goal: ${goal}`:expected?`Expected type: ${expected}\nNo active proof goal.`:"No active proof goal or expected type."};
            } else if(parsed.kind==="prove") {
              if(!live.goal)throw new TypeError("This expression context has no active proof goal.");
              const proof=current.check(translator.block(tree,new Goal(live.goal,current)),live.goal);
              result={kind:"proof",text:`Checked against ${translator.shownIn(live.goal,current)}. Source unchanged.`,
                proof:translator.shownIn(proof,current),goal:translator.shownIn(live.goal,current)};
            } else if(parsed.kind==="let") {
              current=translator.bindLet(tree[0],current);
              const id=tree[0].target.bindingId,record=table.get(id),value=current.env.get(entryAdapter.key(id));
              const type=current.infer(value).type;
              result={kind:"defined",text:`${record.label} : ${translator.shownIn(type,current)}`,
                assumes:reliedOn(current,record.label,value,type)};
              extension=freeze({source,binding:record,resolved:JSON.stringify(syntax)});
              lexical=lexical.bind(record.label,bindingResolution(id));
              scope=current;
            } else if(parsed.kind==="inspect"||parsed.kind==="witness") {
              const {text}=translator.printed({show:parsed.kind,value:tree},current);
              const checked=current.infer(translator.term(tree,current));
              result={kind:parsed.kind==="inspect"?"inspection":"value",text,assumes:reliedOn(current,null,checked.term,checked.type)};
            } else {
              const term=translator.term(tree,current),checked=current.infer(term);
              const value=current.nf(parsed.kind==="typeof"?checked.type:checked.term);
              result={kind:parsed.kind==="typeof"?"type":"value",text:translator.shownIn(value,current),
                assumes:reliedOn(current,null,checked.term,checked.type)};
            }
            return {result:{...result,conditional:true,scope:this.#point.id,fuel:translator.fuelRecord(unit)},extension};
          } finally {unit.fuel.close();}
        };
        const history=measure(replay.kernel);
        try {
          for(const [index,saved] of this.#history.entries()) {
            try {
              const replayed=execute(saved.source,index).extension;
              if(JSON.stringify(replayed)!==JSON.stringify(saved))throw new TypeError("The scratch binding correspondence changed.");
            } catch(error) {
              throw new ElaborationStop(failure("unavailable",error,{stage:"history",entry:index+1,source:saved.source}));
            }
          }
        } finally {costs.history=spent(replay.kernel,history);}
        const query=measure(replay.kernel);
        try {
          const checked=execute(entry,this.#history.length);
          accepted=checked.extension;
          answer=checked.result;
        } catch(error) {answer=failure("error",error,{stage:"query"});}
        finally {costs.query=spent(replay.kernel,query);}
        // No term, Scope, checker or native handle crosses this boundary.
        throw new ElaborationStop(freeze(answer));
      }});
    const prefix=measure(replay.kernel);
    try {
      Object.assign(replay,replayPolicyCallbacks(inputs,replay.kernel,{onChangedResult:result=>{
        throw new ElaborationStop({kind:"unavailable",text:result.reason??"A declaration changed its result during replay.",
          failure:result.failure??"context",stage:"prefix"});
      }}));
      const result=await replay.check(inputs.modules[inputs.main].text,inputs.main);
      const stopped=result.outputs.concat(result.imports,result.gaps).find(output=>isResourceLimit(output.failure));
      answer=stopped?{kind:"unavailable",text:stopped.reason,failure:stopped.failure,stage:"prefix"}
        :unavailable("Replay did not reach the selected scope point.");
    } catch(error) {
      answer=error instanceof ElaborationStop?error.result:failure("unavailable",error,{stage:"prefix"});
    } finally {
      costs.prefix??=spent(replay.kernel,prefix);
      replay.dispose();
    }
    if(this.#stale())return freeze(unavailable("The source check changed while the query was running."));
    if(accepted&&answer.kind==="defined")this.#history.push(accepted);
    return freeze({...answer,costs});
  }
}
