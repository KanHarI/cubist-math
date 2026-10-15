// A contextual session retains source and binding correspondence only.
// Every request reconstructs the full ordered prefix in a new kernel, runs
// synchronously at the selected entry, then unwinds and disposes that kernel.
import {CubicalProgram} from "./cubical-program.mjs";
import {replayReader,replayPolicyCallbacks,kernelReplayPolicy,applyKernelReplayPolicy} from "./cubical-replay-inputs.mjs";
import {parse,reservedReferences} from "./cubist/parser.mjs";
import {BindingAdapter,bindingResolution} from "./cubist/bindings.mjs";
import {bindingInputs} from "./translator/binding-module.mjs";
import {resolveBindingSyntax,lowerBindingSyntax} from "./cubist/binding-syntax.mjs";
import {NameSupply} from "./translator/names.mjs";
import {syntaxNames} from "./translator/syntax-graph.mjs";
import {ElaborationStop} from "./translator/control.mjs";
import {RECURSIVE} from "./translator/match.mjs";
import {T} from "./translator/core.mjs";
import {replStatements} from "./repl-session.mjs";

const limits=new Set(["fuel","budget","deadline"]);
const freeze=value=>{
  if(value&&typeof value==="object"&&!Object.isFrozen(value)) {
    Object.values(value).forEach(freeze);Object.freeze(value);
  }
  return value;
};
const failure=(kind,error,extra={})=>({kind,text:error.message??String(error),failure:error.kind??"other",...extra});
const unavailable=text=>({kind:"unavailable",text,failure:"context"});
const measure=kernel=>({time:performance.now(),work:kernel.work()});
const spent=(kernel,start)=>({elapsedMs:performance.now()-start.time,work:Object.fromEntries(
  Object.entries(kernel.work()).map(([key,value])=>[key,value-start.work[key]]))});

function parsedEntry(entry) {
  const source=entry.replace(/^(\s*\/\/[^\n]*(\n|$))+/,"").trim().replace(/;\s*$/,"");
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
  const command=/^(typeof|evaluate)\s+([\s\S]+)$/.exec(source);
  const text=command?command[2]:source;
  return {kind:command?.[1]??"evaluate",text,tree:parse(text,true)};
}

function copiedScope(scope,unit) {
  // Copy the maps and their mutable recursion/proof records together so
  // fixed-argument correspondences keep their internal sharing. Native
  // caches are outside these descriptions and must be re-derived.
  const data=structuredClone({context:[...scope.context],env:[...scope.env],dimensions:[...scope.dimensions],evidence:scope.evidence});
  return scope.with({unit,context:new Map(data.context),env:new Map(data.env),dimensions:new Map(data.dimensions),
    sourceBindings:new Map(),localSources:new Map(scope.localSources),evidence:data.evidence});
}

function queryEnvironment(live,adapter,unit) {
  const data=structuredClone({context:[...live.scope.context],env:[...live.scope.env],values:[...live.values],
    dimensions:[...live.scope.dimensions],evidence:live.scope.evidence});
  const original=new Map(data.env),values=new Map(data.values),env=new Map();
  for(const [id,value] of values)env.set(adapter.key(id),value);
  // These are translator permissions, never a destination spelling lookup.
  for(const key of [RECURSIVE,"\u0000superseded"])if(original.has(key))env.set(key,original.get(key));
  const recursive=env.get(RECURSIVE);
  if(recursive) {
    const key=live.keys.get(recursive.key??recursive.source);
    if(key)recursive.key=adapter.key(key);
    // Permissions refer to environment keys, not labels. Compiler-private
    // aliases are not callable from the query and carry no lexical binding.
    if(recursive.destructed)recursive.destructed=new Map([...recursive.destructed].flatMap(([key,value])=>
      live.keys.has(key)?[[adapter.key(live.keys.get(key)),value]]:[]));
  }
  const localSources=new Map([...live.scope.localSources].flatMap(([key,source])=>live.keys.has(key)
    ?[[adapter.key(live.keys.get(key)),{...source,key:adapter.key(live.keys.get(key)),bindingId:live.keys.get(key)}]]:[]));
  return live.scope.with({unit,context:new Map(data.context),env,dimensions:new Map(data.dimensions),
    sourceBindings:new Map(),localSources,evidence:data.evidence});
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
      for(const entry of statements)results.push(await this.#request(entry));
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
      bundledNat:false,collectReferences:inputs.collectReferences,collectScopes:true,scopeRevision:inputs.revision,scopeTarget:this.#point.id,
      scopeProbe:(point,live)=>{
        if(point.id!==this.#point.id)return;
        costs.prefix=spent(replay.kernel,prefix);
        if(this.#stale())throw new ElaborationStop(unavailable("The source check changed while replay was loading."));
        if(JSON.stringify(point)!==JSON.stringify(this.#point))
          throw new ElaborationStop(unavailable("The selected scope did not reproduce its recorded context."));
        const table=replay.scopeRecorder.table,adapter=new BindingAdapter(table);
        const translator=live.translator.forkScope(live.scope,{normalize:false,...inputs.fuelLimits});
        const selectedPolicy=kernelReplayPolicy(replay.kernel);
        let scope,lexical=live.lexical;
        const validation=measure(replay.kernel);
        try {
          applyKernelReplayPolicy(replay.kernel,selectedPolicy);
          scope=queryEnvironment(live,adapter,translator.unit().declaration(translator.declarationFuel));
          // Inferring even Unit derives every local type in order through
          // contextScope. A recorded lambda domain is not typing authority.
          scope.infer(T.unit);
          for(const target of [live.goal,live.expected].filter(Boolean))
            if(scope.nf(scope.infer(target).type).tag!=="U")throw new TypeError("The scope's target is not a checked type.");
        } catch(error) {
          throw new ElaborationStop(failure("unavailable",error,{stage:"validation"}));
        } finally {scope?.unit.fuel?.close();costs.validation=spent(replay.kernel,validation);}

        const execute=(source,index)=>{
          applyKernelReplayPolicy(replay.kernel,selectedPolicy);
          const parsed=parsedEntry(source),reserved=reservedReferences(parsed.text);
          const {adapter:entryAdapter,context,constructors}=bindingInputs(table,live.values,{reserved,lexical:lexical.snapshot()});
          const owner=["contextual-session",this.#serial,"entry",String(index)],moduleName=owner.join("/");
          const syntax=resolveBindingSyntax(parsed.tree,{table,owner,context,constructors,
            source:{revision:inputs.revision,module:moduleName}});
          const tree=lowerBindingSyntax(syntax,entryAdapter);
          const used=syntaxNames({context:[...scope.context],env:[...scope.env],dimensions:[...scope.dimensions]});
          const names=new NameSupply({taken:name=>used.has(name)||scope.checker.assumptions.has(name)});
          const unit=translator.unit({source:parsed.text,moduleName,bindingAdapter:entryAdapter,names,
            declaring:live.scope.unit.declaring}).declaration(translator.declarationFuel);
          let current=copiedScope(scope,unit),result,extension=null;
          try {
            if(parsed.kind==="let") {
              current=translator.bindLet(tree[0],current);
              const id=tree[0].target.bindingId,record=table.get(id),value=current.env.get(entryAdapter.key(id));
              const type=current.infer(value).type;
              result={kind:"defined",text:`${record.label} : ${translator.shownIn(type,current)}`};
              extension=freeze({source,binding:record,resolved:JSON.stringify(syntax)});
              lexical=lexical.bind(record.label,bindingResolution(id));
              scope=current;
            } else {
              const term=translator.term(tree,current),checked=current.infer(term);
              const value=current.nf(parsed.kind==="typeof"?checked.type:checked.term);
              result={kind:parsed.kind==="typeof"?"type":"value",text:translator.shownIn(value,current)};
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
      const stopped=result.outputs.concat(result.imports,result.gaps).find(output=>limits.has(output.failure));
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
