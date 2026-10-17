// Replay consumes a recorded check, never the current filesystem or the
// original check's callbacks. Resource changes at declaration boundaries
// are data too. A deadline epoch distinguishes a fresh per-declaration
// clock from one clock that spans several declarations.
export function kernelReplayPolicy(kernel) {
  return Object.freeze({stepBudget:String(kernel.stepBudget),maxQuerySteps:String(kernel.maxQuerySteps),
    optimizations:Object.freeze({...kernel.optimizations}),extensions:Object.freeze({...kernel.extensions}),
    deadlineDuration:kernel.deadlineDuration??0,deadlineGeneration:kernel.deadlineGeneration??0});
}

export function applyKernelReplayPolicy(kernel,policy,{resetDeadline=true}={}) {
  kernel.stepBudget=BigInt(policy.stepBudget);
  kernel.maxQuerySteps=BigInt(policy.maxQuerySteps);
  kernel.setStepBudget(kernel.stepBudget);
  kernel.setOptimizations(policy.optimizations);
  kernel.setExtensions(policy.extensions);
  if(resetDeadline)kernel.setDeadline(policy.deadlineDuration);
}

export class ReplayInputs {
  #events=[];
  constructor({revision,main,prepared,readSource,fuelLimits,kernel,collectReferences}) {
    this.revision=revision;this.main=main;
    this.modules=Object.freeze(Object.fromEntries([...prepared].map(([name,entry])=>[name,Object.freeze({
      text:entry.text??null,error:entry.error?.message??null,nameBased:!!readSource.nameBased?.(name),
    })])));
    this.fuelLimits=Object.freeze(Object.fromEntries(Object.entries(fuelLimits).map(([kind,limits])=>
      [kind,limits?Object.freeze({...limits}):undefined])));
    this.initialPolicy=kernelReplayPolicy(kernel);
    this.collectReferences=collectReferences;
    Object.freeze(this);
  }
  record(stage,module,declaration,kernel,result=null) {
    this.#events.push(Object.freeze({stage,module,name:replayItemName(declaration),policy:kernelReplayPolicy(kernel),
      outcome:result?Object.freeze({status:result.status,failure:result.failure??null}):null}));
  }
  snapshot() {
    return Object.freeze({revision:this.revision,main:this.main,modules:this.modules,fuelLimits:this.fuelLimits,
      initialPolicy:this.initialPolicy,collectReferences:this.collectReferences,
      events:Object.freeze([...this.#events])});
  }
}

const replayItemName=item=>item.name?.text??`${item.kind}@${item.start}`;

export function replayReader(snapshot) {
  const get=name=>{
    if(!Object.hasOwn(snapshot.modules,name))throw new TypeError(`Module is outside the pinned replay: ${name}`);
    return snapshot.modules[name];
  };
  const read=async name=>{
    const entry=get(name);
    if(entry.error)throw new Error(entry.error);
    return entry.text;
  };
  read.nameBased=name=>get(name).nameBased;
  // A refusal of the root's imports must also survive, although its text
  // is supplied directly to check() rather than read through this function.
  read.checkImports=name=>get(name).error;
  return read;
}

export function replayPolicyCallbacks(snapshot,kernel,{onChangedResult=()=>{}}={}) {
  let next=0,generation=snapshot.initialPolicy.deadlineGeneration;
  applyKernelReplayPolicy(kernel,snapshot.initialPolicy);
  const apply=(stage,module,declaration)=>{
    const event=snapshot.events[next++];
    if(!event||event.stage!==stage||event.module!==module||event.name!==replayItemName(declaration))
      throw new TypeError("The ordered declaration prefix changed during replay.");
    applyKernelReplayPolicy(kernel,event.policy,{resetDeadline:generation!==event.policy.deadlineGeneration});
    generation=event.policy.deadlineGeneration;
    return event;
  };
  const finish=(stage,module,declaration,result)=>{
      const event=apply(stage,module,declaration);
      if(result&&(result.status!==event.outcome.status||(result.failure??null)!==event.outcome.failure))onChangedResult(result,event);
  };
  return {onDeclarationStart:(module,declaration)=>apply("start",module,declaration),
    onDeclaration:(module,declaration,result)=>finish("end",module,declaration,result),
    onDirectiveStart:(module,directive)=>apply("directive-start",module,directive),
    onDirective:(module,directive,result)=>finish("directive-end",module,directive,result)};
}
