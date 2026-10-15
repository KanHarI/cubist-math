// Production source boundary for retained theory interfaces. File effects
// resolve in the source module once; artifact construction uses only IDs.
import {reservedReferences} from "../cubist/parser.mjs";
import {retainTheorySource} from "../cubist/retained-theories.mjs";
import {retainedTheoryArtifacts,retainedMorphismArtifacts} from "../cubist/retained-theory-artifacts.mjs";
import {sourceBindingInputs,bindingDeclaration} from "./binding-module.mjs";
import {activateSourceItem,withSourceCaptures} from "./retained-source-context.mjs";
import {Scope} from "./elaboration.mjs";

export function retainedTheoryDeclarations(t,module,declaration,env,{lookup,isTheory}) {
  const registry=t.compilationBindings,table=registry.table;
  const source={revision:registry.revision,module:module.moduleName};
  const owner=["theory-source",module.moduleName,String(declaration.start)];
  const inputs=sourceBindingInputs(registry,env,{reserved:reservedReferences(module.source)});
  const prepared=activateSourceItem(t,new Scope(module,new Map(),new Map([...env,...inputs.env])),
    declaration,inputs,{owner,source});
  const captures=withSourceCaptures(new Map([...env,...inputs.env]),prepared,inputs.adapter);
  const proposition=id=>{
    const entry=captures.get(inputs.adapter.key(id));
    return entry?.tag==="Inductive"&&(entry.modifier==="prop"||entry.modifier?.trunc===-1);
  };
  const retained=retainTheorySource(prepared.item,{table,owner,source,context:prepared.context,
    constructors:inputs.constructors},{lookup,proposition});
  const built=retainedTheoryArtifacts(retained,{table,owner:[...owner,"base"]});
  const morphisms=retainedMorphismArtifacts(built.record,{table,owner:[...owner,"morphisms"],
    bindings:built.bindings,isTheory});
  const record=morphisms.record;
  built.artifacts[0].theory=record;
  const requires=[...new Set(record.fields.filter(field=>field.evidence).map(field=>field.evidence))];
  const declarations=[...built.artifacts,...morphisms.artifacts].map(({binding,syntax,...metadata})=>
    bindingDeclaration(binding,syntax,{...metadata,
      ...(["model","make"].includes(metadata.generated.role)?{requires}:{})}));
  for(const [key,value] of captures)env.set(key,value);
  return {record,declarations};
}
