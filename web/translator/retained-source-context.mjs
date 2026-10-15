// File-level recipes activate once for each source consumer, before its
// parameters. Generated copies use the resulting external identities and
// closed values, just as they use their source imports; no recipe is replayed
// in the destination. The caller explicitly carries this capture environment
// with the retained syntax across module/generation boundaries.
import {sourceOrigin,mapResolution} from "../cubist/bindings.mjs";
import {resolveBindingReceiver,lowerBindingSyntax} from "../cubist/binding-syntax.mjs";
import {fileSelectionEffects} from "../cubist/scopes.mjs";
import {freeNames,isTerm} from "./core.mjs";
import {selected} from "./theories.mjs";
import {checkedNotationContext,notationContextEntry} from "./notation-context.mjs";

export function activateSourceItem(t,scope,item,{context,constructors,adapter},{owner,source}) {
  if(scope.context.size||scope.dimensions.size)
    throw new TypeError("File-level activation requires a closed module scope before declaration parameters.");
  const effects=fileSelectionEffects(item.kind),table=t.compilationBindings.table;
  const captures=[],activations=[],notationValues=[];
  let inner=scope.withUnit(scope.unit.with({bindingAdapter:adapter}));
  if(effects.labels||effects.notation)for(const [index,recipe] of (item.uses??[]).entries()) {
    const origin=sourceOrigin({...source,start:recipe.start,end:recipe.end});
    const binding=table.allocate([...owner,"activation",String(index)],{role:"activation",label:"selection",origin});
    const syntax=resolveBindingReceiver(recipe,{table,owner:[...owner,"recipe",String(index)],context,constructors,source},
      {namespace:false});
    const token={text:binding.label,bindingId:binding.id,bindingRole:binding.role,origin,
      start:recipe.start,end:recipe.end};
    inner=selected(t,inner,lowerBindingSyntax(syntax,adapter),{effects,activation:token});
    const outcome=inner.slotOutcomes.activation(binding.id),value=inner.env.get(adapter.key(binding.id));
    if(!outcome||!isTerm(value)||freeNames(value).size)
      throw new TypeError("A retained model activation needs its checked closed receiver and resolved interface.");
    const capture=t.compilationBindings.capture(value,origin);
    const notation=effects.notation?t.compilationBindings.captureModelNotation(capture,origin):null;
    const members=Object.freeze(outcome.members.map(([label,resolution])=>Object.freeze([label,
      mapResolution(resolution,id=>id===binding.id?capture.id:id)])));
    inner=inner.alias(adapter.key(capture.id),value);
    // Binding all ready labels at this boundary preserves later-local
    // shadowing and hides conflicting qualified globals through their root.
    // Labels the interface does not provide keep the previous whole lookup.
    for(const [label,resolution] of members)context=context.bind(label,resolution);
    if(notation) {
      context=context.withSelectedNotation(notation.id);
      // Only this explicit ephemeral environment carries checked values.
      // The lexical snapshot and activation history carry identities alone.
      const value=checkedNotationContext(inner);
      inner=inner.aliases([notationContextEntry(adapter.key(notation.id),value)]);
      notationValues.push(Object.freeze([notation.id,value]));
    }
    captures.push(Object.freeze([capture.id,value]));
    activations.push(Object.freeze({binding,capture,notation,syntax,effects,members,
      consumer:sourceOrigin({...source,start:item.start,end:item.end})}));
  }
  return Object.freeze({item:Object.freeze({...item,uses:[]}),context,constructors,
    captures:Object.freeze(captures),activations:Object.freeze(activations),notationValues:Object.freeze(notationValues)});
}

// Capture IDs are external to each generated declaration's local telescope.
// Copying/freshening those locals preserves the closed source captures. This
// environment remains explicit, and missing captures never fall back to a
// public label in the destination.
export function withSourceCaptures(env,prepared,adapter) {
  return new Map([...env,...prepared.captures.map(([id,value])=>[adapter.key(id),value]),
    ...prepared.notationValues.map(([id,value])=>notationContextEntry(adapter.key(id),value))]);
}
