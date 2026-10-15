import {selected} from "./theories.mjs";
import {bindNotationContext,selectNotationContext} from "./notation-context.mjs";
import {lowerBindingReference} from "../cubist/binding-syntax.mjs";

// One expression boundary, shared by term elaboration and consumers which
// inspect a term's structure. Enter its actual scope/effects before examining
// the body; stripping a wrapper would skip receiver checks or capture names.
// Ordinary term elaboration enters one boundary at a time so observations
// at intervening source nodes are preserved.
export function enterExpressionScope(translator,scope,node,{receiver=false}={}) {
  switch(node.kind) {
    case "operandAlternatives":return {node:receiver?node.receiver:node.value,scope};
    case "bindingReference": {
      const lowered=lowerBindingReference(node,scope.unit.bindingAdapter,scope.slotOutcomes,{deferMissing:true});
      return lowered===node?null:{node:lowered,scope};
    }
    case "name": {
      const operand=scope.env.get(node.name);
      return operand?.tag==="SourceOperand"?{node:operand.node,scope:operand.scope}:null;
    }
    case "select":return {node:node.body,scope:selected(translator,scope,node.model,
      {effects:node.effects,activation:node.activation})};
    case "scoped":return {node:node.node,scope:node.scope};
    case "boundNotation": {
      const reference=node.selection.kind==="bindingReference"
        ?lowerBindingReference(node.selection,scope.unit.bindingAdapter,scope.slotOutcomes):node.selection;
      if(reference.kind!=="name")throw new TypeError("A retained notation context must resolve to its exact identity.");
      return {node:node.body,scope:selectNotationContext(scope,reference.name)};
    }
    case "notationArgument":return {node:node.body,
      scope:bindNotationContext(scope,translator.identityAdapter.key(node.notation.bindingId))};
    default:return null;
  }
}
