import {selected} from "./theories.mjs";

// One expression boundary, shared by term elaboration and consumers which
// inspect a term's structure. Enter its actual scope/effects before examining
// the body; stripping a wrapper would skip receiver checks or capture names.
// Ordinary term elaboration enters one boundary at a time so observations
// at intervening source nodes are preserved.
export function enterExpressionScope(translator,scope,node) {
  switch(node.kind) {
    case "select":return {node:node.body,scope:selected(translator,scope,node.model,
      {effects:node.effects,activation:node.activation})};
    case "scoped":return {node:node.node,scope:node.scope};
    case "notationScope":return {node:node.body,scope:scope.withUnit(scope.unit.with({references:null})).aliases(node.aliases)};
    default:return null;
  }
}
