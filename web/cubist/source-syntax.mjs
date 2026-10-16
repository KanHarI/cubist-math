// Authored provenance is carried with syntax but is not part of its meaning.
// Every structural comparison and relocation uses this same metadata gate.
import {sourceOrigin,expandedOrigin} from "./bindings.mjs";
import {visitSyntax,mapSyntax} from "../translator/syntax-graph.mjs";

export const substitutionFrame = node => node.origin?.expansion.findLast(frame=>frame.kind==="substitution"&&frame.binding);

export const sourceMetadata = (key,value) => key==="shadowedDeclaration"&&typeof value==="string"
  ||key==="literalFailure"&&value?.tag==="failure"
  ||key==="origin"&&value&&typeof value==="object"
  &&typeof value.revision==="string"&&typeof value.module==="string"&&Array.isArray(value.expansion);

export function syntaxValue(tree,project=(_key,value)=>value) {
  return JSON.stringify(tree,(key,value)=>sourceMetadata(key,value)?undefined:project(key,value));
}

export function expandedSource(tree,expansion) {
  return mapSyntax(tree,value=>sourceMetadata("origin",value)?expandedOrigin(value,expansion):undefined);
}

export function qualifySource(tree,{revision,module}) {
  // The parser owns this fresh graph. Annotate shared nodes once, before any
  // expansion; source collection is a consumer of provenance, not its owner.
  visitSyntax(tree,node=>{
    // Clause/rule records have spans too, even when they have no `kind`.
    // They can be the innermost diagnostic site after a source copy.
    if(node&&!sourceMetadata("origin",node)&&Number.isInteger(node.start)&&Number.isInteger(node.end))
      node.origin??=sourceOrigin({revision,module,start:node.start,end:node.end});
  });
  return tree;
}
