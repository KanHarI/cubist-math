import test from 'node:test';
import assert from 'node:assert/strict';
import {dimensionContextKey,mapSyntax,syntaxGraphBudget,syntaxNames} from '../syntax-graph.mjs';

test('dimension cache keys depend on assignments and reflect later map changes',()=>{
  const one=new Map([['i',0],['j',1]]),other=new Map([['j',1],['i',0]]);
  assert.equal(dimensionContextKey(one),dimensionContextKey(other));
  other.set('j',2);
  assert.notEqual(dimensionContextKey(one),dimensionContextKey(other));
});

test('bounded syntax traversal and copying retain shared objects and names',()=>{
  const leaf={tag:'Var',name:'x'},root={left:leaf,right:leaf,face:[['i:1']]};
  assert.deepEqual([...syntaxNames(root)].sort(),['Var','i','x']);
  const copy=mapSyntax(root,()=>undefined);
  assert.notEqual(copy,root);
  assert.equal(copy.left,copy.right);
  assert.notEqual(copy.left,leaf);
  const exhausted=syntaxGraphBudget({maxVisits:2});
  assert.throws(()=>syntaxNames(root,{budget:exhausted}),/term-size budget/);
});
