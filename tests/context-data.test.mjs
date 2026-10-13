import test from "node:test";
import assert from "node:assert/strict";
import {snapshotSyntax,syntaxGraphBudget} from "../web/translator/syntax-graph.mjs";

test("persistent context syntax remains compact under sharing and contains no live references",()=>{
  const local={tag:"Var",name:"x"};
  let term=local;
  for(let k=0;k<40;k++)term={tag:"App",fn:term,arg:term};
  const snapshot=snapshotSyntax({context:[["x",{tag:"Unit"}]],value:term},{budget:syntaxGraphBudget({maxVisits:1000})});
  assert.ok(snapshot.nodes.length<50);
  assert.ok(JSON.stringify(snapshot).length<10000);
  assert.deepEqual(JSON.parse(JSON.stringify(snapshot)),snapshot);
  const before=JSON.stringify(snapshot);
  local.name="changed";
  assert.equal(JSON.stringify(snapshot),before);
  assert.throws(()=>snapshot.nodes[0].fields.push(["bad",true]),TypeError);
});

test("snapshots reject live state, executable accessors, cycles and excessive data",()=>{
  for(const value of [new Map(),new Set(),new Date(),()=>{},Infinity,1n])
    assert.throws(()=>snapshotSyntax({value}),TypeError);
  let invoked=false;
  const accessor={get unsafe(){invoked=true;return 1;}};
  assert.throws(()=>snapshotSyntax(accessor),/accessors/);
  assert.equal(invoked,false);
  const cycle={};cycle.self=cycle;
  assert.throws(()=>snapshotSyntax(cycle),/acyclic/);
  assert.throws(()=>snapshotSyntax({name:"large"},{maxText:2}),/text budget/);
  assert.throws(()=>snapshotSyntax({name:"x"},{budget:syntaxGraphBudget({maxVisits:1})}),/term-size budget/);
});

test("a snapshot never promotes non-enumerable checked annotations into authority",()=>{
  const term={tag:"PApp",path:{tag:"Var",name:"p"},arg:[["i"]]};
  Object.defineProperty(term,"checkedType",{value:new Map([["native handle",17]])});
  const snapshot=snapshotSyntax(term);
  assert.equal(JSON.stringify(snapshot).includes("checkedType"),false);
  assert.ok(snapshot.nodes.some(node=>node.fields.some(([key,value])=>key==="tag"&&value==="PApp")));
});

test("descriptions distinguish array holes and null-prototype records",()=>{
  assert.notDeepEqual(snapshotSyntax([]),snapshotSyntax(new Array(2)));
  assert.notDeepEqual(snapshotSyntax({}),snapshotSyntax(Object.create(null)));
});
