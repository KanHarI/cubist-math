import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { ObservationFrame } from "../web/translator/observations.mjs";
import { SourceUnit } from "../web/translator/elaboration.mjs";
import { checkProgram } from "./check-program.mjs";

const observer = () => {
  const events = [];
  const frame = new ObservationFrame(Object.fromEntries(["reference","step","scope"].map(kind =>
    [kind,(...values) => events.push([kind,...values])])));
  return {frame,events};
};

test("rejecting an enclosing attempt discards all selected nested observations", () => {
  const {frame,events} = observer(), first = frame.fork("recursive-fixed"), nested = first.fork("path-body");
  first.record("reference","before");
  for (const kind of ["reference","step","scope"]) nested.record(kind,"nested");
  nested.select();
  assert.equal(nested.outcome,"pending");
  assert.deepEqual(events,[]);
  first.discard();
  assert.equal(nested.outcome,"discarded");
  assert.throws(() => nested.record("scope","late"),/discarded/);
  const second = frame.fork("recursive-generalized");
  second.record("scope","retained");
  second.select();
  assert.deepEqual(events,[["scope","retained"]]);
});

test("selection preserves observation order through nested attempts", () => {
  const {frame,events} = observer(), outer = frame.fork("recursive");
  outer.record("reference","before");
  const inner = outer.fork("path-body");
  inner.record("step","proof");
  inner.record("scope","inside");
  inner.select();
  outer.record("reference","after");
  outer.select();
  assert.deepEqual(events,[["reference","before"],["step","proof"],["scope","inside"],["reference","after"]]);
  assert.throws(() => inner.select(),/only once/);
  assert.throws(() => outer.discard(),/pending/);
});

test("quiet attempts own no visible effects and collection does not change attempt paths", () => {
  const {frame,events} = observer(), disabled = new ObservationFrame();
  for (const root of [frame,disabled]) {
    const quiet = root.fork("argument-inference",{visible:false});
    for (const kind of ["reference","step","scope"]) {
      assert.equal(quiet.enabled(kind),false);
      quiet.record(kind,"discarded");
    }
    quiet.discard();
  }
  assert.deepEqual(frame.fork("actual").path,disabled.fork("actual").path);
  assert.deepEqual(events,[]);
  assert.deepEqual(frame.declaration().fork("actual").path,[{kind:"actual",index:0}]);
});

test("automatic coherence discards the written wildcard's proof steps and references", async t => {
  const source = `import hlevels;
inductive S1 { base; loop : base = base; }
inductive Two : prop U0 { left_; right_; }
def f(c : S1) : Two { match c { base => { exact left_; } _ => { exact right_; } } }
def checked_value : f(base) = left_ { rfl; }
def captured : f(base) = right_ { rfl; }`;
  const {program,result,get} = await checkProgram(t,source);
  assert.deepEqual(result.gaps.map(g => [g.name,g.code]),[["captured","E606"]]);
  assert.equal(get("checked_value").verified,true);
  const steps = program.steps("main","f").map(step => source.slice(step.start,step.end));
  assert.ok(steps.includes("exact left_;"));
  assert.ok(!steps.includes("exact right_;"));
  const linksAt = text => {
    const at = source.indexOf(text);
    assert.ok(at >= 0);
    return result.links.filter(link => link.start >= at && link.start < at + text.length);
  };
  assert.ok(linksAt("exact left_;").length > 0);
  assert.deepEqual(linksAt("exact right_;"),[]);
});

test("derived source units retain their consumers under shared attempt ownership", () => {
  const events = [], unit = new SourceUnit({checker:{},references:value => events.push(["original",value])});
  const observations = unit.observations.fork("candidate");
  const changed = unit.with({observations,references:value => events.push(["derived",value])});
  changed.recordReference("kept");
  changed.with({references:null}).recordReference("muted");
  assert.deepEqual(events,[]);
  observations.select();
  unit.recordReference("outer");
  assert.deepEqual(events,[["derived","kept"],["original","outer"]]);
});
