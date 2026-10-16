import test from "node:test";
import assert from "node:assert/strict";
import { compactSamples, hashEntries } from "../tools/frontend-generation-evidence.mjs";

test("cost evidence retains per-sample semantic digests and rejects mode-dependent behavior", () => {
  const sample = {name:"workload",source:"source",declarations:1,verified:1,generatedNames:["x"],assumptions:[],
    sourceDigest:"sources",interfacesDigest:"interfaces",declarationFuel:[["x",{queries:1}]],gaps:[],elapsedMs:1,
    collections:{references:false}};
  const referenceMode = {...sample,collections:{references:true},elapsedMs:2};
  const result = compactSamples([sample,referenceMode]);
  assert.deepEqual(result.samples[0].digests, result.samples[1].digests);
  assert.notEqual(result.samples[0].elapsedMs, result.samples[1].elapsedMs);
  for (const changes of [{interfacesDigest:"changed"},{generatedNames:[]},{assumptions:["new axiom"]},
    {declarationFuel:[["x",{queries:2}]]},{gaps:[{code:"E606"}]}]) {
    assert.throws(() => compactSamples([sample,{...referenceMode,...changes}]), {code:"ERR_ASSERTION"});
  }
  assert.equal(hashEntries([["z","last"],["A","first"]]), hashEntries([["A","first"],["z","last"]]));
});
