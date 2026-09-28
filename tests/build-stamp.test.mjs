// The build stamp (tools/build-stamp.mjs): a hash of each generated
// artifact's sources, so that a stale web/dist fails loudly instead of
// testing code it does not contain.
import test from "node:test";
import assert from "node:assert/strict";
import { buildSources, hashOf, runtimeModules, staleBuilds } from "../tools/build-stamp.mjs";

test("the hash covers each source by path and content", () => {
  const files = new Map([["a.c", "int a;"], ["b.h", "int b;"]]);
  const read = path => files.get(path);
  const before = hashOf([...files.keys()], read);
  assert.equal(hashOf([...files.keys()], read), before, "deterministic");
  files.set("b.h", "int b2;");
  assert.notEqual(hashOf([...files.keys()], read), before, "a changed file");
  files.set("b.h", "int b;");
  assert.notEqual(hashOf(["a.c", "b.h", "c.c"], path => files.get(path) ?? ""), before, "an added file");
  assert.notEqual(hashOf(["b.h", "a.c"], read), before, "the order of paths is part of the hash");
});

test("the stamped sources are the kernel's and the translator copy's", () => {
  const kernel = buildSources.kernel();
  assert.ok(kernel.includes("kernel/src/term_normalize.c") && kernel.includes("wasm/cubical_bridge.c") && kernel.includes("Makefile"));
  assert.ok(kernel.includes("kernel/include/cubical_kernel.h") && kernel.includes("kernel/src/term_internal.h"));
  assert.deepEqual(buildSources.runtime(), runtimeModules.map(name => `lib/cubical/${name}.mjs`));
});

test("the build under test matches its sources", () => {
  assert.deepEqual(staleBuilds(), []);
});
