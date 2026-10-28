import test from "node:test";
import assert from "node:assert/strict";
import { builtinNames, legacyBuiltinNames, reservedReferences } from "../web/cubist/parser.mjs";
import { builtinHandlers, builtinTerm } from "../web/translator/builtins.mjs";

test("every reserved builtin and legacy fallback has a call handler or an explicit syntax owner", () => {
  // Interval is a binder domain; face/face_when are composition/gluing
  // pieces; flip/meet/join are handled by Translator.interval.
  const syntax = ["Interval", "face", "face_when", "flip", "meet", "join"];
  const callKeywords = ["typed", "path", "fill", "at", "left", "right"];
  assert.deepEqual([...new Set([...builtinHandlers.keys(), ...syntax])].sort(),
    [...new Set([...builtinNames, ...legacyBuiltinNames, ...callKeywords])].sort());
  const references = new Set(reservedReferences(""));
  for (const [name, handler] of builtinHandlers) {
    assert.equal(typeof handler, "function", name);
    assert.ok(references.has(name), name);
    assert.ok(!syntax.includes(name), `${name} has two owners`);
  }
});

test("unknown calls and unsupported arities retain the ordinary-call fallback", () => {
  for (const name of ["ordinary", "constructor", "toString", "__proto__"])
    assert.equal(builtinTerm(null, name, { args: [] }, null, null), undefined);
  for (const [name, count] of [["ua", 2], ["typed", 1], ["Glue", 0], ["glue", 0], ["unglue", 2],
    ["path_from_transport", 3], ["at", 1], ["pair_induction", 2], ["unit_induction", 2], ["FunExt", 5], ["absurd", 0],
    ["left", 2], ["refl", 0], ["sym", 2], ["trans", 1], ["cong", 1], ["apd", 3],
    ["apd_path", 1], ["transport", 4], ["path_induction", 5], ["based_induction", 7]])
    assert.equal(builtinTerm(null, name, { args: Array(count) }, null, null), undefined, name);
});
