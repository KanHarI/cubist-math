// Diagnostic codes (web/diagnostics.mjs): every message the sources can
// report has one, each code is one message, and the errors chapter has an
// entry for each. The reference examples' test checks that every failure and
// warning they show is reported with its code.
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { diagnostics, groups, diagnosticCode, withCode, diagnosticLine } from "../web/diagnostics.mjs";
import { compare } from "../tools/diagnostic-codes.mjs";
import { lint } from "../web/cubist/lint.mjs";

test("every message in the sources has a code, and every code a message", () => {
  const { missing, stale } = compare();
  assert.deepEqual(missing.map(({ text, file }) => `${text} (${file})`), [], "Run node tools/diagnostic-codes.mjs --add.");
  assert.deepEqual(stale, [], 'A code whose message is gone stays, marked "retired".');
});

test("codes are unique and well formed, each in its group, one per message", () => {
  const codes = diagnostics.map(([code]) => code);
  assert.equal(new Set(codes).size, codes.length);
  assert.equal(new Set(diagnostics.map(([, message]) => message)).size, diagnostics.length);
  for (const [code, message, status] of diagnostics) {
    assert.match(code, /^[EKW]\d{3}$/, code);
    assert.ok(groups[code.slice(0, 2)], `${code} is in a group`);
    assert.ok(message.length && [undefined, "retired"].includes(status), code);
  }
});

test("a message is shown with its code, the most specific that matches it", () => {
  const mismatch = "Type mismatch: found Unit, expected Nat.";
  assert.equal(diagnostics.find(([code]) => code === diagnosticCode(mismatch))[1], "Type mismatch: found …, expected ….");
  assert.equal(diagnosticCode("Not a message the checker reports."), null);
  assert.equal(withCode(mismatch), `${diagnosticCode(mismatch)}: ${mismatch}`);
  assert.equal(withCode("Not a message the checker reports."), "Not a message the checker reports.");
  // The command line's form: a position at the end of a message moves to the front.
  assert.equal(diagnosticLine({ code: "E606", message: `${mismatch} at 2:3`, declaration: "wrong" }),
    `error E606 at line 2:3 (wrong): ${mismatch}`);
  assert.equal(diagnosticLine({ severity: "warning", code: "W703", message: "k is unused.", line: 1, column: 37 }),
    "warning W703 at line 1:37: k is unused.");
});

test("each warning carries its code", () => {
  const [warning] = lint("def copy(n : Nat) := induction n as k return Nat { zero => 0; succ h => succ(h); };");
  assert.equal(warning.code, diagnosticCode(warning.message));
  assert.match(warning.code, /^W7\d\d$/);
});

test("the errors chapter has one entry for every code", () => {
  const html = readFileSync(new URL("../web/reference/errors.html", import.meta.url), "utf8");
  const anchors = [...html.matchAll(/ id="([EKW]\d{3})"/g)].map(match => match[1]);
  assert.deepEqual(anchors.toSorted(), diagnostics.map(([code]) => code).toSorted());
});
