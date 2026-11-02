// Each Cubist test module's inlined errors, warnings and outputs are the
// checker's: every diagnostic and print is a comment directly above the
// declaration or directive it belongs to, and nothing else
// (tools/inline-errors.mjs --write writes them). The modules are checked in
// SHARDS test files, each its share (every SHARDS-th module), so that the
// test runner checks them in parallel: in one file, the check is the
// slowest test of npm test by far.
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { cubistTestModules } from "../web/cubist/modules.mjs";
import { checkedModule, reported, stated } from "../tools/inline-errors.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";

export const SHARDS = 4;

// Every source text the checker prints belongs to one display
// (printedTogether): here each text carries its display's number,
// invisibly, so that a message assembled from two displays shows two. Each
// message the modules report is printed from one, its prose's names
// included (web/translator/translate.mjs, message); the numbers are removed
// before the messages are compared with the modules' comments.
let displays = 0;
const printedTogether = NativeCubicalElaborator.prototype.printedTogether;
NativeCubicalElaborator.prototype.printedTogether = function (...args) {
  const printed = printedTogether.apply(this, args), display = displays++;
  return { ...printed, texts: printed.texts.map(text => `\u2063${display}\u2064${text}`) };
};
const numbered = /\u2063(\d+)\u2064/g;
function oneDisplayEach(name, result) {
  const messages = [...result.outputs.map(output => output.reason), ...result.gaps.map(gap => gap.reason),
    ...result.prints.map(print => print.text), ...(result.warnings ?? []).map(warning => warning.message)];
  for (const message of messages.filter(message => typeof message === "string")) {
    const shown = new Set(Array.from(message.matchAll(numbered), match => match[1]));
    assert.ok(shown.size <= 1, `${name}: a message printed from ${shown.size} displays: ${message.replace(numbered, "[display $1]")}`);
  }
  const plain = text => typeof text === "string" ? text.replace(numbered, "") : text;
  for (const output of result.outputs) output.reason = plain(output.reason);
  for (const gap of result.gaps) gap.reason = plain(gap.reason);
  for (const print of result.prints) print.text = plain(print.text);
  for (const warning of result.warnings ?? []) warning.message = plain(warning.message);
}

export function inlinedShard(shard) {
  const names = cubistTestModules.filter((_, k) => k % SHARDS === shard);
  test(`Cubist test modules ${shard + 1} of ${SHARDS}: inlined errors, warnings and outputs are the checker's`, async () => {
    const module = await createCubical();
    for (const name of names) {
      const { source, result } = await checkedModule(name, module);
      oneDisplayEach(name, result);
      assert.ok(result.outputs.length || result.evaluations.length || result.prints.length, `${name} declares nothing`);
      const items = reported(source, result, name);
      assert.deepEqual(stated(source), items,
        `${name}: its checked comments differ from the check; run node tools/inline-errors.mjs --write ${name}`);
      // Each diagnostic has a code (web/diagnostics.mjs): one without is a
      // message the registry missed.
      for (const { label, text } of items)
        if (label !== "Output") assert.match(text, /^[EKW]\d{3}: /, `${name}: no code for "${text}"`);
    }
  });
}
