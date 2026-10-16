import test from "node:test";
import assert from "node:assert/strict";
import {BindingTable, BindingAdapter, LexicalContext, SlotOutcomes, sourceOrigin,
  bindingResolution, missingResolution, reservedResolution} from "../web/cubist/bindings.mjs";

const origin = sourceOrigin({revision: "source-1", module: "parent", start: 12, end: 13});
const allocate = (table, label = "x", role = "local", owner = ["decl", "0"]) =>
  table.allocate(owner, {role, label, origin});
const roundtrip = value => JSON.parse(JSON.stringify(value));

test("same-spelled identities distinguish owners and counters and replay deterministically", () => {
  const make = revision => {
    const table = new BindingTable(revision);
    const records = [allocate(table), allocate(table), allocate(table, "x", "local", ["decl", "1"])];
    return {table, records};
  };
  const a = make("compilation-1"), b = make("compilation-1"), edited = make("compilation-2");
  assert.equal(new Set(a.records.map(r => r.id)).size, 3);
  assert.deepEqual(a.records, b.records);
  assert.ok(a.records.every((record, k) => record.id !== edited.records[k].id));
  const restored = BindingTable.restore(roundtrip(a.table.snapshot()));
  assert.deepEqual(restored.snapshot(), a.table.snapshot());
  assert.deepEqual(allocate(restored), allocate(a.table));
  const malformed = roundtrip(b.table.snapshot());
  malformed.bindings[1].id = malformed.bindings[0].id;
  assert.throws(() => BindingTable.restore(malformed), /correspondence/);
});

test("freshening gives an explicit correspondence while external references and authored origins stay shared", () => {
  const table = new BindingTable("compilation"), external = allocate(table, "x", "declaration", ["import"]);
  const local = allocate(table), universe = allocate(table, "U", "universe"), dimension = allocate(table, "i", "dimension");
  const copy = table.freshen(new Set([local.id, universe.id, dimension.id]).values(), ["expansion", "0"]);
  assert.equal(copy.has(external.id), false);
  for (const record of [local, universe, dimension]) {
    const cloned = table.get(copy.get(record.id));
    assert.notEqual(record.id, cloned.id);
    assert.equal(cloned.original, record.id);
    assert.deepEqual(cloned.origin, record.origin);
    assert.equal(cloned.label, record.label);
    assert.equal(cloned.role, record.role);
  }
  const copiedAgain = table.freshen(copy.values(), ["expansion", "1"]);
  assert.equal(table.get(copiedAgain.get(copy.get(local.id))).original, local.id);
  assert.deepEqual(BindingTable.restore(roundtrip(table.snapshot())).snapshot(), table.snapshot());
  const before = table.snapshot();
  assert.throws(() => table.freshen([local.id, local.id], ["bad"]), /owned twice/);
  assert.deepEqual(table.snapshot(), before);
});

test("origins separate authored modules from expansion sites and contain immutable inert data", () => {
  const expanded = sourceOrigin({...origin, expansion: [{kind: "inheritance", site:
    {revision: "caller-1", module: "caller", start: 80, end: 96}}]});
  assert.equal(expanded.module, "parent");
  assert.equal(expanded.expansion[0].site.module, "caller");
  assert.deepEqual(sourceOrigin(roundtrip(expanded)), expanded);
  assert.throws(() => expanded.expansion[0].site.module = "parent", TypeError);
  assert.throws(() => sourceOrigin({...origin, expansion: [{kind: "generation", site: expanded}]}), /origin graph/);
  assert.throws(() => sourceOrigin({...origin, start: -1}), /span/);
});

test("deferred slots preserve original enclosing resolution and missing lookups across branches", () => {
  const table = new BindingTable("compilation"), outer = allocate(table), slot = allocate(table, "x", "pattern");
  const before = new LexicalContext().bind("x", bindingResolution(outer.id));
  const deferred = before.defer("x", slot.id), missing = new LexicalContext().defer("x", slot.id);
  const adapter = new BindingAdapter(table);
  const outcomes = new SlotOutcomes();
  assert.equal(adapter.lower(deferred.lookup("x"), outcomes), null);
  const variable = outcomes.decide(slot.id, "variable"), constructor = outcomes.decide(slot.id, "constructor");
  assert.equal(adapter.lower(deferred.lookup("x"), variable), adapter.key(slot.id));
  assert.equal(adapter.lower(deferred.lookup("x"), constructor), adapter.key(outer.id));
  assert.throws(() => adapter.lower(missing.lookup("x"), constructor), /Untranslated name: x/);
  assert.deepEqual(before.lookup("x"), bindingResolution(outer.id));
  assert.deepEqual(new LexicalContext(roundtrip(deferred.snapshot())).snapshot(), deferred.snapshot());
  assert.equal(adapter.lower(deferred.lookup("x"), new SlotOutcomes(roundtrip(variable.snapshot()))), adapter.key(slot.id));
  assert.throws(() => variable.decide(slot.id, "constructor"), /already been decided/);
  // An inserted argument refers directly to the caller's x. Deciding the
  // surrounding slot cannot capture it retrospectively.
  assert.equal(adapter.lower(bindingResolution(outer.id), variable), adapter.key(outer.id));
});

test("nested candidate constructors fall back through saved slots without destination lookup", () => {
  const table = new BindingTable("compilation"), a = allocate(table, "x", "pattern"), b = allocate(table, "x", "pattern");
  const context = new LexicalContext().defer("x", a.id).defer("x", b.id);
  const adapter = new BindingAdapter(table), outcomes = new SlotOutcomes().decide(b.id, "constructor");
  assert.equal(adapter.lower(context.lookup("x"), outcomes), null);
  assert.equal(adapter.lower(context.lookup("x"), outcomes.decide(a.id, "variable")), adapter.key(a.id));
  assert.throws(() => adapter.lower(context.lookup("x"), outcomes.decide(a.id, "constructor")), /Untranslated name/);
});

test("lowering rejects absent identities and limits explicit late lookup to its reserved namespace", () => {
  const table = new BindingTable("compilation"), x = allocate(table);
  const adapter = new BindingAdapter(table, {reserved: ["U0", "Unit"]});
  assert.equal(adapter.lower(reservedResolution("Unit")), "Unit");
  assert.throws(() => adapter.lower(reservedResolution("x")), /not allowed/);
  assert.throws(() => adapter.lower(bindingResolution("x")), /Unknown binding identity/);
  assert.throws(() => adapter.lower(missingResolution("Unit")), /Untranslated name/);
  assert.throws(() => adapter.lower(new LexicalContext().defer("x", "absent").lookup("x")), /Unknown binding identity/);
  assert.throws(() => adapter.lower(new LexicalContext().defer("x", x.id).lookup("x")), /candidate pattern/);
});
