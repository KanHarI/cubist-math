import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import createKernel from "../web/dist/kernel.mjs";
import { Kernel } from "../web/kernel.mjs";
import { Session } from "../web/session.mjs";
import { parse, formatStep } from "../web/language.mjs";
import { layout, pathFromMarked, pathFromNames } from "../web/expressions.mjs";
const module = await createKernel();
const fresh = () => new Session(module);

test("preview is isolated; accept, undo, branches, and replay preserve results", () => {
  const s = fresh();
  try {
    s.loadDemo();
    const before = s.snapshot(),
      view = s.inspect("nested");
    const preview = s.previewFocus({
      name: "nested",
      side: "expression",
      path: [1],
      operation: "BetaReducePointed",
      resultName: "reduced",
    });
    assert.deepEqual(s.engine.stats(), before.stats);
    assert.equal(s.engine.bindings.has("reduced"), false);
    assert.equal(preview.steps.length, 4);
    assert.equal(preview.result.expression.kind, "Ap");
    assert.equal(preview.result.expression.children[1].kind, "Singleton");
    assert.deepEqual(s.inspect("nested"), view);
    s.accept(preview.token);
    const branch = s.revision;
    assert.equal(s.inspect("reduced").expression.children[1].kind, "Singleton");
    assert.throws(() => s.accept(preview.token), /stale/);
    const old = s.previewSource("old = unit()");
    assert.throws(() => s.previewSource("invalid syntax"), /Line/);
    assert.throws(() => s.accept(old.token), /stale/);
    s.undo();
    assert.equal(s.revision, before.revision);
    assert.equal(s.engine.bindings.has("reduced"), false);
    const p = s.previewSource("alternate = unit()");
    s.accept(p.token);
    assert.notEqual(s.revision, branch);
    s.checkout(branch);
    assert.equal(s.inspect("reduced").expression.children[1].kind, "Singleton");
  } finally {
    s.dispose();
  }
});
test("rejection and malformed import are atomic; fresh assumptions stay distinct", () => {
  const s = fresh();
  try {
    s.loadDemo();
    const before = s.snapshot();
    assert.throws(
      () => s.previewSource("bad = apply(identity, zero)"),
      /rejected/,
    );
    assert.deepEqual(s.engine.stats(), before.stats);
    assert.equal(s.draft, null);
    assert.throws(() => s.previewSource("bad = var(Unit)"), /context/);
    assert.throws(
      () =>
        s.previewFocus({
          name: "nested",
          side: "expression",
          path: [3],
          operation: "BetaReducePointed",
        }),
      /rejected/,
    );
    const p = s.previewSource("y = assume(Unit)\ny_value = var(y)");
    s.accept(p.token);
    assert.notEqual(
      s.engine.bindings.get("x").id,
      s.engine.bindings.get("y").id,
    );
    const exported = s.export(),
      source = s.snapshot().source;
    exported.steps.push({
      name: "evil",
      op: "PiElim",
      args: ["missing", "zero"],
      free: [],
    });
    assert.throws(() => s.import(exported), /judgement/);
    assert.equal(s.snapshot().source, source);
  } finally {
    s.dispose();
  }
});
test("source/export round trip, explicit axioms, and structured validation", () => {
  const s = fresh(),
    other = fresh();
  try {
    s.loadDemo();
    const document = s.export();
    other.import(document);
    assert.deepEqual(other.inspect("nested"), s.inspect("nested"));
    const source = s.snapshot().source,
      third = fresh();
    try {
      const p = third.previewSource(source);
      third.accept(p.token);
      assert.deepEqual(third.inspect("nested"), s.inspect("nested"));
    } finally {
      third.dispose();
    }
    assert.throws(() => s.previewSource("a = kernel.Axiom(Unit)"), /rejected/);
    s.setPolicy(true);
    const p = s.previewSource("a = kernel.Axiom(Unit)");
    s.accept(p.token);
    assert.throws(() => s.setPolicy(false), /rejected/);
    assert.equal(s.allowAxioms, true);
    assert.throws(() => other.import(s.export()), /axiom policy/);
    assert.throws(
      () => parse("a = eval(Unit)", s.metadata),
      /Unknown operation/,
    );
    assert.throws(
      () => s.previewSource("v = kernel.Vble(; context: x, context: x)"),
      /Repeated/,
    );
    assert.throws(() => s.previewSource("v = apply(identity)"), /requires 2/);
    assert.equal(s.metadata.length, 67);
    for (const m of s.metadata) {
      const step = {
        name: "value",
        op: m.name,
        args: Array(m.judgements).fill("j"),
        context: m.context ? "c" : null,
        free: Array(m.free).fill(null),
      };
      assert.equal(parse(formatStep(step), s.metadata)[0].op, m.name);
    }
  } finally {
    s.dispose();
    other.dispose();
  }
});
test("path and extra-parenthesis selection distinguish shared occurrences and reject edits", () => {
  const s = fresh();
  try {
    s.loadDemo();
    const p = s.previewSource(
      "twice = kernel.SigmaIntro(one, Unit, one; free: [_])",
    );
    s.accept(p.token);
    const tree = s.inspect("twice").expression,
      { text, spans } = layout(tree);
    assert.equal(tree.children[0].id, tree.children[1].id);
    for (const path of [[0], [1]]) {
      const span = spans.find(
        (x) => JSON.stringify(x.path) === JSON.stringify(path),
      );
      const marked =
        text.slice(0, span.start) +
        "(" +
        text.slice(span.start, span.end) +
        ")" +
        text.slice(span.end);
      assert.deepEqual(pathFromMarked(tree, marked), path);
    }
    assert.deepEqual(pathFromNames(tree, ["second"]), [1]);
    assert.throws(
      () => pathFromMarked(tree, text.replace("⋆", "0")),
      /unchanged/,
    );
    assert.throws(() => pathFromNames(tree, ["argument"]), /No child/);
  } finally {
    s.dispose();
  }
});
test("CLI uses both path and parenthesis selection with the same checked engine", () => {
  const s = fresh();
  let marked, markedType;
  try {
    s.loadDemo();
    const t = layout(s.inspect("identity").type);
    const codomain = t.spans.find((x) => JSON.stringify(x.path) === "[1]");
    markedType =
      t.text.slice(0, codomain.start) +
      "(" +
      t.text.slice(codomain.start, codomain.end) +
      ")" +
      t.text.slice(codomain.end);
    const { text, spans } = layout(s.inspect("nested").expression);
    const range = spans.find((x) => JSON.stringify(x.path) === "[1]");
    marked =
      text.slice(0, range.start) +
      "(" +
      text.slice(range.start, range.end) +
      ")" +
      text.slice(range.end);
  } finally {
    s.dispose();
  }
  const commands = `demo\nuse identity\nselect type.codomain\nselect type --paren ${markedType}\nparent\ndown codomain\nuse nested\nselect expr.argument\nselect expr --paren ${marked}\nreduce cli_result\naccept\nuse cli_result\nstats\nquit\n`;
  const result = spawnSync(process.execPath, ["cli/repl.mjs"], {
    input: commands,
    encoding: "utf8",
    cwd: new URL("..", import.meta.url),
    timeout: 20000,
  });
  assert.equal(result.status, 0, result.stderr);
  assert.doesNotMatch(result.stdout, /ERROR:/);
  assert.match(result.stdout, /ACCEPTED/);
  assert.match(result.stdout, /cli_result \[judgement\]/);
});
test("WASM replays all 3652 native reference records, with identical successful fingerprints", async () => {
  const k = new Kernel(module, true);
  let successes = 0,
    checked = 0;
  const js = new Map(),
    cs = new Map();
  const mix = (x) => {
    x = BigInt.asUintN(64, x ^ (x >> 30n));
    x = BigInt.asUintN(64, x * 0xbf58476d1ce4e5b9n);
    x ^= x >> 27n;
    x = BigInt.asUintN(64, x * 0x94d049bb133111ebn);
    return x ^ (x >> 31n);
  };
  const cache = new Map();
  function fp(id) {
    if (!id) return 0n;
    if (cache.has(id)) return cache.get(id);
    let h = mix(
      BigInt(module._wb_node(k.handle, id, 0)) +
        (BigInt(module._wb_node(k.handle, id, 1)) << 32n),
    );
    for (const child of k.node(id).children) h = mix(h ^ fp(child));
    cache.set(id, h);
    return h;
  }
  try {
    const lines = (
      await readFile(new URL("reference_trace.txt", import.meta.url), "utf8")
    )
      .trim()
      .split("\n");
    for (const [i, line] of lines.entries()) {
      const words = line.split(/\s+/);
      let n = 0;
      const num = () => Number(words[n++]);
      const opcode = num(),
        nj = num(),
        args = Array.from({ length: nj }, () => js.get(num()));
      const context = cs.get(num()) ?? null,
        nf = num(),
        free = Array.from({ length: nf }, () => cs.get(num()) ?? null);
      const status = num(),
        originalId = num(),
        expected = words.slice(n).map(BigInt),
        meta = k.metadata.find((m) => m.code === opcode);
      // Resource-policy failures depend on the native test's temporary configuration.
      if (status === 2) continue;
      const step = { name: `line${i + 1}`, op: meta.name, args, context, free };
      if (status !== 0) {
        assert.throws(
          () => k.apply(step),
          (e) => e.details?.status === status,
          `record ${i + 1}`,
        );
        checked++;
        continue;
      }
      k.apply(step);
      const binding = k.bindings.get(step.name),
        kind = Number(meta.returnsContext),
        get = (f) => module._wb_view(k.handle, kind, binding.id, f);
      (kind ? cs : js).set(originalId, step.name);
      let dep = 0n;
      for (let set = get(kind ? 1 : 2); set; set = k.node(set).children[0])
        dep = mix(dep ^ BigInt(k.node(set).parameter));
      assert.deepEqual(
        [kind ? 0n : fp(get(0)), fp(get(kind ? 0 : 1)), dep],
        expected,
        `record ${i + 1}: ${meta.name}`,
      );
      successes++;
      checked++;
    }
    assert.ok(successes > 2600);
    assert.ok(checked > 3600);
  } finally {
    k.dispose();
  }
});

test("included polymorphic identity verifies in the WASM kernel", async () => {
  const s = fresh();
  try {
    const source = await readFile(
      new URL("../examples/identity.math", import.meta.url),
      "utf8",
    );
    const p = s.previewSource(source);
    s.accept(p.token);
    assert.equal(s.verify("Identity", "identity"), true);
  } finally {
    s.dispose();
  }
});
