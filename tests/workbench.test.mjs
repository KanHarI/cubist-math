import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import createKernel from "../web/dist/kernel.mjs";
import { Kernel } from "../web/kernel.mjs";
import { Session } from "../web/session.mjs";
import { parse, formatStep, MAX_STEPS } from "../web/language.mjs";
import { layout, pathFromMarked, pathFromNames } from "../web/expressions.mjs";
const module = await createKernel();
const fresh = () => new Session(module);

test("Un-highlight previews and commits the kernel UnHigh rule", () => {
  const session = fresh();
  try {
    const setup = session.previewSource("N = NatForm()\nz = NatIntroZ()\nfocused = HighExp(z)");
    session.accept(setup.token);
    const before = session.inspect("focused");
    assert.equal(before.focus.side, "expression");
    const draft = session.previewFocus({ name: "focused", operation: "UnHigh", resultName: "plain" });
    assert.equal(session.engine.bindings.has("plain"), false);
    assert.equal(draft.result.focus.side, null);
    assert.equal(draft.result.expression.id, before.expression.id);
    session.accept(draft.token);
    assert.equal(session.inspect("plain").focus.side, null);
  } finally { session.dispose(); }
});

test("axiom dependencies use public aliases by checked identity without changing replay history", () => {
  const k = new Kernel(module, true);
  try {
    k.apply({ name: "N", op: "NatForm", args: [] });
    k.apply({ name: "internal", op: "Axiom", args: ["N"], hidden: true });
    k.apply({ name: "proof", op: "EqIntro", args: ["internal"] });
    assert.deepEqual(k.axiomsFor("proof"), ["internal"]);
    k.apply({ name: "public", op: "Axiom", args: ["N"] });
    assert.equal(k.bindings.get("internal").id, k.bindings.get("public").id);
    assert.deepEqual(k.axiomsFor("proof"), ["public"]);
    assert.equal(k.steps.find(s => s.name === "proof").args[0], "internal");
    k.apply({ name: "U", op: "UnitForm", args: [] });
    k.apply({ name: "different", op: "Axiom", args: ["U"] });
    assert.deepEqual(k.axiomsFor("different"), ["different"]);
    assert.deepEqual(k.axiomsFor("N"), []);
  } finally { k.dispose(); }
});

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
    assert.equal(s.metadata.length, 75);
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
test("WASM replays all 9606 native reference records, with identical successful fingerprints", async () => {
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

test("every ported proof opens, verifies its exports, and round trips as JSON and math", async () => {
  const { default: catalogue } = await import("../web/proofs/catalogue.mjs");
  const sources = JSON.parse(
    await readFile(
      new URL("../docs/proof_sources.json", import.meta.url),
      "utf8",
    ),
  );
  assert.equal(catalogue.length, 28);
  assert.deepEqual(
    new Set(
      catalogue
        .filter(
          (p) =>
            !["prelude_library", "identity", "wnat_equiv", "primes"].includes(
              p.id,
            ),
        )
        .map((p) => p.source),
    ),
    new Set(Object.keys(sources)),
  );
  for (const entry of catalogue) {
    const document = JSON.parse(
      await readFile(
        new URL(`../web/proofs/${entry.file}`, import.meta.url),
        "utf8",
      ),
    );
    const source = await readFile(
      new URL(`../web/proofs/${entry.id}.math`, import.meta.url),
      "utf8",
    );
    const s = fresh(),
      other = new Session(module, entry.allowAxioms);
    try {
      s.import(document, true);
      assert.equal(s.program().length, entry.steps, entry.id);
      assert.equal(s.allowAxioms, entry.allowAxioms);
      for (const name of entry.exports) {
        assert.equal(s.inspect(name).kind, "judgement", name);
        assert.equal(s.inspect(name).assumptions.length, 0, name);
      }
      if (entry.verify) assert.equal(s.verify(...entry.verify), true, entry.id);
      other.import(s.export());
      for (const name of entry.exports)
        assert.deepEqual(other.inspect(name), s.inspect(name));
      other.checkout(0);
      const preview = other.previewSource(source);
      other.accept(preview.token);
      for (const name of entry.exports) {
        assert.deepEqual(
          other.inspect(name).expression,
          s.inspect(name).expression,
          name,
        );
        assert.deepEqual(other.inspect(name).type, s.inspect(name).type, name);
      }
      if (entry.id === "prelude_library") {
        assert.equal(s.snapshot().bindings.filter((b) => !b.hidden).length, 51);
        assert.equal(s.inspect("LEM").expression.kind, "Axiom");
        assert.equal(s.inspect("AOC").expression.kind, "Axiom");
        const p = s.previewSource("lem_reflexive = kernel.DefEqRefl(LEM)");
        s.accept(p.token);
        assert.throws(() => s.setPolicy(false), /rejected/);
      }
    } finally {
      s.dispose();
      other.dispose();
    }
  }
});

test("opening a bundled proof adopts policy only after successful replay", async () => {
  const { default: library } = await import("../web/proofs/library.mjs");
  const s = fresh();
  try {
    s.loadDemo();
    const before = s.export();
    const bad = structuredClone(library);
    bad.steps.at(-1).args = ["missing"];
    assert.throws(() => s.import(bad, true));
    assert.deepEqual(s.export(), before);
    assert.throws(() => s.import(library), /axiom policy/);
    s.import(library, true);
    assert.equal(s.allowAxioms, true);
    s.import(before, true);
    assert.equal(s.allowAxioms, false);
    assert.equal(s.inspect("nested").expression.kind, "Ap");
  } finally {
    s.dispose();
  }
});

test("CLI opens every bundled program and exposes LEM and AOC at startup", async () => {
  const { default: catalogue } = await import("../web/proofs/catalogue.mjs");
  const commands =
    "show LEM\nshow AOC\nproofs\n" +
    catalogue.map((p) => `open ${p.id}\n`).join("") +
    "quit\n";
  const result = spawnSync(process.execPath, ["cli/repl.mjs"], {
    input: commands,
    encoding: "utf8",
    cwd: new URL("..", import.meta.url),
    timeout: 20000,
  });
  assert.equal(result.status, 0, result.stderr);
  assert.doesNotMatch(result.stdout, /ERROR:/);
  assert.match(result.stdout, /LEM \[judgement\]/);
  assert.match(result.stdout, /AOC \[judgement\]/);
  assert.equal(
    (result.stdout.match(/Opened /g) || []).length,
    catalogue.length,
  );
  assert.equal((result.stdout.match(/\nVERIFIED\n/g) || []).length, 5);
});

test("WNat equivalence has the full coherence field and cannot replay without funext", async () => {
  const document = JSON.parse(
    await readFile(
      new URL("../web/proofs/wnat_equiv.thth.json", import.meta.url),
      "utf8",
    ),
  );
  assert.equal(document.steps.filter((s) => s.op === "Axiom").length, 1);
  const s = fresh();
  try {
    s.import(document, true);
    assert.equal(s.verify("WNatToNat_isEquiv", "wnat_to_nat_isEquiv"), true);
    const stats = s.engine.stats();
    const abbreviated = s.inspect("wnat_to_nat_isEquiv");
    assert.deepEqual(abbreviated.propositions, ["WNatToNat_isEquiv"]);
    assert.equal(abbreviated.inference.op, "DefEqExtR");
    const containsOmission = (n) =>
      n.truncated || n.children.some(containsOmission);
    assert.equal(containsOmission(abbreviated.expression), true);
    const full = s.inspect("wnat_to_nat_isEquiv", {
      expand: ["expression", "type"],
    });
    const occurrences = (n) =>
      1 + n.children.reduce((count, child) => count + occurrences(child), 0);
    assert.equal(containsOmission(full.expression), false);
    assert.equal(occurrences(full.expression), 7335);
    assert.equal(occurrences(full.expression), full.expression.size);
    assert.equal(containsOmission(full.type), false);
    assert.equal(full.expression.id, abbreviated.expression.id);
    assert.equal(full.type.id, abbreviated.type.id);
    assert.deepEqual(s.engine.stats(), stats);
    assert.throws(
      () => s.inspect("wnat_to_nat_isEquiv", { expand: ["invalid"] }),
      /Unknown expression view/,
    );
    const type = s.inspect("WNatToNat_isEquiv").expression;
    assert.equal(type.kind, "Sigma");
    assert.equal(type.children[0].kind, "Pi");
    assert.equal(type.children[0].children[0].kind, "Nat");
    assert.equal(type.children[0].children[1].kind, "W");
    const eta = type.children[1],
      epsilon = eta.children[1],
      tau = epsilon.children[1];
    assert.equal(eta.kind, "Sigma");
    assert.equal(epsilon.kind, "Sigma");
    assert.equal(tau.kind, "Pi");
    assert.equal(tau.children[1].kind, "Eq");
    assert.equal(tau.children[1].children[0].kind, "Eq");
    const before = s.export();
    const forbidden = structuredClone(document);
    forbidden.policy.allowAxioms = false;
    assert.throws(() => s.import(forbidden, true), /Axiom rejected/);
    assert.deepEqual(s.export(), before);
    const broken = structuredClone(document);
    broken.steps = broken.steps.filter((step) => step.op !== "Axiom");
    assert.throws(() => s.import(broken, true), /judgement/);
    assert.deepEqual(s.export(), before);
  } finally {
    s.dispose();
  }
});

test("Euclid is a closed unbounded-primes theorem with no axiom dependencies", async () => {
  const document = JSON.parse(
    await readFile(
      new URL("../web/proofs/primes.thth.json", import.meta.url),
      "utf8",
    ),
  );
  assert.equal(document.steps.length, 4329);
  assert.equal(document.policy.allowAxioms, false);
  assert.equal(
    document.steps.some((step) => step.op === "Axiom"),
    false,
  );
  const s = fresh();
  try {
    s.import(document);
    assert.equal(
      s.verify("InfinitelyManyPrimes", "infinitely_many_primes"),
      true,
    );
    const proposition = s.inspect("InfinitelyManyPrimes").expression;
    assert.equal(proposition.kind, "Pi");
    assert.equal(proposition.children[0].kind, "Nat");
    const witness = proposition.children[1];
    assert.equal(witness.kind, "Sigma");
    assert.equal(witness.children[0].kind, "Nat");
    assert.equal(witness.children[1].kind, "Sigma");
    assert.equal(witness.children[1].children[0].kind, "Sigma");
    assert.equal(s.inspect("infinitely_many_primes").assumptions.length, 0);
    assert.deepEqual(s.inspect("infinitely_many_primes").propositions, [
      "InfinitelyManyPrimes",
    ]);
    const before = s.export();
    const broken = structuredClone(document);
    broken.steps.at(-1).args = ["InfinitelyManyPrimes"];
    assert.throws(() => s.import(broken), /rejected/);
    assert.deepEqual(s.export(), before);
    const oversized = structuredClone(document);
    oversized.steps = Array(MAX_STEPS + 1).fill(document.steps[0]);
    assert.throws(() => s.import(oversized), /Unsupported proof/);
  } finally {
    s.dispose();
  }
});
