import { Kernel } from "../kernel.mjs";
import { tokenize } from "./parser.mjs";
import { leadingDocumentation } from "./documentation.mjs";
import { layout } from "../expressions.mjs";
import { MAX_STEPS } from "../language.mjs";

// Explicit construction notation is the lossless escape hatch for every kernel
// rule, including focused rewrites and universe operations. It is parsed as data,
// never JavaScript. The C kernel checks every call and every verify statement.
export const constructors = {
  Nop: "noop",
  Axiom: "postulate",
  CtxExt: "assume",
  Vble: "variable",
  Def: "define",
  DefEqSwp: "definition_symmetry",
  DefEqExtL: "definition_left",
  DefEqExtR: "definition_right",
  DefEqRefl: "definition_refl",
  DefLookup: "definition_body",
  Subs: "substitute",
  HighSubs: "rewrite_selected",
  HighExp: "select_expression",
  HighType: "select_type",
  HighUp: "select_parent",
  SuspForm: "suspension_type",
  SuspNorth: "suspension_north",
  SuspSouth: "suspension_south",
  SuspMerid: "suspension_meridian",
  SuspElim: "suspension_induction",
  SuspMeridComp: "suspension_meridian_compute",
  Transport: "transport",
  Apd: "dependent_path_map",
  High0: "select_first",
  High1: "select_second",
  High2: "select_third",
  High3: "select_fourth",
  UnHigh: "clear_selection",
  UIntro0: "universe_zero",
  UIntro: "universe_above",
  UIntroOmega: "universe_omega",
  UCumul: "universe_lift",
  UCumulOmega: "universe_lift_omega",
  UCumulKappa: "universe_lift_kappa",
  UCumulContext: "universe_lift_context",
  UCumul0: "universe_lift_zero",
  UVble: "universe_variable",
  PiForm: "function_type",
  PiIntro: "function_intro",
  PiElim: "apply",
  PiComp: "function_compute",
  PiUniq: "function_eta",
  SigmaForm: "pair_type",
  SigmaIntro: "pair_intro",
  SigmaElim: "pair_eliminate",
  SigmaComp: "pair_compute",
  SumForm: "either_type",
  SumIntroL: "either_left",
  SumIntroR: "either_right",
  SumElim: "either_eliminate",
  SumCompL: "either_compute_left",
  SumCompR: "either_compute_right",
  VoidForm: "empty_type",
  VoidElim: "empty_eliminate",
  UnitForm: "unit_type",
  UnitIntro: "unit_value",
  UnitElim: "unit_eliminate",
  UnitComp: "unit_compute",
  EqForm: "equality_type",
  EqIntro: "reflexivity",
  EqElim: "equality_eliminate",
  EqComp: "equality_compute",
  NatForm: "natural_type",
  NatIntroZ: "zero",
  NatIntroS: "successor",
  NatElim: "natural_induction",
  NatCompZ: "natural_compute_zero",
  NatCompS: "natural_compute_successor",
  WForm: "tree_type",
  WIntro: "tree_intro",
  WElim: "tree_induction",
  WComp: "tree_compute",
  BetaReducePointed: "reduce_selected",
  BetaReduceGrossKnuth: "reduce_pass",
  DefReducePointed: "unfold_selected",
  DefBetaReduceGrossKnuth: "unfold_pass",
};

export function compileConstruction(module, source, { onProgress } = {}) {
  const ts = tokenize(source);
  let i = 0,
    kernel;
  const links = [],
    steps = [],
    outputs = [],
    checks = [],
    declarations = [];
  function take(expected) {
    const t = ts[i];
    if (expected && t.text !== expected)
      throw new Error(`Expected '${expected}', found '${t.text}'.`);
    if (t.text !== "EOF") i++;
    return t;
  }
  function name() {
    const t = take();
    if (!/^[A-Za-z][A-Za-z_0-9]*$/.test(t.text) || t.text === "EOF")
      throw new Error("Expected a name.");
    return t;
  }
  try {
    take("construction");
    const title = name().text;
    take("{");
    let allowAxioms = false;
    if (ts[i].text === "axioms") {
      take();
      take("allow");
      take(";");
      allowAxioms = true;
    }
    kernel = new Kernel(module, allowAxioms);
    const metadata = new Map(
      kernel.metadata.map((m) => [constructors[m.name], m]),
    );
    const byName = new Map();
    const totalStatements = ts.slice(i).filter(t => t.text === ";").length;
    const reportProgress = () => onProgress?.({
      unit: "steps",
      completed: kernel.steps.length + checks.length,
      total: totalStatements,
      current: "",
      instructions: kernel.steps.length,
    });
    while (ts[i].text !== "}") {
      if ((kernel.steps.length + checks.length) % 64 === 0) reportProgress();
      if (steps.length >= MAX_STEPS + 100)
        throw new Error("Too many construction statements.");
      const t = take();
      if (t.text === "verify") {
        const proposition = name();
        take("with");
        const proof = name();
        const end = take(";").end;
        if (!kernel.verify(proposition.text, proof.text))
          throw new Error(
            `Verification failed: ${proof.text} : ${proposition.text}.`,
          );
        for (const ref of [proposition, proof])
          links.push({
            ...byName.get(ref.text),
            start: ref.start,
            end: ref.end,
          });
        checks.push({ proposition: proposition.text, proof: proof.text });
        steps.push({
          start: t.start,
          end,
          goal: `${proof.text} : ${proposition.text}`,
          locals: [],
        });
        continue;
      }
      if (!["private", "export"].includes(t.text))
        throw new Error("Expected private, export, or verify.");
      const n = name();
      take("=");
      const operation = name();
      take("(");
      const refs = [];
      if (ts[i].text !== ")") {
        refs.push(name());
        while (ts[i].text === ",") {
          take(",");
          refs.push(name());
        }
      }
      take(")");
      const end = take(";").end;
      const fresh = operation.text === "assume_fresh";
      const meta = metadata.get(fresh ? "assume" : operation.text);
      if (!meta) throw new Error(`Unknown constructor '${operation.text}'.`);
      const count =
        meta.judgements + Number(meta.context) + (fresh ? 0 : meta.free);
      if (refs.length !== count)
        throw new Error(
          `${operation.text} requires ${count} arguments: judgements, then context, then binder slots (none for unused slots).`,
        );
      const values = refs.map((r) => (r.text === "none" ? null : r.text));
      if (kernel.steps.length >= MAX_STEPS)
        throw new Error(`Compiled proof exceeds ${MAX_STEPS} instructions.`);
      kernel.apply({
        name: n.text,
        op: meta.name,
        args: values.slice(0, meta.judgements),
        context: meta.context ? values[meta.judgements] : null,
        free: fresh
          ? [null]
          : values.slice(meta.judgements + Number(meta.context)),
        fresh,
        hidden: t.text === "private",
      });
      const binding = kernel.bindings.get(n.text);
      const info = {
        name: n.text,
        description: leadingDocumentation(source, t.start)?.text ?? "",
        binding: n.text,
        role: binding.axiom ? "explicit axiom" : binding.kind,
        type: null,
        start: n.start,
        end: n.end,
        definitionStart: t.start,
        definitionEnd: end,
      };
      byName.set(n.text, info);
      links.push(info);
      for (const ref of refs)
        if (ref.text !== "none")
          links.push({
            ...byName.get(ref.text),
            start: ref.start,
            end: ref.end,
          });
      declarations.push({
        ...info,
        private: t.text === "private",
        operation: operation.text,
      });
      steps.push({
        start: t.start,
        end,
        goal: `${n.text} = ${operation.text}(${refs.map((r) => r.text).join(", ")})`,
        locals: refs
          .filter((r) => r.text !== "none")
          .map((r) => ({ ...byName.get(r.text), type: "Checked premise" })),
      });
      if (t.text === "export")
        outputs.push({
          ...info,
          kind: info.role,
          start: t.start,
          end,
          instructions: 1,
        });
    }
    reportProgress();
    take("}");
    take("EOF");
    if (!outputs.length)
      throw new Error("Export at least one construction result.");
    // Render only exports here. Thousands of intermediate types stay lazy and
    // are inspected on demand, avoiding quadratic source-loading overhead.
    for (const output of outputs) {
      const b = kernel.bindings.get(output.binding);
      const id = module._wb_view(
        kernel.handle,
        Number(b.kind === "context"),
        b.id,
        b.kind === "context" ? 0 : 1,
      );
      output.type = layout(kernel.tree(id, { left: 80, maxDepth: 12 })).text;
      output.axioms = kernel.axiomsFor(output.binding);
      output.verified = checks.some((c) => c.proof === output.binding);
    }
    return {
      kernel,
      source,
      title,
      mode: "construction",
      links,
      steps,
      outputs,
      declarations,
      checks,
      imports: [],
      libraryCount: 0,
      instructionCount: kernel.steps.length,
      allowAxioms,
      axiomCount: kernel.steps.filter((s) => s.op === "Axiom").length,
    };
  } catch (e) {
    kernel?.dispose();
    const offset = e.offset ?? ts[Math.max(0, i - 1)].start;
    const line = source.slice(0, offset).split("\n").length;
    const column = offset - source.lastIndexOf("\n", offset - 1);
    throw Object.assign(
      new Error(`Line ${line}, column ${column}: ${e.message}`),
      { offset, line, column },
    );
  }
}
