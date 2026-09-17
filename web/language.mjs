// One binding per line and one checked instruction per binding. No eval.
export const aliases = {
  "universe.zero": "UIntro0",
  "universe.next": "UIntro",
  "universe.omega": "UIntroOmega",
  assume: "CtxExt",
  var: "Vble",
  pi: "PiForm",
  lambda: "PiIntro",
  apply: "PiElim",
  sigma: "SigmaForm",
  pair: "SigmaIntro",
  "sigma.elim": "SigmaElim",
  unit: "UnitForm",
  "unit.value": "UnitIntro",
  void: "VoidForm",
  nat: "NatForm",
  zero: "NatIntroZ",
  succ: "NatIntroS",
  "eq.type": "EqForm",
  "eq.refl": "EqIntro",
  "defeq.refl": "DefEqRefl",
  "defeq.swap": "DefEqSwp",
  define: "Def",
  "focus.expr": "HighExp",
  "focus.type": "HighType",
  "focus.parent": "HighUp",
  "focus.clear": "UnHigh",
  "rewrite.focus": "HighSubs",
  rewrite: "Subs",
  "reduce.focus": "BetaReducePointed",
  "reduce.pass": "BetaReduceGrossKnuth",
  "unfold.focus": "DefReducePointed",
  "unfold.pass": "DefBetaReduceGrossKnuth",
};
function split(text) {
  let depth = 0,
    start = 0;
  const out = [];
  for (let i = 0; i < text.length; i++) {
    if (text[i] === "[") depth++;
    if (text[i] === "]") depth--;
    if (depth < 0 || depth > 1) throw new Error("Invalid context list.");
    if (text[i] === "," && depth === 0) {
      out.push(text.slice(start, i).trim());
      start = i + 1;
    }
  }
  if (depth) throw new Error("Unclosed context list.");
  out.push(text.slice(start).trim());
  return out;
}
const ref = (s) => (s === "_" ? null : s);
export function parse(source, metadata) {
  if (typeof source !== "string" || source.length > 1000000)
    throw new Error("Source must be at most 1 MB.");
  const steps = [];
  for (const [index, raw] of source.split(/\r?\n/).entries()) {
    const text = raw.replace(/#.*$|\/\/.*$/, "").trim();
    if (!text) continue;
    try {
      const m = text.match(
        /^([A-Za-z][A-Za-z0-9_]*)\s*=\s*([A-Za-z][A-Za-z0-9_.]*)\s*\((.*)\)$/,
      );
      if (!m)
        throw new Error(
          "Use name = operation(arguments; options), one instruction per line.",
        );
      const [, name, spelling, inside] = m,
        sections = inside.split(";");
      if (sections.length > 2)
        throw new Error("Use one semicolon before options.");
      let args = sections[0].trim() ? split(sections[0]) : [];
      let op = aliases[spelling] || spelling.replace(/^kernel\./, "");
      let context = null,
        free = null,
        fresh = spelling === "assume";
      const seen = new Set();
      if (spelling === "var") {
        if (args.length !== 1) throw new Error("var requires one context.");
        context = args[0];
        args = [];
      }
      if (spelling === "focus.child") {
        if (args.length !== 2 || !/^([0-3])$/.test(args[1]))
          throw new Error(
            "focus.child requires a judgement and child index 0–3.",
          );
        op = `High${args.pop()}`;
      }
      for (const option of sections[1]?.trim() ? split(sections[1]) : []) {
        const pair = option.match(/^(context|free|bind|after)\s*:\s*(.+)$/);
        if (!pair) throw new Error(`Unknown option: ${option}`);
        const [, key, value] = pair;
        if (seen.has(key)) throw new Error(`Repeated option: ${key}`);
        seen.add(key);
        if (key === "context") {
          if (context !== null) throw new Error("Repeated context.");
          context = ref(value);
        } else {
          if (free !== null)
            throw new Error("Specify only one of free, bind, or after.");
          if (key === "after" && op !== "CtxExt")
            throw new Error("after is only valid for assumptions.");
          if (value.startsWith("[") && value.endsWith("]"))
            free = value.slice(1, -1).trim()
              ? split(value.slice(1, -1)).map(ref)
              : [];
          else free = [ref(value)];
          fresh = false;
        }
      }
      const meta = metadata.find((x) => x.name === op);
      if (!meta) throw new Error(`Unknown operation: ${spelling}`);
      steps.push({
        name,
        op,
        args,
        context,
        free: free ?? Array(meta.free).fill(null),
        fresh,
        line: index + 1,
      });
    } catch (e) {
      throw new Error(`Line ${index + 1}: ${e.message}`);
    }
  }
  if (steps.length > 4096)
    throw new Error("A program may contain at most 4096 instructions.");
  return steps;
}
export function formatStep(s) {
  const options = [];
  if (s.context) options.push(`context: ${s.context}`);
  if (s.free.length)
    options.push(`free: [${s.free.map((x) => x ?? "_").join(", ")}]`);
  return `${s.name} = kernel.${s.op}(${s.args.join(", ")}${options.length ? "; " + options.join(", ") : ""})`;
}
export const demo = `# Reduce the highlighted inner application, or explore another operation.
Unit = unit()
one = unit.value()
x = assume(Unit)
x_value = var(x)
identity = lambda(Unit, x_value; bind: x)
application = apply(identity, one)
nested = apply(identity, application)
equality = kernel.PiComp(x_value, one; free: [x])
Nat = nat()
zero = zero()`;
