import { compileConstruction } from "./construction.mjs";
import { Builder } from "./builder.mjs";
import { parse } from "./parser.mjs";
import { declarations } from "./library.mjs";
import preludeLibrary from "../proofs/library.mjs";
import { MAX_STEPS } from "../language.mjs";

// Bidirectional elaboration into the existing checked instruction language.
// Type descriptors carry checked judgements and closures for dependent binders;
// they never manufacture kernel nodes or bypass conversion/type checking.
export function compile(module, source, library, { onProgress, optimizations = {} } = {}) {
  if (!optimizations || typeof optimizations !== "object" || Array.isArray(optimizations) ||
      Object.entries(optimizations).some(([key, value]) =>
        !["normalForms", "instructions"].includes(key) || typeof value !== "boolean"))
    throw new Error("Compiler optimizations must contain only Boolean normalForms and instructions options.");
  if (/^\s*(?:\/\/[^\n]*\n\s*)*construction\b/.test(source)) {
    // Recorded construction instructions are replayed exactly in every mode.
    return { ...compileConstruction(module, source, { onProgress }),
      optimizations: { normalForms: false, instructions: false } };
  }
  optimizations = { normalForms: optimizations.normalForms ?? true, instructions: optimizations.instructions ?? true };
  const program = parse(source);
  const sources =
    typeof library === "string" ? { primes: library } : (library ?? {});
  const visited = new Set(),
    visiting = new Set(),
    importedDeclarations = [];
  let usesPrelude = false;
  function visit(name) {
    if (visited.has(name)) return;
    if (name === "prelude") {
      usesPrelude = true;
      visited.add(name);
      return;
    }
    if (visiting.has(name)) throw new Error(`Cyclic module import: ${name}`);
    if (typeof sources[name] !== "string")
      throw new Error(
        `The ${name} import requires its mathematical .proof source.`,
      );
    visiting.add(name);
    const p = parse(sources[name]);
    for (const dependency of p.imports) visit(dependency);
    const mark = (node) => {
      if (!node || typeof node !== "object") return;
      node.library = name;
      for (const [key, child] of Object.entries(node))
        if (key !== "library") {
          if (Array.isArray(child)) child.forEach(mark);
          else if (child && typeof child === "object") mark(child);
        }
    };
    p.declarations.forEach(mark);
    importedDeclarations.push(...p.declarations);
    visiting.delete(name);
    visited.add(name);
  }
  for (const name of program.imports) visit(name);
  const sourceDeclarations = [...importedDeclarations, ...program.declarations];
  const usesDeclaredAxioms = sourceDeclarations.some(d => d.kind === "axiom");
  const usesTruncation = sourceDeclarations.some(d => /"name":"truncation(?:_intro|_prop|_elim)?(?:_at)?"/.test(JSON.stringify(d)));
  const usesChoice = sourceDeclarations.some(d => /"name":"set_choice"/.test(JSON.stringify(d)));
  const usesClassical = sourceDeclarations.some(d => /"name":"classical_truncation"/.test(JSON.stringify(d)));
  const b = new Builder(module, {
    loadLibrary: false,
    allowAxioms: usesPrelude || usesDeclaredAxioms,
    optimizations,
  });
  const links = [],
    steps = [],
    outputs = [];
  let recording = false,
    current = null;
  try {
    const importedProgram = importedDeclarations.length
      ? { declarations: importedDeclarations }
      : null;
    if (usesPrelude) {
      // Reuse the existing checked prelude declarations, including their exact
      // axiom types. Replay only the premise closure of the requested principles.
      const byName = new Map(
        preludeLibrary.steps.map((step) => [step.name, step]),
      );
      const needed = new Set();
      function need(name) {
        if (!name || needed.has(name)) return;
        const step = byName.get(name);
        if (!step) throw new Error(`Missing prelude declaration: ${name}`);
        needed.add(name);
        [...step.args, ...step.free, step.context].forEach(need);
      }
      ["lib_univalence", "lib_ua_elim", "lib_funext", "lib_isEquiv"].forEach(
        need,
      );
      if (usesTruncation)
        ["lib_Trunc", "lib_trunc_intro", "lib_trunc_is_trunc", "lib_trunc_elim"].forEach(need);
      if (usesChoice) need("AOC");
      if (usesClassical) need("LEM");
      if (usesChoice || usesClassical) need("lib_Trunc");
      for (const step of preludeLibrary.steps)
        if (needed.has(step.name)) b.k.apply(step);
    }
    b.serial = 100000;
    b.maxSteps = MAX_STEPS;
    b.opaque = true;
    const op = (...args) => b.emit(...args),
      norm = (x) => b.norm(x);
    const env = new Map();
    const U = op("UIntro0"),
      U1 = op("UIntro", [U]),
      N = op("NatForm"),
      V = op("VoidForm"),
      Unit = op("UnitForm");
    const atom = (j, pretty) => ({ j, kind: "atom", pretty });
    const type = atom(U, "Type"),
      nat = atom(N, "Nat"),
      voidType = atom(V, "Void");
    const smallTypes = new Map();
    let indexedTypes = 0;
    function smallestKnownType(T) {
      // Reuse a previously checked small-universe judgement of the same type
      // and assumption set. This never lowers a universe by assertion: the
      // replacement premise already exists in the kernel. It avoids propagating
      // an unnecessary Type1 lift into equalities between paths in a small type.
      while (indexedTypes < b.k.steps.length) {
        const step = b.k.steps[indexedTypes++],
          binding = b.k.bindings.get(step.name);
        if (binding.kind !== "judgement" || b.view(step.name, 4)) continue;
        const sort = b.k.node(b.view(step.name, 1));
        if (sort.kind !== "U") continue;
        const key = `${b.view(step.name, 0)}:${b.view(step.name, 2)}`,
          old = smallTypes.get(key);
        if (!old || sort.parameter < old.level)
          smallTypes.set(key, { j: step.name, level: sort.parameter });
      }
      const known = smallTypes.get(`${b.view(T.j, 0)}:${b.view(T.j, 2)}`);
      return known ? { ...T, j: known.j } : T;
    }
    function equalityType(A, x, y, pretty = `${x.display} = ${y.display}`) {
      A = smallestKnownType(A);
      return {
        j: b.eq(A.j, x.binding, y.binding),
        kind: "atom",
        pretty,
        equality: () => ({ carrier: A, from: x, to: y }),
      };
    }
    function val(binding, type, display, extra = {}) {
      return { binding, type, display, ...extra };
    }
    env.set("Type", val(U, atom(U1, "Type1"), "Type"));
    env.set("Nat", val(N, type, "Nat"));
    env.set("Void", val(V, type, "Void"));
    env.set("Unit", val(Unit, type, "Unit"));
    env.set("tt", val(op("UnitIntro"), atom(Unit, "Unit"), "tt"));
    const universes = [U, U1];
    function sortType(binding) {
      const sort = b.k.node(b.view(binding, 1));
      if (sort.kind !== "U") return null;
      while (universes.length <= sort.parameter)
        universes.push(op("UIntro", [universes.at(-1)]));
      return atom(
        universes[sort.parameter],
        sort.parameter ? `Type${sort.parameter}` : "Type",
      );
    }
    for (let i = 1; i <= 3; i++) {
      while (universes.length <= i + 1)
        universes.push(op("UIntro", [universes.at(-1)]));
      env.set(
        `Type${i}`,
        val(universes[i], atom(universes[i + 1], `Type${i + 1}`), `Type${i}`),
      );
    }
    const instantiated = new Map();
    function pi(A, body, label = "_") {
      const x = b.fresh(A.j),
        C = body(val(x.v, A, label));
      return {
        kind: "pi",
        j: op("PiForm", [A.j, C.j], [x.c]),
        domain: A,
        binder: { ...x, label },
        template: C,
        body: (a) => instantiateType(C, [{ ...x, label }], [a]),
        pretty:
          label === "_"
            ? `${A.pretty} -> ${C.pretty}`
            : `forall ${label} : ${A.pretty}, ${C.pretty}`,
      };
    }
    function sigma(A, body, label = "_") {
      const x = b.fresh(A.j),
        C = body(val(x.v, A, label));
      return {
        kind: "sigma",
        j: op("SigmaForm", [A.j, C.j], [x.c]),
        domain: A,
        binder: { ...x, label },
        template: C,
        body: (a) => instantiateType(C, [{ ...x, label }], [a]),
        pretty:
          label === "_"
            ? `${A.pretty} and ${C.pretty}`
            : `exists ${label} : ${A.pretty}, ${C.pretty}`,
      };
    }
    const numeralCache = [val(op("NatIntroZ"), nat, "0")];
    function numeral(n) {
      while (numeralCache.length <= n)
        numeralCache.push(
          val(
            op("NatIntroS", [numeralCache.at(-1).binding]),
            nat,
            String(numeralCache.length),
          ),
        );
      return numeralCache[n];
    }
    env.set(
      "succ",
      val(
        b.lam(N, (n) => op("NatIntroS", [n])),
        pi(nat, () => nat),
        "succ",
      ),
    );
    function extend(e, name, value, token) {
      if (e.has(name))
        throw Object.assign(
          new Error(
            `Name '${name}' is already in scope; choose a distinct name.`,
          ),
          { offset: token?.start },
        );
      const next = new Map(e);
      next.set(name, { ...value, display: name });
      return next;
    }
    function describe(n, e) {
      if (n.kind === "name") return e.get(n.name)?.display ?? n.name;
      if (n.kind === "number") return String(n.value);
      if (n.kind === "call")
        return `${describe(n.fn, e)}(${n.args.map((x) => describe(x, e)).join(", ")})`;
      if (n.kind === "binary")
        return `(${describe(n.left, e)} ${n.operator} ${describe(n.right, e)})`;
      return (sources[n.library] ?? source).slice(n.start, n.end);
    }
    function record(node, value, role = "expression") {
      if (recording && !node.library)
        links.push({
          start: node.start,
          end: node.end,
          name: value.display,
          binding: value.binding,
          type: value.type.pretty,
          role,
        });
      return value;
    }
    function convert(value, T) {
      // Cumulativity is a checked inference on a type-valued argument.
      const actualSort = b.k.node(b.view(value.binding, 1)),
        targetSort = b.k.node(b.view(T.j, 0));
      if (
        actualSort.kind === "U" &&
        targetSort.kind === "U" &&
        actualSort.parameter < targetSort.parameter
      ) {
        let binding = value.binding;
        for (let i = actualSort.parameter; i < targetSort.parameter; i++)
          binding = op("UCumul", [binding]);
        value = { ...value, binding, type: T };
      }
      try {
        return { ...value, binding: b.coerce(value.binding, T.j), type: T };
      } catch (error) {
        // Definitions remain boxed during ordinary normalization. Conversion
        // may unfold their checked bodies when needed, and restores the named
        // target type with an explicit definitional-equality witness.
        if (b.opaque && error.message === "Conversion types differ") {
          try {
            return {
              ...value,
              binding: b.coerceDefinitions(value.binding, T.j),
              type: T,
            };
          } catch (expandedError) {
            error = expandedError;
          }
        }
        throw new Error(
          `Expected ${T.pretty}; got ${value.type.pretty}. ${error.message}`,
        );
      }
    }
    function apply(f, args) {
      for (const argument of args) {
        if (f.type.kind !== "pi")
          throw new Error(`${f.display} is not a function.`);
        const a = convert(argument, f.type.domain),
          C = f.type.body(a);
        const template = f.functionTemplate;
        const extra = template
          ? mapMeta(
              template.body,
              (j) => {
                let f = op(
                  "PiIntro",
                  [template.binder.A, j],
                  [template.binder.c],
                );
                if (template.transform) f = template.transform(f);
                return b.app(f, a.binding);
              },
              (text) =>
                replaceWord(
                  template.prettyTransform
                    ? template.prettyTransform(text)
                    : text,
                  template.binder.label,
                  a.display,
                ),
            )
          : {};
        f = val(
          b.app(f.binding, a.binding),
          C,
          `${f.display}(${a.display})`,
          extra,
        );
      }
      return f;
    }
    function asType(n, e) {
      if (!n.library) current = n;
      if (n.kind === "forall" || n.kind === "exists") {
        const A = asType(n.domain, e),
          body = (x) => asType(n.body, new Map(e).set(n.name.text, x));
        return n.kind === "forall"
          ? pi(A, body, n.name.text)
          : sigma(A, body, n.name.text);
      }
      if (n.kind === "binary" && ["and", "or", "->"].includes(n.operator)) {
        const A = asType(n.left, e),
          C = asType(n.right, e);
        if (n.operator === "and") return sigma(A, () => C);
        if (n.operator === "->") return pi(A, () => C);
        return {
          kind: "sum",
          j: op("SumForm", [A.j, C.j]),
          left: A,
          right: C,
          pretty: `${A.pretty} or ${C.pretty}`,
        };
      }
      const v = infer(n, e),
        sort = b.k.node(b.view(v.binding, 1));
      if (!["U", "UUOmega", "UUKappa"].includes(sort.kind))
        throw new Error(`${describe(n, e)} is a term, not a type.`);
      return {
        ...(v.representedType ?? atom(v.binding, describe(n, e))),
        j: v.binding,
        pretty: describe(n, e),
      };
    }
    function infer(n, e) {
      if (!n.library) current = n;
      let v;
      if (n.kind === "induction") {
        const natNode = {
          kind: "name",
          name: "Nat",
          start: n.index.start,
          end: n.index.end,
          library: true,
        };
        const motive = {
          kind: "lambda",
          name: n.index,
          domain: natNode,
          body: n.type,
          start: n.type.start,
          end: n.type.end,
        };
        const hypothesis = {
          kind: "lambda",
          name: n.hypothesis,
          domain: n.type,
          body: n.step,
          start: n.step.start,
          end: n.step.end,
        };
        const branch = {
          kind: "lambda",
          name: n.index,
          domain: natNode,
          body: hypothesis,
          start: n.step.start,
          end: n.step.end,
        };
        v = primitives.induct([n.value, motive, n.base, branch], e);
      } else if (n.kind === "match") {
        const value = infer(n.value, e),
          T = value.type;
        if (T.kind !== "sum") throw new Error("match requires an or value.");
        const z = n.motiveName ? b.fresh(T.j) : null;
        const at = (v) =>
          asType(
            n.type,
            n.motiveName ? new Map(e).set(n.motiveName.text, v) : e,
          );
        const C = at(z ? val(z.v, T, n.motiveName.text) : value);
        const x = b.fresh(T.left.j),
          y = b.fresh(T.right.j),
          vx = val(x.v, T.left, n.left.text),
          vy = val(y.v, T.right, n.right.text),
          il = val(
            op("SumIntroL", [T.left.j, T.right.j, x.v]),
            T,
            `left(${vx.display})`,
          ),
          ir = val(
            op("SumIntroR", [T.left.j, T.right.j, y.v]),
            T,
            `right(${vy.display})`,
          );
        record(n.left, vx, "local");
        record(n.right, vy, "local");
        const le = new Map(e).set(n.left.text, vx),
          re = new Map(e).set(n.right.text, vy);
        if (n.motiveName) {
          le.set(n.motiveName.text, il);
          re.set(n.motiveName.text, ir);
        }
        const l = check(n.leftBody, le, at(il)),
          r = check(n.rightBody, re, at(ir));
        const exact = (branch, injection) =>
          z
            ? b.coerce(branch.binding, b.subst(C.j, z, injection.binding))
            : b.coerce(branch.binding, C.j);
        v = val(
          norm(
            op(
              "SumElim",
              [C.j, exact(l, il), exact(r, ir), value.binding],
              [z?.c ?? null, x.c, y.c],
            ),
          ),
          at(value),
          "case analysis",
        );
      } else if (n.kind === "unpack") {
        const value = infer(n.value, e),
          T = value.type,
          C = asType(n.type, e);
        if (T.kind !== "sigma")
          throw new Error("unpack requires an exists/and value.");
        const x = b.fresh(T.domain.j),
          vx = val(x.v, T.domain, n.left.text),
          B = T.body(vx),
          y = b.fresh(B.j),
          vy = val(y.v, B, n.right.text);
        record(n.left, vx, "local");
        record(n.right, vy, "local");
        const branch = check(
          n.body,
          new Map(e).set(n.left.text, vx).set(n.right.text, vy),
          C,
        );
        v = val(
          norm(
            op(
              "SigmaElim",
              [C.j, branch.binding, value.binding],
              [null, x.c, y.c],
            ),
          ),
          C,
          "unpacked result",
        );
      } else if (n.kind === "lambda") {
        const A = asType(n.domain, e),
          x = b.fresh(A.j),
          vx = val(x.v, A, n.name.text);
        record(n.name, vx, "parameter");
        const body = infer(n.body, new Map(e).set(n.name.text, vx));
        const T = {
          kind: "pi",
          j: op("PiForm", [A.j, body.type.j], [x.c]),
          domain: A,
          binder: { ...x, label: n.name.text },
          template: body.type,
          body: (a) =>
            instantiateType(body.type, [{ ...x, label: n.name.text }], [a]),
          pretty: `forall ${n.name.text} : ${A.pretty}, ${body.type.pretty}`,
        };
        v = val(op("PiIntro", [A.j, body.binding], [x.c]), T, "function", {
          functionTemplate: {
            body,
            binder: { ...x, label: n.name.text },
            variables: [],
            values: [],
          },
        });
      } else if (n.kind === "name") {
        v = e.get(n.name);
        if (!v) throw new Error(`Unknown name '${n.name}'.`);
      } else if (n.kind === "number") v = numeral(n.value);
      else if (n.kind === "call") {
        const primitive = n.fn.kind === "name" ? primitives[n.fn.name] : null;
        if (primitive) {
          v = primitive(n.args, e);
          const principle = {
            univalence: ["lib_univalence", "Equiv(A, B) -> (A = B)"],
            univalence_beta: [
              "lib_ua_elim",
              "Transport along univalence equals the equivalence function",
            ],
            truncation: ["lib_Trunc", "Type -> Type"],
            truncation_intro: ["lib_trunc_intro", "A -> Mere(A)"],
            truncation_prop: ["lib_trunc_is_trunc", "IsProp(Mere(A))"],
            truncation_elim: ["lib_trunc_elim", "IsProp(P) -> (A -> P) -> Mere(A) -> P"],
            truncation_at: ["lib_Trunc", "Universe-indexed propositional truncation"],
            truncation_intro_at: ["lib_trunc_intro", "Universe-indexed truncation introduction"],
            truncation_prop_at: ["lib_trunc_is_trunc", "Universe-indexed truncation is a proposition"],
            truncation_elim_at: ["lib_trunc_elim", "Universe-indexed truncation elimination into propositions"],
            funext_at: ["lib_funext", "Universe-indexed function extensionality"],
            set_choice: ["AOC", "Choice for a family of inhabited sets indexed by a set"],
            classical_truncation: ["LEM", "Double negation implies mere inhabitation"],
            funext: [
              "lib_funext",
              "Pointwise equality implies function equality",
            ],
          }[n.fn.name];
          if (principle && recording && !n.library)
            links.push({
              start: n.fn.start,
              end: n.fn.end,
              name: n.fn.name,
              binding: principle[0],
              type: principle[1],
              role: "existing prelude axiom",
              sourceModule: "prelude_library_construction",
              sourceName: principle[0],
            });
        } else if (n.fn.kind === "name" && n.fn.name === "refl") {
          if (n.args.length !== 1) throw new Error("refl requires one term.");
          const raw = infer(n.args[0], e),
            x = convert(raw, raw.type);
          v = val(
            b.refl(x.binding),
            equalityType(x.type, x, x),
            describe(n, e),
          );
        } else
          v = apply(
            infer(n.fn, e),
            n.args.map((arg) => infer(arg, e)),
          );
      } else if (
        n.kind === "binary" &&
        ["+", "*", "<", "<=", "="].includes(n.operator)
      ) {
        let x = infer(n.left, e),
          y = infer(n.right, e);
        if (n.operator === "=") {
          x = convert(x, x.type);
          y = convert(y, x.type);
          const E = equalityType(x.type, x, y, describe(n, e));
          v = val(E.j, type, describe(n, e), { representedType: E });
        } else {
          x = convert(x, nat);
          y = convert(y, nat);
          const name =
            n.operator === "+" ? "add" : n.operator === "*" ? "mul" : "le";
          if (!e.has(name))
            throw new Error(`Import primes to use '${n.operator}'.`);
          if (n.operator === "<" && e.has("isLt"))
            v = apply(e.get("isLt"), [x, y]);
          else {
            if (n.operator === "<") x = apply(env.get("succ"), [x]);
            v = apply(e.get(name), [x, y]);
          }
        }
      } else if (["forall", "exists"].includes(n.kind) || n.kind === "binary") {
        const T = asType(n, e);
        v = val(T.j, type, T.pretty, { representedType: T });
      } else
        throw new Error(
          "A pair needs an expected exists/and type. Use exact inside a typed theorem or have block.",
        );
      if (
        recording &&
        !n.library &&
        n.operatorStart !== undefined &&
        ["+", "*", "<", "<=", "="].includes(n.operator)
      ) {
        const name = {
            "+": "add",
            "*": "mul",
            "<": "isLt",
            "<=": "le",
            "=": "Eq",
          }[n.operator],
          entry = e.get(name);
        links.push({
          start: n.operatorStart,
          end: n.operatorEnd,
          name: n.operator,
          binding: entry?.binding ?? v.binding,
          type: entry?.type.pretty ?? "Equality type",
          role: "notation",
          sourceModule: entry ? "primes" : undefined,
          sourceName: name,
          description:
            n.operator === "="
              ? `a = b denotes Eq(A, a, b), where A is the checked type of a and b.`
              : `a ${n.operator} b denotes ${name}(a, b), applied as (${name}(a))(b).${n.operator === "<" ? " isLt(a, b) is le(succ(a), b)." : ""}`,
        });
      }
      if (
        !v.representedType &&
        ["U", "UUOmega", "UUKappa"].includes(
          b.k.node(b.view(v.binding, 1)).kind,
        )
      )
        v.representedType = atom(v.binding, describe(n, e));
      // In particular a quantified type over Type lives in Type1, not Type.
      // Obtain its sort from the checked judgement rather than guessing U0.
      const sort = sortType(v.binding);
      if (sort) v = { ...v, type: sort };
      return record(n, { ...v, display: describe(n, e) });
    }
    function check(n, e, T) {
      if (!n.library) current = n;
      if (
        n.kind === "call" &&
        n.fn.kind === "name" &&
        ["left", "right"].includes(n.fn.name)
      ) {
        if (T.kind !== "sum" || n.args.length !== 1)
          throw new Error(
            "left/right requires one value and an expected or type.",
          );
        const left = n.fn.name === "left",
          x = check(n.args[0], e, left ? T.left : T.right);
        return val(
          op(left ? "SumIntroL" : "SumIntroR", [
            T.left.j,
            T.right.j,
            x.binding,
          ]),
          T,
          describe(n, e),
        );
      }
      if (n.kind === "pair") {
        if (T.kind !== "sigma")
          throw new Error("Expected an exists/and type for this pair.");
        const x = check(n.left, e, T.domain),
          C = T.body(x),
          y = check(n.right, e, C),
          fresh = b.fresh(T.domain.j),
          family = T.body(val(fresh.v, T.domain, "_"));
        return record(
          n,
          val(
            op(
              "SigmaIntro",
              [
                x.binding,
                family.j,
                b.coerce(y.binding, b.subst(family.j, fresh, x.binding)),
              ],
              [fresh.c],
            ),
            T,
            describe(n, e),
          ),
        );
      }
      if (n.kind === "call" && n.fn.kind === "name" && n.fn.name === "absurd") {
        if (n.args.length !== 1)
          throw new Error("absurd requires one proof of Void.");
        const impossible = check(n.args[0], e, voidType);
        return record(
          n,
          val(
            op("VoidElim", [T.j, impossible.binding], [null]),
            T,
            describe(n, e),
          ),
        );
      }
      return convert(infer(n, e), T);
    }
    // Substitute checked type judgements while retaining their binder structure.
    // This is used for inferred lambdas; proof bodies are not re-elaborated at
    // every application. All substitutions still go through kernel rules.
    function abstractApply(j, variables, values) {
      for (const x of [...variables].reverse())
        j = op("PiIntro", [x.A, j], [x.c]);
      for (const value of values) j = b.app(j, value.binding);
      return j;
    }
    function replaceWord(text, name, value) {
      return text.replace(new RegExp(`\\b${name}\\b`, "g"), () => value);
    }
    function mapType(T, transform, prettyTransform = (text) => text) {
      const root = T.originalType ?? T;
      const composed = T.typeTransform
        ? (j) => transform(T.typeTransform(j))
        : transform;
      const combinedPretty = T.prettyTransform
        ? (text) => prettyTransform(T.prettyTransform(text))
        : prettyTransform;
      const out = {
        ...T,
        j: transform(T.j),
        pretty: prettyTransform(T.pretty),
        originalType: root,
        typeTransform: composed,
        prettyTransform: combinedPretty,
      };
      if (root.equality) {
        let cached;
        out.equality = () => {
          if (cached) return cached;
          const eq = root.equality();
          const term = (v) =>
            val(
              composed(v.binding),
              mapType(v.type, composed, combinedPretty),
              combinedPretty(v.display),
              mapMeta(v, composed, combinedPretty),
            );
          return (cached = {
            carrier: mapType(eq.carrier, composed, combinedPretty),
            from: term(eq.from),
            to: term(eq.to),
          });
        };
      }
      if (root.parameter)
        out.parameter = mapType(root.parameter, composed, combinedPretty);
      if (root.domain)
        out.domain = mapType(root.domain, composed, combinedPretty);
      if (root.template)
        out.body = (a) =>
          mapType(
            root.template,
            (j) =>
              b.app(
                composed(op("PiIntro", [root.binder.A, j], [root.binder.c])),
                a.binding,
              ),
            (text) =>
              replaceWord(combinedPretty(text), root.binder.label, a.display),
          );
      if (root.left) out.left = mapType(root.left, composed, combinedPretty);
      if (root.right) out.right = mapType(root.right, composed, combinedPretty);
      return out;
    }
    function instantiateType(T, variables, values) {
      const key =
        T.j +
        ":" +
        variables.map((x) => x.c).join(",") +
        ":" +
        values.map((x) => x.binding).join(",");
      if (instantiated.has(key)) return instantiated.get(key);
      const rename = (text) => {
        for (let i = 0; i < variables.length; i++)
          text = replaceWord(text, variables[i].label, values[i].display);
        return text;
      };
      const out = mapType(
        T,
        (j) => abstractApply(j, variables, values),
        rename,
      );
      instantiated.set(key, out);
      return out;
    }
    function mapMeta(value, transform, prettyTransform = (text) => text) {
      const extra = {};
      if (value.representedType)
        extra.representedType = mapType(
          value.representedType,
          transform,
          prettyTransform,
        );
      if (value.functionTemplate) {
        const t = value.functionTemplate;
        extra.functionTemplate = {
          ...t,
          transform: t.transform ? (j) => transform(t.transform(j)) : transform,
          prettyTransform: t.prettyTransform
            ? (text) => prettyTransform(t.prettyTransform(text))
            : prettyTransform,
        };
      }
      return extra;
    }
    function represented(value) {
      const sort = b.k.node(b.view(value.binding, 1));
      if (!["U", "UUOmega", "UUKappa"].includes(sort.kind))
        throw new Error("The motive must return a type.");
      return {
        ...(value.representedType ?? atom(value.binding, value.display)),
        j: value.binding,
      };
    }
    function arity(args, n, label) {
      if (args.length !== n)
        throw new Error(`${label} requires ${n} arguments.`);
    }
    function pathInduction(A, motive, base, x, y, p) {
      const a = b.fresh(A.j),
        c = b.fresh(A.j),
        eqT = atom(b.eq(A.j, a.v, c.v), "path"),
        q = b.fresh(eqT.j),
        z = b.fresh(A.j);
      const av = val(a.v, A, "path_from"),
        cv = val(c.v, A, "path_to"),
        qv = val(q.v, eqT, "path");
      const C = represented(apply(motive, [av, cv, qv]));
      const specialize = (body, vars, values) => {
        let f = body;
        for (const v of [...vars].reverse()) f = op("PiIntro", [v.A, f], [v.c]);
        for (const value of values)
          f = op("UnHigh", [
            op("BetaReducePointed", [
              op("HighExp", [op("PiElim", [f, value])]),
            ]),
          ]);
        return f;
      };
      const baseValue = apply(base, [val(z.v, A, "path_base")]);
      const exactBase = b.coerce(
        baseValue.binding,
        specialize(C.j, [a, c, q], [z.v, z.v, b.refl(z.v)]),
      );
      const result = norm(
        op(
          "EqElim",
          [C.j, exactBase, x.binding, y.binding, p.binding],
          [a.c, c.c, q.c, z.c],
        ),
      );
      return val(
        result,
        represented(apply(motive, [x, y, p])),
        "path induction",
      );
    }
    // Keep raw applications for premises whose kernel type is C(point). The
    // ordinary application helper normalizes; conversion restores these exact
    // types before the native dependent-elimination checks.
    function familyAt(C, point) {
      const result = apply(C, [point]);
      return {
        ...represented(result),
        j: op("PiElim", [C.binding, point.binding]),
      };
    }
    function suspensionData(args, e) {
      const C = infer(args[0], e),
        S = C.type.domain;
      if (C.type.kind !== "pi" || S.kind !== "suspension")
        throw new Error(
          "The suspension motive must be a function on Suspension(A).",
        );
      const A = S.parameter,
        n = val(op("SuspNorth", [A.j]), S, "north"),
        s = val(op("SuspSouth", [A.j]), S, "south"),
        cn = check(args[1], e, familyAt(C, n)),
        cs = check(args[2], e, familyAt(C, s));
      const H = pi(A, (a) => {
        const p = op("SuspMerid", [A.j, a.binding]),
          moved = op("Transport", [
            C.binding,
            n.binding,
            s.binding,
            p,
            cn.binding,
          ]);
        return atom(b.eq(cs.type.j, moved, cs.binding), "meridian coherence");
      });
      const h = check(args[3], e, H);
      return { C, S, A, cn, cs, h };
    }
    function withPrelude(action) {
      if (!usesPrelude)
        throw new Error(
          "Import prelude to use the existing classical, choice, truncation, or univalence/function-extensionality principles.",
        );
      const previous = b.opaque;
      b.opaque = false;
      try {
        return action();
      } finally {
        b.opaque = previous;
      }
    }
    // Open only the library signature. User arguments may contain opaque
    // proof definitions and must retain their names when the axiom is applied.
    function preludeAxiom(name) {
      return withPrelude(() => {
        let current = op("HighType", [name]);
        for (let i = 0; i < 100; i++) {
          const next = op("DefBetaReduceGrossKnuth", [current]);
          if (b.view(current, 1) === b.view(next, 1))
            return op("UnHigh", [next]);
          current = next;
        }
        throw new Error(`Prelude signature did not normalize: ${name}`);
      });
    }
    function nativeEquivalence(A, B, value) {
      const arrow = b.arrow(A.j, B.j),
        f = b.fresh(arrow),
        family = b.app("lib_isEquiv", op("UCumulOmega", [U]), A.j, B.j, f.v),
        E = norm(op("SigmaForm", [arrow, family], [f.c]));
      return b.coerce(value.binding, E);
    }
    function forwardEquivalence(A, B, proof) {
      const arrow = b.arrow(A.j, B.j),
        f = b.fresh(arrow),
        family = b.app("lib_isEquiv", op("UCumulOmega", [U]), A.j, B.j, f.v),
        h = b.fresh(family);
      return norm(op("SigmaElim", [arrow, f.v, proof], [null, f.c, h.c]));
    }
    function pathData(p) {
      if (!p.type.equality)
        throw new Error(
          "This path needs an explicit equality type annotation.",
        );
      return p.type.equality();
    }
    function asValue(A) {
      return val(A.j, sortType(A.j), A.pretty, { representedType: A });
    }
    function explicitUniverse(n, e) {
      const universe = asType(n, e);
      if (b.k.node(b.view(universe.j, 0)).kind !== "U")
        throw new Error("Expected a universe such as Type, Type1, or Type2.");
      return universe;
    }
    function typeInUniverse(n, e, universe) {
      const T = asType(n, e);
      return { ...T, j: convert(asValue(T), atom(universe.j, universe.pretty)).binding };
    }
    function pathFunction(e, name) {
      if (!e.has(name)) throw new Error(`Import paths to use ${name}.`);
      return e.get(name);
    }
    const primitives = {
      sym(args, e) {
        arity(args, 1, "sym");
        const p = infer(args[0], e),
          { carrier: A, from: x, to: y } = pathData(p);
        return apply(pathFunction(e, "inverse"), [asValue(A), x, y, p]);
      },
      trans(args, e) {
        arity(args, 2, "trans");
        const p = infer(args[0], e),
          q = infer(args[1], e),
          a = pathData(p),
          b = pathData(q);
        return apply(pathFunction(e, "concatenate"), [
          asValue(a.carrier),
          a.from,
          a.to,
          b.to,
          p,
          q,
        ]);
      },
      cong(args, e) {
        arity(args, 2, "cong");
        const f = infer(args[0], e),
          p = infer(args[1], e),
          { carrier: A, from: x, to: y } = pathData(p);
        if (f.type.kind !== "pi") throw new Error("cong needs a function.");
        return apply(pathFunction(e, "ap"), [
          asValue(A),
          asValue(f.type.body(x)),
          f,
          x,
          y,
          p,
        ]);
      },
      univalence(args, e) {
        arity(args, 3, "univalence");
        const A = asType(args[0], e),
          B = asType(args[1], e),
          evidence = infer(args[2], e);
        return withPrelude(() => {
          const eqv = nativeEquivalence(A, B, evidence),
            result = b.app(
              "lib_univalence",
              op("UCumulOmega", [U]),
              A.j,
              B.j,
              eqv,
            );
          return val(
            result,
            atom(b.eq(U, A.j, B.j), `${A.pretty} = ${B.pretty}`),
            "univalence",
          );
        });
      },
      univalence_beta(args, e) {
        arity(args, 4, "univalence_beta");
        const A = asType(args[0], e),
          B = asType(args[1], e),
          evidence = infer(args[2], e),
          x = check(args[3], e, A);
        return withPrelude(() => {
          const eqv = nativeEquivalence(A, B, evidence),
            path = b.app(
              "lib_univalence",
              op("UCumulOmega", [U]),
              A.j,
              B.j,
              eqv,
            ),
            id = b.lam(U, (T) => T),
            xAtA = b.coerce(x.binding, op("PiElim", [id, A.j])),
            moved = norm(op("Transport", [id, A.j, B.j, path, xAtA])),
            image = b.app(forwardEquivalence(A, B, eqv), x.binding),
            T = atom(b.eq(B.j, moved, image), "univalence computation"),
            proof = b.app(
              "lib_ua_elim",
              op("UCumulOmega", [U1]),
              U,
              A.j,
              B.j,
              eqv,
              x.binding,
            );
          return convert(val(proof, T, "univalence computation"), T);
        });
      },
      funext(args, e) {
        arity(args, 5, "funext");
        const A = asType(args[0], e),
          B = infer(args[1], e),
          F = pi(A, (x) => represented(apply(B, [x]))),
          f = check(args[2], e, F),
          g = check(args[3], e, F),
          H = pi(A, (x) =>
            atom(
              b.eq(F.body(x).j, apply(f, [x]).binding, apply(g, [x]).binding),
              "pointwise equality",
            ),
          ),
          h = check(args[4], e, H);
        // Unfold the library signature before specializing it. Unfolding the
        // whole application would also expand opaque user definitions inside
        // its arguments and change the endpoints of the resulting equality.
        const axiom = preludeAxiom("lib_funext");
        return val(
          b.app(
            axiom,
            op("UCumulOmega", [U]),
            A.j,
            B.binding,
            f.binding,
            g.binding,
            h.binding,
          ),
          atom(b.eq(F.j, f.binding, g.binding), "function equality"),
          "function extensionality",
        );
      },
      // Dependent elimination of a pair. All formation, branch substitution,
      // and discharge checks are performed by the existing Sigma rules.
      pair_induction(args, e) {
        arity(args, 3, "pair_induction");
        const C = infer(args[0], e),
          p = infer(args[2], e),
          T = p.type;
        if (T.kind !== "sigma")
          throw new Error("pair_induction requires a dependent pair.");
        const z = b.fresh(T.j),
          x = b.fresh(T.domain.j),
          vx = val(x.v, T.domain, "first"),
          B = T.body(vx),
          y = b.fresh(B.j),
          vy = val(y.v, B, "second"),
          a = b.fresh(T.domain.j),
          family = T.body(val(a.v, T.domain, "index")),
          pair = val(
            op(
              "SigmaIntro",
              [x.v, family.j, b.coerce(y.v, b.subst(family.j, a, x.v))],
              [a.c],
            ),
            T,
            "pair",
          ),
          motive = represented(apply(C, [val(z.v, T, "pair")])),
          branch = apply(infer(args[1], e), [vx, vy]);
        return val(
          norm(
            op(
              "SigmaElim",
              [
                motive.j,
                b.coerce(branch.binding, b.subst(motive.j, z, pair.binding)),
                p.binding,
              ],
              [z.c, x.c, y.c],
            ),
          ),
          represented(apply(C, [p])),
          "pair induction",
        );
      },
      truncation_at(args, e) {
        arity(args, 2, "truncation_at");
        const universe = explicitUniverse(args[0], e),
          A = typeInUniverse(args[1], e, universe),
          axiom = preludeAxiom("lib_Trunc"),
          j = b.app(axiom, op("UCumulOmega", [universe.j]), A.j);
        return val(j, type, `Mere[${universe.pretty}](${A.pretty})`, {
          representedType: atom(j, `Mere[${universe.pretty}](${A.pretty})`),
        });
      },
      truncation_intro_at(args, e) {
        arity(args, 3, "truncation_intro_at");
        const universe = explicitUniverse(args[0], e),
          A = typeInUniverse(args[1], e, universe),
          a = check(args[2], e, A),
          axiom = preludeAxiom("lib_trunc_intro"),
          u = op("UCumulOmega", [universe.j]),
          T = atom(b.app("lib_Trunc", u, A.j), `Mere[${universe.pretty}](${A.pretty})`);
        return val(b.app(axiom, u, A.j, a.binding), T, "truncation introduction");
      },
      truncation_prop_at(args, e) {
        arity(args, 2, "truncation_prop_at");
        const universe = explicitUniverse(args[0], e),
          A = typeInUniverse(args[1], e, universe),
          axiom = preludeAxiom("lib_trunc_is_trunc"),
          u = op("UCumulOmega", [universe.j]),
          T = atom(b.app("lib_Trunc", u, A.j), `Mere[${universe.pretty}](${A.pretty})`),
          P = pi(T, x => pi(T, y => equalityType(T, x, y)));
        return val(b.coerce(b.app(axiom, u, A.j), P.j), P, "truncation is a proposition");
      },
      truncation_elim_at(args, e) {
        arity(args, 5, "truncation_elim_at");
        const universe = explicitUniverse(args[0], e),
          A = typeInUniverse(args[1], e, universe),
          P = typeInUniverse(args[2], e, universe),
          isProp = pi(P, x => pi(P, y => equalityType(P, x, y))),
          proposition = check(args[3], e, isProp),
          f = check(args[4], e, pi(A, () => P)),
          axiom = preludeAxiom("lib_trunc_elim"),
          u = op("UCumulOmega", [universe.j]),
          premise = op("SigmaIntro", [f.binding, isProp.j, proposition.binding], [null]),
          T = atom(b.app("lib_Trunc", u, A.j), `Mere[${universe.pretty}](${A.pretty})`);
        return val(b.app(axiom, u, A.j, P.j, premise), pi(T, () => P), "truncation elimination");
      },
      funext_at(args, e) {
        arity(args, 6, "funext_at");
        const universe = explicitUniverse(args[0], e),
          A = typeInUniverse(args[1], e, universe),
          B = check(args[2], e, pi(A, () => atom(universe.j, universe.pretty))),
          F = pi(A, x => represented(apply(B, [x]))),
          f = check(args[3], e, F),
          g = check(args[4], e, F),
          H = pi(A, x => equalityType(F.body(x), apply(f, [x]), apply(g, [x]))),
          h = check(args[5], e, H),
          axiom = preludeAxiom("lib_funext"),
          result = b.app(axiom, op("UCumulOmega", [universe.j]), A.j, B.binding, f.binding, g.binding, h.binding);
        return val(result, equalityType(F, f, g), "function extensionality");
      },
      classical_truncation(args, e) {
        arity(args, 2, "classical_truncation");
        const A = asType(args[0], e),
          notA = pi(A, () => voidType),
          nn = check(args[1], e, pi(notA, () => voidType)),
          axiom = preludeAxiom("LEM"),
          result = b.app(axiom, op("UCumulOmega", [U]), A.j, nn.binding),
          T = b.app("lib_Trunc", op("UCumulOmega", [U]), A.j);
        return val(result, atom(T, `Mere(${A.pretty})`), "classical mere inhabitation");
      },
      set_choice(args, e) {
        arity(args, 5, "set_choice");
        const A = asType(args[0], e),
          B = check(args[1], e, pi(A, () => type)),
          isSet = T => pi(T, x => pi(T, y => {
            const paths = equalityType(T, x, y);
            return pi(paths, p => pi(paths, q => equalityType(paths, p, q)));
          })),
          setA = check(args[2], e, isSet(A)),
          setFibers = pi(A, x => isSet(represented(apply(B, [x])))),
          sets = check(args[3], e, setFibers),
          axiom = preludeAxiom("AOC"),
          mere = T => atom(b.app("lib_Trunc", op("UCumulOmega", [U]), T.j), `Mere(${T.pretty})`),
          inhabited = check(args[4], e, pi(A, x => mere(represented(apply(B, [x]))))),
          sections = pi(A, x => represented(apply(B, [x]))),
          conditions = op("SigmaIntro", [setA.binding, setFibers.j, sets.binding], [null]),
          result = b.app(axiom, op("UCumulOmega", [U]), A.j, B.binding, conditions, inhabited.binding);
        return val(result, mere(sections), "axiom of choice");
      },
      truncation(args, e) {
        arity(args, 1, "truncation");
        const A = asType(args[0], e);
        return withPrelude(() => {
          const j = b.app("lib_Trunc", op("UCumulOmega", [U]), A.j);
          return val(j, type, `Mere(${A.pretty})`, {representedType: atom(j, `Mere(${A.pretty})`)});
        });
      },
      truncation_intro(args, e) {
        arity(args, 2, "truncation_intro");
        const A = asType(args[0], e), a = check(args[1], e, A);
        return withPrelude(() => {
          const T = b.app("lib_Trunc", op("UCumulOmega", [U]), A.j);
          return val(b.app("lib_trunc_intro", op("UCumulOmega", [U]), A.j, a.binding), atom(T, `Mere(${A.pretty})`), "truncation introduction");
        });
      },
      truncation_prop(args, e) {
        arity(args, 1, "truncation_prop");
        const A = asType(args[0], e);
        return withPrelude(() => {
          const j = b.app("lib_Trunc", op("UCumulOmega", [U]), A.j), T = atom(j, `Mere(${A.pretty})`),
            P = pi(T, x => pi(T, y => equalityType(T, x, y)));
          return val(b.coerce(b.app("lib_trunc_is_trunc", op("UCumulOmega", [U]), A.j), P.j), P, "truncation is a proposition");
        });
      },
      truncation_elim(args, e) {
        arity(args, 4, "truncation_elim");
        const A = asType(args[0], e),
          P = asType(args[1], e),
          isProp = pi(P, x => pi(P, y => equalityType(P, x, y))),
          proposition = check(args[2], e, isProp),
          f = check(args[3], e, pi(A, () => P)),
          axiom = preludeAxiom("lib_trunc_elim"),
          // The prelude packages the map and proposition evidence as a pair.
          premise = op("SigmaIntro", [f.binding, isProp.j, proposition.binding], [null]),
          result = b.app(axiom, op("UCumulOmega", [U]), A.j, P.j, premise),
          mereA = atom(b.app("lib_Trunc", op("UCumulOmega", [U]), A.j), `Mere(${A.pretty})`);
        return val(result, pi(mereA, () => P), "truncation elimination");
      },
      unit_induction(args, e) {
        arity(args, 3, "unit_induction");
        const C = infer(args[0], e),
          A = atom(Unit, "Unit"),
          x = b.fresh(Unit),
          vx = val(x.v, A, "unit"),
          family = represented(apply(C, [vx])),
          star = val(op("UnitIntro"), A, "tt"),
          base = check(args[1], e, represented(apply(C, [star]))),
          u = check(args[2], e, A);
        return val(
          norm(
            op(
              "UnitElim",
              [
                family.j,
                b.coerce(base.binding, b.subst(family.j, x, star.binding)),
                u.binding,
              ],
              [x.c],
            ),
          ),
          represented(apply(C, [u])),
          "unit induction",
        );
      },
      Suspension(args, e) {
        arity(args, 1, "Suspension");
        const A = asType(args[0], e),
          j = op("SuspForm", [A.j]);
        return val(j, sortType(j), `Suspension(${A.pretty})`, {
          representedType: {
            kind: "suspension",
            parameter: A,
            j,
            pretty: `Suspension(${A.pretty})`,
          },
        });
      },
      north(args, e) {
        arity(args, 1, "north");
        const A = asType(args[0], e),
          j = op("SuspForm", [A.j]);
        return val(
          op("SuspNorth", [A.j]),
          {
            kind: "suspension",
            parameter: A,
            j,
            pretty: `Suspension(${A.pretty})`,
          },
          "north",
        );
      },
      south(args, e) {
        arity(args, 1, "south");
        const A = asType(args[0], e),
          j = op("SuspForm", [A.j]);
        return val(
          op("SuspSouth", [A.j]),
          {
            kind: "suspension",
            parameter: A,
            j,
            pretty: `Suspension(${A.pretty})`,
          },
          "south",
        );
      },
      meridian(args, e) {
        arity(args, 2, "meridian");
        const A = asType(args[0], e),
          a = check(args[1], e, A),
          S = op("SuspForm", [A.j]),
          n = op("SuspNorth", [A.j]),
          s = op("SuspSouth", [A.j]);
        return val(
          op("SuspMerid", [A.j, a.binding]),
          atom(b.eq(S, n, s), "north = south"),
          "meridian",
        );
      },
      transport(args, e) {
        arity(args, 5, "transport");
        const C = infer(args[0], e);
        if (C.type.kind !== "pi")
          throw new Error("transport needs a type family.");
        const A = C.type.domain,
          x = check(args[1], e, A),
          y = check(args[2], e, A),
          p = check(args[3], e, atom(b.eq(A.j, x.binding, y.binding), "path")),
          u = check(args[4], e, familyAt(C, x));
        return val(
          norm(
            op("Transport", [
              C.binding,
              x.binding,
              y.binding,
              p.binding,
              u.binding,
            ]),
          ),
          familyAt(C, y),
          "transport",
        );
      },
      apd(args, e) {
        arity(args, 4, "apd");
        const f = infer(args[0], e);
        if (f.type.kind !== "pi") throw new Error("apd needs a function.");
        const A = f.type.domain,
          x = check(args[1], e, A),
          y = check(args[2], e, A),
          p = check(args[3], e, atom(b.eq(A.j, x.binding, y.binding), "path")),
          result = op("Apd", [f.binding, x.binding, y.binding, p.binding]);
        // Reconstruct the checked family through its Pi descriptor.
        const a = b.fresh(A.j),
          B = f.type.body(val(a.v, A, "point")),
          Cj = op("PiIntro", [A.j, B.j], [a.c]),
          C = val(
            Cj,
            pi(A, () => sortType(B.j)),
            "family",
          ),
          fx = convert(apply(f, [x]), familyAt(C, x)),
          fy = apply(f, [y]),
          moved = norm(
            op("Transport", [Cj, x.binding, y.binding, p.binding, fx.binding]),
          );
        return val(
          norm(result),
          atom(
            b.eq(fy.type.j, b.coerce(moved, fy.type.j), fy.binding),
            "dependent application",
          ),
          "apd",
        );
      },
      suspension_induction(args, e) {
        arity(args, 5, "suspension_induction");
        const { C, S, cn, cs, h } = suspensionData(args, e),
          x = check(args[4], e, S);
        return val(
          norm(
            op("SuspElim", [
              C.binding,
              cn.binding,
              cs.binding,
              h.binding,
              x.binding,
            ]),
          ),
          familyAt(C, x),
          "suspension induction",
        );
      },
      suspension_meridian_beta(args, e) {
        arity(args, 5, "suspension_meridian_beta");
        const { C, S, A, cn, cs, h } = suspensionData(args, e),
          a = check(args[4], e, A),
          x = b.fresh(S.j),
          body = op("SuspElim", [
            C.binding,
            cn.binding,
            cs.binding,
            h.binding,
            x.v,
          ]),
          section = op("PiIntro", [S.j, body], [x.c]),
          n = op("SuspNorth", [A.j]),
          s = op("SuspSouth", [A.j]),
          p = op("SuspMerid", [A.j, a.binding]),
          lhs = norm(op("Apd", [section, n, s, p])),
          rhs = apply(h, [a]);
        return val(
          norm(
            op("SuspMeridComp", [
              C.binding,
              cn.binding,
              cs.binding,
              h.binding,
              a.binding,
            ]),
          ),
          atom(
            b.eq(rhs.type.j, b.coerce(lhs, rhs.type.j), rhs.binding),
            "suspension meridian computation",
          ),
          "suspension meridian computation",
        );
      },
      unfold(args, e) {
        arity(args, 1, "unfold");
        const value = infer(args[0], e),
          previous = b.opaque;
        b.opaque = false;
        try {
          return val(
            norm(value.binding),
            mapType(value.type, norm),
            value.display,
            mapMeta(value, norm),
          );
        } finally {
          b.opaque = previous;
        }
      },
      typed(args, e) {
        arity(args, 2, "typed");
        return check(args[1], e, asType(args[0], e));
      },
      Eq(args, e) {
        arity(args, 3, "Eq");
        const A = asType(args[0], e),
          x = check(args[1], e, A),
          y = check(args[2], e, A);
        const E = equalityType(A, x, y);
        return val(E.j, sortType(E.j), E.pretty, { representedType: E });
      },
      induct(args, e) {
        arity(args, 4, "induct");
        const n = check(args[0], e, nat),
          m = infer(args[1], e),
          z = b.fresh(N),
          k = b.fresh(N);
        const C = represented(apply(m, [val(z.v, nat, "index")]));
        const at = (v) => represented(apply(m, [v]));
        const zero = check(args[2], e, at(numeral(0))),
          kv = val(k.v, nat, "predecessor"),
          H = at(kv),
          h = b.fresh(b.subst(C.j, z, k.v));
        const step = infer(args[3], e),
          branch = apply(step, [kv, val(h.v, H, "hypothesis")]);
        const successor = op("NatIntroS", [k.v]);
        return val(
          norm(
            op(
              "NatElim",
              [
                C.j,
                b.coerce(zero.binding, b.subst(C.j, z, numeral(0).binding)),
                b.coerce(branch.binding, b.subst(C.j, z, successor)),
                n.binding,
              ],
              [z.c, k.c, h.c],
            ),
          ),
          at(n),
          "induction",
        );
      },
      cases(args, e) {
        arity(args, 4, "cases");
        const v = infer(args[0], e),
          T = v.type,
          C = asType(args[1], e);
        if (T.kind !== "sum") throw new Error("cases requires an or value.");
        const x = b.fresh(T.left.j),
          y = b.fresh(T.right.j),
          l = apply(infer(args[2], e), [val(x.v, T.left, "left_case")]),
          r = apply(infer(args[3], e), [val(y.v, T.right, "right_case")]);
        return val(
          norm(
            op(
              "SumElim",
              [
                C.j,
                b.coerce(l.binding, C.j),
                b.coerce(r.binding, C.j),
                v.binding,
              ],
              [null, x.c, y.c],
            ),
          ),
          C,
          "cases",
        );
      },
      unpack(args, e) {
        arity(args, 3, "unpack");
        const v = infer(args[0], e),
          T = v.type,
          C = asType(args[1], e);
        if (T.kind !== "sigma")
          throw new Error("unpack requires an exists/and value.");
        const x = b.fresh(T.domain.j),
          vx = val(x.v, T.domain, "witness"),
          B = T.body(vx),
          y = b.fresh(B.j),
          branch = apply(infer(args[2], e), [vx, val(y.v, B, "evidence")]);
        return val(
          norm(
            op(
              "SigmaElim",
              [C.j, b.coerce(branch.binding, C.j), v.binding],
              [null, x.c, y.c],
            ),
          ),
          C,
          "unpack",
        );
      },
      path_induction(args, e) {
        arity(args, 6, "path_induction");
        const A = asType(args[0], e),
          x = check(args[3], e, A),
          y = check(args[4], e, A),
          p = check(
            args[5],
            e,
            atom(b.eq(A.j, x.binding, y.binding), "equality"),
          );
        return pathInduction(A, infer(args[1], e), infer(args[2], e), x, y, p);
      },
    };
    function bindPattern(pattern, v, e, goal, rest) {
      current = pattern;
      if (pattern.kind === "name") {
        record(pattern, { ...v, display: pattern.name }, "local");
        return rest(extend(e, pattern.name, v, pattern));
      }
      const T = v.type;
      if (T.kind !== "sigma")
        throw new Error(
          "obtain needs an exists/and value with a known signature.",
        );
      const x = b.fresh(T.domain.j),
        vx = val(
          x.v,
          T.domain,
          pattern.left.kind === "name" ? pattern.left.name : "_",
        ),
        B = T.body(vx),
        y = b.fresh(B.j),
        vy = val(y.v, B, "_");
      const branch = bindPattern(pattern.left, vx, e, goal, (e) =>
        bindPattern(pattern.right, vy, e, goal, rest),
      );
      return val(
        norm(
          op(
            "SigmaElim",
            [goal.j, b.coerce(branch.binding, goal.j), v.binding],
            [null, x.c, y.c],
          ),
        ),
        goal,
        "obtained result",
      );
    }
    function block(statements, e, goal) {
      if (!statements.length)
        throw new Error("Unfinished proof: expected exact or cases.");
      const [s, ...rest] = statements;
      current = s;
      steps.push({
        start: s.start,
        end: s.end,
        goal: goal.pretty,
        locals: [...e]
          .filter(([name]) => !env.has(name))
          .map(([name, v]) => ({
            name,
            binding: v.binding,
            type: v.type.pretty,
          })),
      });
      // A named proposition retains its Pi descriptor. Introduction opens that
      // checked type, so the source can state a theorem using a definition name.
      if (s.kind === "intro") {
        if (goal.kind !== "pi")
          throw new Error("intro requires a forall or implication goal.");
        const x = b.fresh(goal.domain.j),
          vx = val(x.v, goal.domain, s.name.text),
          C = goal.body(vx);
        record(s.name, vx, "parameter");
        const body = convert(
          block(rest, extend(e, s.name.text, vx, s.name), C),
          C,
        );
        return convert(
          val(
            op("PiIntro", [goal.domain.j, body.binding], [x.c]),
            goal,
            "introduction",
          ),
          goal,
        );
      }
      if (s.kind === "let") {
        const v = infer(s.value, e);
        record(s.target, { ...v, display: s.target.name }, "local");
        return block(rest, extend(e, s.target.name, v, s.target), goal);
      }
      if (s.kind === "obtain")
        return bindPattern(s.target, infer(s.value, e), e, goal, (e) =>
          block(rest, e, goal),
        );
      if (s.kind === "have") {
        const T = asType(s.type, e),
          v = convert(block(s.body, e, T), T);
        record(s.name, { ...v, display: s.name.text }, "local");
        return block(rest, extend(e, s.name.text, v, s.name), goal);
      }
      if (rest.length)
        throw new Error(
          "No statements may follow exact or cases in the same block.",
        );
      if (s.kind === "exact") return check(s.value, e, goal);
      const v = infer(s.value, e),
        T = v.type;
      if (T.kind !== "sum") throw new Error("cases needs an or value.");
      const x = b.fresh(T.left.j),
        y = b.fresh(T.right.j),
        vx = val(x.v, T.left, s.left.text),
        vy = val(y.v, T.right, s.right.text);
      record(s.left, vx, "local");
      record(s.right, vy, "local");
      const left = convert(
          block(s.leftBody, extend(e, s.left.text, vx, s.left), goal),
          goal,
        ),
        right = convert(
          block(s.rightBody, extend(e, s.right.text, vy, s.right), goal),
          goal,
        );
      return val(
        norm(
          op(
            "SumElim",
            [goal.j, left.binding, right.binding, v.binding],
            [null, x.c, y.c],
          ),
        ),
        goal,
        "case analysis",
      );
    }
    let libraryCount = 0;
    const importedOutputs = [];
    const allDeclarations = [
      ...(importedProgram?.declarations ?? []),
      ...program.declarations,
    ];
    function mathscriptView(decl, T) {
      const text = sources[decl.library] ?? source;
      let expression = decl.name.text, expressionKind = "reference";
      if (decl.kind === "def") {
        if (decl.value) {
          expression = text.slice(decl.valueStart, decl.valueEnd);
          for (const parameter of [...decl.valueParameters].reverse())
            expression = `fun (${parameter.name.text} : ${text.slice(parameter.type.start, parameter.type.end)}) => ${expression}`;
          expressionKind = "expression";
        } else {
          expression = text.slice(decl.start, decl.end);
          expressionKind = "declaration";
        }
      }
      return { expression, expressionKind, type: T.pretty };
    }
    let completedDeclarations = 0;
    const reportProgress = () => onProgress?.({
      unit: "definitions",
      completed: completedDeclarations,
      total: allDeclarations.length,
      current: allDeclarations[completedDeclarations]?.name.text ?? "",
      instructions: b.k.steps.length,
    });
    b.progress = reportProgress;
    reportProgress();
    for (const decl of allDeclarations) {
      recording = !decl.library;
      if (!decl.library && !libraryCount) {
        if (visited.has("primes")) {
          for (const entry of declarations) {
            const value = env.get(entry.name);
            if (!value) continue;
            const signature = parse(entry.type, true);
            const mark = (node) => {
              if (!node || typeof node !== "object") return;
              node.library = true;
              for (const [key, child] of Object.entries(node))
                if (key !== "library") {
                  if (Array.isArray(child)) child.forEach(mark);
                  else if (child && typeof child === "object") mark(child);
                }
            };
            mark(signature);
            const T = asType(signature, env);
            if (!b.k.verify(T.j, value.binding))
              throw new Error(`Interface mismatch: ${entry.name}`);
            env.set(entry.name, { ...value, type: T });
            const output = importedOutputs.find((o) => o.name === entry.name);
            if (output) output.type = entry.type;
          }
        }
        libraryCount = b.k.steps.length;
      }
      current = decl;
      const start = b.k.steps.length;
      if (env.has(decl.name.text) || b.k.bindings.has(decl.name.text))
        throw new Error(`Name '${decl.name.text}' is already defined.`);
      function declaredType(params, e) {
        if (!params.length) return asType(decl.type, e);
        const [p, ...tail] = params,
          A = asType(p.type, e);
        return pi(
          A,
          (x) => declaredType(tail, new Map(e).set(p.name.text, x)),
          p.name.text,
        );
      }
      if (decl.value) {
        const value = infer(decl.value, env),
          T = value.type;
        let result = convert(value, T).binding;
        if (decl.kind === "theorem" || decl.opaque)
          result = op("DefEqExtL", [op("Def", [result])]);
        const binding = b.named(result, decl.name.text),
          proposition = b.named(T.j, decl.name.text + "_type");
        if (!b.k.verify(proposition, binding))
          throw new Error(`The kernel did not verify ${decl.name.text}.`);
        const named = { ...value, binding, display: decl.name.text };
        if (decl.opaque) b.boxedDefinitions.add(b.view(binding, 0));
        env.set(decl.name.text, named);
        record(decl.name, named, decl.kind);
        (decl.library ? importedOutputs : outputs).push({
          name: decl.name.text,
          binding,
          proposition,
          type: T.pretty,
          kind: decl.kind,
          role: decl.kind,
          start: decl.start,
          end: decl.end,
          definitionStart: decl.start,
          sourceModule: decl.library || undefined,
          mathscript: mathscriptView(decl, T),
          instructions: b.k.steps.length - start,
        });
        completedDeclarations++;
        reportProgress();
        continue;
      }
      const T = declaredType(decl.params, env);
      function prove(params, e) {
        if (!params.length) return block(decl.body, e, asType(decl.type, e));
        const [p, ...tail] = params,
          A = asType(p.type, e),
          x = b.fresh(A.j),
          vx = val(x.v, A, p.name.text);
        record(p.name, vx, "parameter");
        const body = prove(tail, extend(e, p.name.text, vx, p.name));
        return val(
          op("PiIntro", [A.j, body.binding], [x.c]),
          declaredType(params, e),
          decl.name.text,
        );
      }
      const v = decl.kind === "axiom"
          ? val(op("Axiom", [T.j], [], null, decl.name.text), T, decl.name.text)
          : convert(prove(decl.params, env), T),
        proof =
          (decl.kind === "theorem" || decl.opaque)
            ? op("DefEqExtL", [op("Def", [v.binding])])
            : v.binding,
        binding = decl.kind === "axiom" ? v.binding : b.named(proof, decl.name.text),
        proposition = b.named(T.j, decl.name.text + "_type");
      if (!b.k.verify(proposition, binding))
        throw new Error(`The kernel did not verify ${decl.name.text}.`);
      const named = val(binding, T, decl.name.text);
      if (decl.opaque) b.boxedDefinitions.add(b.view(binding, 0));
      env.set(decl.name.text, named);
      record(decl.name, named, decl.kind);
      (decl.library ? importedOutputs : outputs).push({
        name: decl.name.text,
        definitionStart: decl.start,
        sourceModule: decl.library || undefined,
        mathscript: mathscriptView(decl, T),
        binding,
        proposition,
        type: T.pretty,
        kind: decl.kind,
        start: decl.start,
        end: decl.end,
        instructions: b.k.steps.length - start,
      });
      completedDeclarations++;
      reportProgress();
    }
    if (!outputs.length) throw new Error("Write at least one def or theorem.");
    if (b.k.steps.length > MAX_STEPS)
      throw new Error(
        `Compiled mathematical proof exceeds ${MAX_STEPS} instructions.`,
      );
    const visible = new Set(
      [...outputs, ...importedOutputs].map((o) => o.binding),
    );
    for (const step of b.k.steps) {
      step.hidden = !visible.has(step.name);
      b.k.bindings.get(step.name).hidden = step.hidden;
    }
    for (const output of [...outputs, ...importedOutputs])
      output.axioms = b.k.axiomsFor(output.binding);
    return {
      kernel: b.k,
      allowAxioms: usesPrelude || usesDeclaredAxioms,
      axiomCount: b.k.steps.filter((s) => s.op === "Axiom").length,
      mode: "mathematical",
      optimizations,
      preludeAxioms: usesPrelude ? preludeLibrary.steps
        .filter(s => s.op === "Axiom" && b.k.bindings.has(s.name))
        .map(s => s.name) : [],
      source,
      links,
      steps,
      outputs,
      libraryCount,
      instructionCount: b.k.steps.length,
      imports: importedOutputs.map((o) => ({
        ...declarations.find((d) => d.name === o.name),
        ...o,
        sourceModule: o.sourceModule,
        sourceName: o.name,
      })),
      symbols: [...env]
        .map(([name, v]) => ({
          name,
          binding: v.binding,
          type: v.type.pretty,
          role: "builtin",
        }))
        .concat(
          numeralCache.map((v) => ({
            name: v.display,
            binding: v.binding,
            type: "Nat",
            role: "natural-number literal",
          })),
        ),
    };
  } catch (e) {
    b.k.dispose();
    const offset = e.offset ?? current?.start ?? 0;
    const line = source.slice(0, offset).split("\n").length,
      column = offset - (source.lastIndexOf("\n", offset - 1) + 1) + 1;
    const error = new Error(`Line ${line}, column ${column}: ${e.message}`);
    error.line = line;
    error.column = column;
    error.offset = offset;
    throw error;
  }
}
