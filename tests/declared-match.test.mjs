// match on declared types, work-plan L2.2a: clauses elaborated against the
// clause types the kernel computes, dependent motives, path and squash
// clauses, structural recursion, the refusals, and the H1 release fixture:
// the circle's winding number, computed through univalence.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const module = await createCubical();
async function check(t, source) {
  const program = new CubicalProgram(module, sourceReader(), { experimental: ["h1"] });
  t.after(() => program.dispose());
  const result = await program.check(source, "main");
  return { result, get: name => {
    const found = result.outputs.find(output => output.name === name);
    assert.ok(found, `no declaration ${name}`);
    return found;
  } };
}
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};

const naturals = `inductive N { zero; succ(n : N); }
def add(n, m : N) : N := match n { zero => m; succ(k) => succ(add(k, m)); };
`;

test("structural recursion computes, with a parameter held fixed", async t => {
  const { get } = await check(t, `${naturals}
def double(n : N) : N := match n { zero => zero; succ(m) => succ(succ(double(m))); };
def four : double(succ(succ(zero))) = succ(succ(succ(succ(zero)))) { rfl; }
def three : add(succ(succ(zero)), succ(zero)) = succ(succ(succ(zero))) { rfl; }
def wrong : double(succ(zero)) = succ(zero) { rfl; }
`);
  for (const name of ["add", "double", "four", "three"]) ok(get(name));
  refused(get("wrong"), /./);
});

test("a dependent motive: each clause is checked at its own instance", async t => {
  const { get } = await check(t, `${naturals}
def zero_right(n : N) : add(n, zero) = n := match n as k return add(k, zero) = k {
  zero => refl(zero);
  succ(m) => cong(succ, zero_right(m));
};
`);
  ok(get("zero_right"));
});

test("data before positions: clauses name arguments in the order declared", async t => {
  const { get } = await check(t, `${naturals}
inductive Tree(U < UU0, A : U) { leaf; node(l : Tree(U, A), a : A, r : Tree(U, A)); }
def size(A : U0, t : Tree(U0, A)) : N := match t { leaf => zero; node(l, a, r) => succ(add(size(A, l), size(A, r))); };
def labels(t : Tree(U0, N)) : N := match t { leaf => zero; node(l, a, r) => add(a, add(labels(l), labels(r))); };
def small : Tree(U0, N) := node(node(leaf, succ(zero), leaf), zero, leaf);
def two : size(N, small) = succ(succ(zero)) { rfl; }
def one : labels(small) = succ(zero) { rfl; }
`);
  for (const name of ["size", "labels", "two", "one"]) ok(get(name));
});

test("a path constructor's clause is a path between the clauses at its ends", async t => {
  const { get } = await check(t, `${naturals}
inductive Circle { base; loop : base = base; }
def flat(x : Circle) : N := match x { base => zero; loop i => zero; };
def at_loop : flat(loop @ 1) = zero { rfl; }
def torn(x : Circle) : N := match x { base => zero; loop i => succ(zero); };
def unnamed(x : Circle) : N := match x { base => zero; loop => zero; };
def extra(x : Circle) : N := match x { base i => zero; loop i => zero; };
`);
  ok(get("flat"));
  ok(get("at_loop"));
  refused(get("torn"), /mismatch|clause/i);
  refused(get("unnamed"), /loop is a path constructor: name its 1 dimension after its arguments/);
  refused(get("extra"), /base has no dimensions to name/);
});

// E3: a truncation's eliminator, with its squash clause written T.squash.
// E8: a match on it without the squash clause is refused.
test("a truncation's squash clause, with T.squash and recursive results", async t => {
  const { get } = await check(t, `${naturals}
inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
def same(x, y : Trunc(U0, N)) : x = y := Trunc.squash(x, y);
def rebuilt(t : Trunc(U0, N)) : Trunc(U0, N) := match t {
  point(a) => point(a);
  squash(x, y) i => Trunc.squash(rebuilt(x), rebuilt(y)) @ i;
};
def rebuilt_point : rebuilt(point(zero)) = point(zero) { rfl; }
def unsquashed(t : Trunc(U0, N)) : Trunc(U0, N) := match t { point(a) => point(a); };
`);
  for (const name of ["same", "rebuilt", "rebuilt_point"]) ok(get(name));
  refused(get("unsquashed"), /Give the squash clause, .*generated squash clauses come with automatic clauses \(L2\.2b\)/);
});

// E8: a missing clause, a duplicate clause and an unknown constructor.
test("the refusals name the clause or the call", async t => {
  const { get } = await check(t, `${naturals}
def unknown(n : N) : N := match n { zero => zero; succ(m) => m; tail(x) => x; };
def twice(n : N) : N := match n { zero => zero; zero => zero; succ(m) => m; };
def partial(n : N) : N := match n { zero => zero; };
def arity(n : N) : N := match n { zero => zero; succ => zero; };
def growing(n : N) : N := match n { zero => zero; succ(m) => growing(succ(m)); };
def outside(n : N) : N := add(outside(n), match n { zero => zero; succ(m) => m; });
def untyped(n : N) := match n { zero => zero; succ(m) => m; };
def on_nat(n : Nat) : Nat := match n { zero => zero; succ(m) => m; };
`);
  refused(get("unknown"), /N has no constructor tail: its constructors are zero, succ/);
  refused(get("twice"), /zero has two clauses/);
  refused(get("partial"), /match on N needs a clause for succ/);
  refused(get("arity"), /succ takes 1 argument here/);
  refused(get("growing"), /not on an argument of the matched constructor: only structural recursion/);
  refused(get("outside"), /outside is being defined: it can call itself only on an argument of a constructor/);
  refused(get("untyped"), /match needs its result's type/);
  refused(get("on_nat"), /match requires a value of a declared type, or of a sum/);
});

// E1: the winding number, by S1's eliminator into U0 with ua of the
// successor equivalence. E2 in substance: code_on_loop, cong(code, loop)
// equal to ua(succ) by rfl.
test("the H1 release fixture: the circle's winding number computes through univalence", async t => {
  const source = await readFile(new URL("../docs/examples/h1/winding.cubist", import.meta.url), "utf8");
  const { result, get } = await check(t, source);
  for (const name of ["succ_equiv", "code", "winding", "winding_loop", "winding_twice", "winding_back", "code_on_loop"]) {
    ok(get(name));
    assert.deepEqual(get(name).extensions, ["H1"]);
    assert.deepEqual(get(name).axioms, [], `${name} uses no assumption: it computes`);
  }
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value),
    ["pos(succ(zero))", "pos(succ(succ(succ(zero))))", "pos(zero)"]);
  assert.ok(result.complete);
});

test("recursion recognizes the declaration's own parameter by its binder, not by its name", async t => {
  const { get } = await check(t, `${naturals}
def tricky(n : N) : N := (fun (n : N) => match n return N { zero => zero; succ(m) => tricky(m); })(zero);
def shadowed(n : N) : N := match n { zero => zero; succ(n) => shadowed(n); };
`);
  // The inner n is another variable: a call there is not recursion on it.
  refused(get("tricky"), /tricky is being defined: it can call itself only on an argument of a constructor/);
  // A clause may name its argument as the parameter was named.
  ok(get("shadowed"));
});

test("recursion only where the match is the whole body, and with the matched parameter rebound", async t => {
  const { get } = await check(t, `${naturals}
def wrapped(n : N) : N := succ(match n return N { zero => zero; succ(k) => wrapped(k); });
def captured(n : N) : N := match n { zero => n; succ(k) => captured(k); };
def constant_zero : captured(succ(succ(zero))) = zero { rfl; }
def not_identity : captured(succ(zero)) = succ(zero) { rfl; }
def via_block(n : N) : N { exact match n { zero => zero; succ(k) => via_block(k); }; }
def via_value(n : N) := match n return N { zero => zero; succ(k) => via_value(k); };
`);
  // Around the match, a call's recursive result would omit the succ.
  refused(get("wrapped"), /wrapped is being defined: it can call itself only on an argument of a constructor/);
  // n in the zero clause is zero there, on every recursive call: f is constant zero.
  for (const name of ["captured", "constant_zero", "via_block", "via_value"]) ok(get(name));
  refused(get("not_identity"), /./);
});

test("a clause's own names shadow the declaration's name and its matched parameter", async t => {
  const { get } = await check(t, `${naturals}
def f(n : N) : N := match n { zero => zero; succ(f) => f; };
def predecessor : f(succ(succ(zero))) = succ(zero) { rfl; }
def g(n : N) : N := match n { zero => zero; succ(n) => n; };
def also_predecessor : g(succ(succ(zero))) = succ(zero) { rfl; }
`);
  for (const name of ["f", "predecessor", "g", "also_predecessor"]) ok(get(name));
});

test("the formatter keeps a qualified name's dot tight", async () => {
  const { formatMathScript } = await import("../web/mathscript/formatter.mjs");
  const source = "def same(x, y : Trunc(U0, Nat)) : x = y := Trunc.squash(x, y);\n";
  const formatted = formatMathScript(source);
  assert.match(formatted, /Trunc\.squash\(x, y\)/);
  assert.equal(formatMathScript(formatted), formatted);
});

test("nested legacy matches are walked once: parsing and formatting stay linear", async () => {
  const { parse } = await import("../web/mathscript/parser.mjs");
  const { formatMathScript } = await import("../web/mathscript/formatter.mjs");
  let body = "0";
  for (let depth = 0; depth < 40; depth++) body = `match x return Nat { left a => ${body}; right b => 0; }`;
  const source = `def deep(x : Nat or Nat) : Nat := ${body};\n`;
  const started = performance.now();
  const match = parse(source).declarations[0].body[0].value;
  assert.ok(match.leftBody && match.clauses.length === 2, "the legacy fields and the clauses are both there");
  assert.ok(!Object.keys(match).includes("clauses"), "the legacy shape's clauses are not enumerated");
  formatMathScript(source);
  assert.ok(performance.now() - started < 5000, "a doubled walk would take 2^40 steps");
});

test("recursive calls are the calls written: their types, arities and arguments", async t => {
  const { get } = await check(t, `${naturals}
inductive Tag(n : N) : U0 { tag; }
def tagged(n : N) : Tag(n) := match n { zero => tag; succ(m) => tagged(m); };
def outer_motive(n : N) : Tag(n) := match n as z return Tag(n) { zero => tag; succ(m) => outer_motive(m); };
def refl_all(n : N) : n = n := match n { zero => refl(zero); succ(m) => refl(succ(m)); };
def applied(n : N) : N -> N := match n { zero => fun (x : N) => x; succ(m) => fun (x : N) => applied(m(x)); };
def dep(n : N, p : n = zero) : N := match n { zero => zero; succ(m) => dep(m, p); };
def f(f : N -> N, n : N) : N := match n { zero => f(zero); succ(m) => f(m); };
def shadowed_by_parameter : f(succ, succ(succ(zero))) = succ(succ(zero)) { rfl; }
`);
  // tagged(m) has type Tag(m), not Tag(n): the succ clause needs Tag(succ(m)).
  refused(get("tagged"), /mismatch/i);
  refused(get("outer_motive"), /The motive mentions n itself: write it over the matched value/);
  ok(get("refl_all"));
  refused(get("applied"), /m takes 0 arguments here, as an argument of the matched constructor/);
  // p is generalized: in the succ clause it proves succ(m) = zero, and the
  // call needs m = zero.
  refused(get("dep"), /Type mismatch: found succ\(m\) = zero, expected m = zero/);
  ok(get("f"));
  ok(get("shadowed_by_parameter"));
});

test("third review: a path of the matched type is recursed on at its dimensions", async t => {
  const { get } = await check(t, `${naturals}
inductive S : set { point; }
def ill_typed(s : S) : S := match s {
  point => point;
  squash(x, y, p, q) i j => S.squash(ill_typed(x), ill_typed(y), ill_typed(p), ill_typed(q)) @ i @ j;
};
def rebuilt(s : S) : S := match s {
  point => point;
  squash(x, y, p, q) i j => S.squash(rebuilt(x), rebuilt(y), path k => rebuilt(p @ k), path k => rebuilt(q @ k)) @ i @ j;
};
def rebuilt_point : rebuilt(point) = point { rfl; }
def too_many(s : S) : S := match s {
  point => point;
  squash(x, y, p, q) i j => S.squash(too_many(x @ i), too_many(y), path k => too_many(p @ k), path k => too_many(q @ k)) @ i @ j;
};
`);
  // p : x = y is not an S: too_many(p) would be ill-typed outside the definition.
  refused(get("ill_typed"), /p is a 1-dimensional path of the matched type, not an element: call ill_typed on it at its dimensions, as ill_typed\(p @ i\)/);
  ok(get("rebuilt"));
  ok(get("rebuilt_point"));
  refused(get("too_many"), /x is an element of the matched type, not a path/);
});

test("third review: a parameter that shadows its type's name still matches", async t => {
  const { get } = await check(t, `${naturals}
def count(N : N) : Nat := match N { zero => 0; succ(k) => count(k); };
def counted : count(succ(succ(zero))) = 0 { rfl; }
`);
  ok(get("count"));
  ok(get("counted"));
});

test("fourth review: a user constructor named squash and the generated T.squash are distinct clauses", async t => {
  const { get } = await check(t, `${naturals}
inductive S : prop { squash; }
def keep(s : S) : S := match s { squash => squash; S.squash(x, y) i => S.squash(keep(x), keep(y)) @ i; };
def kept : keep(squash) = squash { rfl; }
def ambiguous(s : S) : S := match s { squash => squash; squash(x, y) i => S.squash(x, y) @ i; };
inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
def qualified(t : Trunc(U0, N)) : Trunc(U0, N) := match t {
  point(a) => point(a);
  Trunc.squash(x, y) i => Trunc.squash(qualified(x), qualified(y)) @ i;
};
`);
  for (const name of ["keep", "kept", "qualified"]) ok(get(name));
  // squash here is the user's constructor: two clauses for it.
  refused(get("ambiguous"), /squash has two clauses/);
  const { formatMathScript } = await import("../web/mathscript/formatter.mjs");
  const source = "def f(t : T) : T := match t { T.squash(x, y) i => x; };\n";
  assert.match(formatMathScript(source), /T\.squash\(x, y\) i => x;/);
});

test("fifth review: a position's arguments may be curried in a recursive call", async t => {
  const { get } = await check(t, `inductive W { leaf; node(p : Nat -> Nat -> W); }
def size(w : W) : Nat := match w { leaf => 0; node(p) => succ(size(p(0)(0))); };
def size_flat(w : W) : Nat := match w { leaf => 0; node(p) => succ(size(p(0, 0))); };
def one : size(node(fun (a : Nat) => fun (b : Nat) => leaf)) = 1 { rfl; }
def partial(w : W) : Nat := match w { leaf => 0; node(p) => succ(partial(p(0))); };
`);
  for (const name of ["size", "size_flat", "one"]) ok(get(name));
  refused(get("partial"), /p takes 2 arguments here, as an argument of the matched constructor/);
});

// The closing proof statement (L2.2a through the HoTT roadmap's A5): its
// motive is the goal over the matched value, and each clause is a proof
// block of the goal at its constructor.
test("the match statement proves the goal at each constructor, recursing by name", async t => {
  const { get } = await check(t, `${naturals}
def add_zero(n : N) : add(n, zero) = n {
  match n {
    zero => { rfl; }
    succ(m) => { exact cong(succ, add_zero(m)); }
  }
}
def IsZero(n : N) : U0 := match n { zero => Unit; succ(m) => Void; };
def zero_of(n : N, h : IsZero(n)) : n = zero {
  match n {
    zero => { rfl; }
    succ(m) => { exact absurd(h); }
  }
}
def zero_named(n : N, h : IsZero(n)) : n = zero {
  match n {
    zero => { exact refl(n); }
    succ(m) => { exact absurd(h); }
  }
}
def zero_named_after_intro : forall n : N. IsZero(n) -> n = zero {
  intro n, h;
  match n {
    zero => { exact refl(n); }
    succ(m) => { exact absurd(h); }
  }
}
def local_fact(n : N, h : IsZero(n)) : n = zero {
  have k : IsZero(n) { exact h; }
  match n {
    zero => { rfl; }
    succ(m) => { exact absurd(k); }
  }
}
def local_value(n : N) : add(n, zero) = n {
  let copy := n;
  let twice := add(n, n);
  match n {
    zero => { exact refl(add(copy, twice)); }
    succ(m) => { exact cong(succ, add_zero(m)); }
  }
}
def nested_copy(n : N) : add(n, zero) = n {
  let copy := n;
  match n {
    zero => { rfl; }
    succ(m) => {
      match m {
        zero => { exact refl(copy); }
        succ(k) => { exact cong(succ, add_zero(succ(k))); }
      }
    }
  }
}
def simp_at_generalized(n : N, h : n = n) : n = n {
  match n {
    zero => {
      simp only [] at h as k;
      exact k;
    }
    succ(m) => { exact h; }
  }
}
def constructor_scrutinee(n : N) : succ(n) = succ(n) {
  match succ(n) {
    zero => { exact refl(zero); }
    succ(k) => { exact refl(succ(k)); }
  }
}
def same(n : N) : N {
  match n {
    zero => { exact n; }
    succ(m) => { exact n; }
  }
}
def same_two : same(succ(succ(zero))) = succ(succ(zero)) { rfl; }
def after_intro : forall n : N. add(n, zero) = n {
  intro n;
  match n {
    zero => { rfl; }
    succ(m) => { exact cong(succ, add_zero(m)); }
  }
}
`);
  for (const name of ["add_zero", "IsZero", "zero_of", "zero_named", "zero_named_after_intro", "local_fact", "local_value", "nested_copy",
    "simp_at_generalized", "constructor_scrutinee", "same", "same_two", "after_intro"]) ok(get(name));
});

test("a match statement's generalized hypothesis takes its own value at a recursive call", async t => {
  const { get } = await check(t, `${naturals}
def Rep(n : N) : U0 := match n { zero => Unit; succ(m) => N and Rep(m); };
def total(n : N, r : Rep(n)) : N {
  match n {
    zero => { exact zero; }
    succ(m) => { exact add(r.1, total(m, r.2)); }
  }
}
def seven : total(succ(succ(zero)), (succ(zero), (succ(succ(zero)), tt))) = succ(succ(succ(zero))) { rfl; }
def unchanged(n : N, r : Rep(n)) : N {
  match n {
    zero => { exact zero; }
    succ(m) => { exact unchanged(m, r); }
  }
}
`);
  for (const name of ["Rep", "total", "seven"]) ok(get(name));
  refused(get("unchanged"), /mismatch/i);
});

// A match inside a recursive clause: the recursive call still names the
// variable the inner match takes apart, at its constructor there.
test("a nested match statement keeps the enclosing recursion", async t => {
  const { get } = await check(t, `${naturals}
def nested(n : N) : add(n, zero) = n {
  match n {
    zero => { rfl; }
    succ(m) => {
      match m {
        zero => { rfl; }
        succ(k) => { exact cong(succ, nested(m)); }
      }
    }
  }
}
def deep(n : N) : add(n, zero) = n {
  match n {
    zero => { rfl; }
    succ(m) => {
      match m {
        zero => { rfl; }
        succ(k) => {
          match k {
            zero => { rfl; }
            succ(j) => { exact cong(succ, deep(m)); }
          }
        }
      }
    }
  }
}
def keep(n, a : N) : N {
  match n {
    zero => { exact a; }
    succ(m) => {
      match a {
        zero => { exact keep(m, a); }
        succ(b) => { exact succ(keep(m, a)); }
      }
    }
  }
}
def keep_two : keep(succ(zero), succ(zero)) = succ(succ(zero)) { rfl; }
inductive Tag(k : N) : U0 { tag; }
inductive W { leaf; node(k : N, p : Tag(k) -> W); }
def count(w : W) : N {
  match w {
    leaf => { exact zero; }
    node(k, p) => {
      match k {
        zero => { exact succ(count(p(tag))); }
        succ(j) => { exact count(p(tag)); }
      }
    }
  }
}
def not_smaller(n : N) : N {
  match n {
    zero => { exact zero; }
    succ(m) => {
      match m {
        zero => { exact zero; }
        succ(k) => { exact not_smaller(n); }
      }
    }
  }
}
`);
  // A position the inner match generalizes, as p : Tag(k) -> W is, is
  // recursed on under its new variable.
  for (const name of ["nested", "deep", "keep", "keep_two", "Tag", "W", "count"]) ok(get(name));
  refused(get("not_smaller"), /not on an argument of the matched constructor/);
});

test("a match statement recurses on several arguments of a constructor, with a parameter fixed", async t => {
  const { get } = await check(t, `${naturals}
inductive Tree(U < UU0, A : U) { leaf; node(l : Tree(U, A), a : A, r : Tree(U, A)); }
def mirror(A : U0, t : Tree(U0, A)) : Tree(U0, A) {
  match t {
    leaf => { exact leaf; }
    node(l, a, r) => { exact node(mirror(A, r), a, mirror(A, l)); }
  }
}
def mirror_mirror(A : U0, t : Tree(U0, A)) : mirror(A, mirror(A, t)) = t {
  match t {
    leaf => { rfl; }
    node(l, a, r) => { exact path i => node(mirror_mirror(A, l) @ i, a, mirror_mirror(A, r) @ i); }
  }
}
`);
  for (const name of ["mirror", "mirror_mirror"]) ok(get(name));
});

// A truncation's squash clause, written in the statement: a path between the
// recursive results at its ends.
test("a match statement's squash clause", async t => {
  const { get } = await check(t, `${naturals}
inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
def rebuilt(t : Trunc(U0, N)) : Trunc(U0, N) {
  match t {
    point(a) => { exact point(a); }
    squash(x, y) i => { exact Trunc.squash(rebuilt(x), rebuilt(y)) @ i; }
  }
}
def rebuilt_point : rebuilt(point(zero)) = point(zero) { rfl; }
def generic(U < UU0, A : U, t : Trunc(U, A)) : Trunc(U, A) {
  match t {
    point(a) => { exact point(a); }
    squash(x, y) i => { exact Trunc.squash(generic(U, A, x), generic(U, A, y)) @ i; }
  }
}
def generic_point(U < UU0, A : U, a : A) : generic(U, A, point(a)) = point(a) { rfl; }
`);
  // A universe parameter passes unchanged as a type parameter does.
  for (const name of ["rebuilt", "rebuilt_point", "generic", "generic_point"]) ok(get(name));
});

test("a match statement's path clause is a path between the clauses at its ends", async t => {
  const { get } = await check(t, `${naturals}
inductive Circle { base; loop : base = base; }
def flat(x : Circle) : N := match x { base => zero; loop i => zero; };
def flat_constant(x : Circle) : flat(x) = zero {
  match x {
    base => { rfl; }
    loop i => { rfl; }
  }
}
`);
  for (const name of ["flat", "flat_constant"]) ok(get(name));
});

test("the match statement's refusals", async t => {
  const { get } = await check(t, `${naturals}
def unreachable(n : N) : N {
  match n {
    zero => { exact zero; }
    succ(m) => { exact m; }
  }
  exact n;
}
def missing(n : N) : N {
  match n {
    zero => { exact zero; }
  }
}
def of_a_sum(p : N or N) : N {
  match p {
    left x => { exact x; }
    right y => { exact y; }
  }
}
def wrong_clause(n : N) : add(n, zero) = n {
  match n {
    zero => { rfl; }
    succ(m) => { rfl; }
  }
}
`);
  refused(get("unreachable"), /^Statements after match are unreachable: each clause's block closes the goal\./);
  refused(get("missing"), /match on N needs a clause for succ\./);
  refused(get("of_a_sum"), /^The match statement takes apart a value of a declared type; for a sum, use cases\./);
  refused(get("wrong_clause"), /./);
});

// L2.2a's third slice: a recursive call passes values of its own for the
// declaration's other parameters. The motive quantifies over each of them but
// those the matched parameter's type depends on, and each clause binds them
// again under their own names.
test("recursion whose other arguments vary: the accumulator, computed and proved", async t => {
  const { result, get } = await check(t, `${naturals}
def acc(n, a : N) : N := match n { zero => a; succ(m) => acc(m, succ(a)); };
def acc_first(a, n : N) : N := match n { zero => a; succ(m) => acc_first(succ(a), m); };
def two_three : acc(succ(succ(zero)), succ(zero)) = succ(succ(succ(zero))) { rfl; }
def add_succ(n, a : N) : add(n, succ(a)) = succ(add(n, a)) {
  match n {
    zero => { rfl; }
    succ(m) => { exact cong(succ, add_succ(m, a)); }
  }
}
def acc_add(n, a : N) : acc(n, a) = add(n, a) {
  match n {
    zero => { rfl; }
    succ(m) => { exact trans(acc_add(m, succ(a)), add_succ(m, a)); }
  }
}
evaluate acc(succ(succ(zero)), zero) expecting succ(succ(zero));
evaluate acc_first(zero, succ(succ(succ(zero)))) expecting succ(succ(succ(zero)));
`);
  for (const name of ["acc", "acc_first", "two_three", "add_succ", "acc_add"]) ok(get(name));
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["succ(succ(zero))", "succ(succ(succ(zero)))"]);
});

// A parameter whose type mentions a generalized one is generalized too; a
// clause's own name shadows a parameter's; a nested match takes apart a
// generalized parameter, and a call passes its constructor.
test("recursion whose other arguments vary: dependent, shadowed and nested parameters", async t => {
  const { get } = await check(t, `${naturals}
def Rep(n : N) : U0 := match n { zero => Unit; succ(m) => N and Rep(m); };
def dep_ok(n : N, p : n = n) : N := match n { zero => zero; succ(m) => dep_ok(m, refl(m)); };
def bounded(n, a : N, h : a = a) : N {
  match n {
    zero => { exact a; }
    succ(m) => { exact bounded(m, succ(a), refl(succ(a))); }
  }
}
def sh(n, a : N) : N := match n { zero => a; succ(a) => sh(a, a); };
def sh_value : sh(succ(succ(zero)), succ(zero)) = zero { rfl; }
def inner(n, k : N, r : Rep(k)) : N {
  match n {
    zero => { exact zero; }
    succ(m) => {
      match k {
        zero => { exact inner(m, zero, tt); }
        succ(j) => { exact add(r.1, inner(m, k, r)); }
      }
    }
  }
}
def inner_value : inner(succ(zero), succ(zero), (succ(zero), tt)) = succ(zero) { rfl; }
`);
  for (const name of ["Rep", "dep_ok", "bounded", "sh", "sh_value", "inner", "inner_value"]) ok(get(name));
});

test("recursion whose other arguments vary: what stays fixed, and path and squash clauses", async t => {
  const { get } = await check(t, `${naturals}
inductive Tree(U < UU0, A : U) { leaf; node(l : Tree(U, A), a : A, r : Tree(U, A)); }
def relabel(A : U0, t : Tree(U0, A)) : N := match t { leaf => zero; node(l, a, r) => relabel(N, l); };
def lift(U < UU0, n : N) : N := match n { zero => zero; succ(m) => lift(U0, m); };
def pick(n, a : N) : N := match n { zero => a; succ(m) => m; };
def pick_unfolds(n, a : N) : pick(n, a) = (match n return N { zero => a; succ(m) => m; }) { rfl; }
def own(n, a : N) : N := match n { zero => a; succ(own) => own; };
def own_unfolds(n, a : N) : own(n, a) = (match n return N { zero => a; succ(k) => k; }) { rfl; }
inductive Circle { base; loop : base = base; }
def around(x : Circle, a : N) : N := match x { base => a; loop i => a; };
def around_loop(a : N) : around(loop @ 1, succ(a)) = succ(a) { rfl; }
def torn(x : Circle, a : N) : N := match x { base => a; loop i => succ(a); };
inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
inductive Steps : prop { stop; next(s : Steps); }
def count(s : Steps, b : N) : Trunc(U0, N) := match s {
  stop => point(b);
  next(r) => count(r, succ(b));
  squash(x, y) i => Trunc.squash(count(x, b), count(y, b)) @ i;
};
def count_two : count(next(next(stop)), zero) = point(succ(succ(zero))) { rfl; }
def skewed(s : Steps, b : N) : Trunc(U0, N) := match s {
  stop => point(b);
  next(r) => skewed(r, succ(b));
  squash(x, y) i => Trunc.squash(skewed(x, succ(b)), skewed(y, b)) @ i;
};
`);
  // A match that never calls its declaration keeps its motive, whatever its
  // binders are named: the declaration is the match as written.
  for (const name of ["pick", "pick_unfolds", "own", "own_unfolds"]) ok(get(name));
  refused(get("relabel"), /^A recursive call of relabel passes A unchanged: the type of the matched t depends on it\./);
  refused(get("lift"), /^A recursive call of lift passes the universe parameter U unchanged\./);
  // A clause over a generalized parameter is a path of functions, and the
  // kernel still checks it against the clauses at its ends.
  for (const name of ["around", "around_loop", "Steps", "count", "count_two"]) ok(get(name));
  refused(get("torn"), /mismatch|clause/i);
  refused(get("skewed"), /mismatch|clause/i);
});

// An operator that stands for the declaration calls it as its name does.
test("recursion whose other arguments vary: a call spelled with an operator", async t => {
  const { get } = await check(t, `inductive N { zero; succ(n : N); }
def add(n, a : N) : N := match n { zero => a; succ(m) => m + succ(a); };
def five : add(succ(succ(zero)), succ(succ(succ(zero)))) = succ(succ(succ(succ(succ(zero))))) { rfl; }
`);
  for (const name of ["add", "five"]) ok(get(name));
});

// A clause's goal shows a generalized parameter under its own name, without
// the parameter it supersedes; its recursive result quantifies over it. A
// recursion that passes its parameters unchanged keeps them fixed, and the
// first attempt of one that changes them leaves no second set of steps.
test("a clause's goal shows a generalized parameter under its source name", async t => {
  const program = new CubicalProgram(module, sourceReader(), { experimental: ["h1"] });
  t.after(() => program.dispose());
  await program.check(`${naturals}
def acc(n, a : N) : N := match n { zero => a; succ(m) => acc(m, succ(a)); };
def add_succ(n, a : N) : add(n, succ(a)) = succ(add(n, a)) {
  match n {
    zero => { rfl; }
    succ(m) => { exact cong(succ, add_succ(m, a)); }
  }
}
def acc_add(n, a : N) : acc(n, a) = add(n, a) {
  match n {
    zero => { rfl; }
    succ(m) => { exact trans(acc_add(m, succ(a)), add_succ(m, a)); }
  }
}
def same(n, a1 : N) : acc(n, a1) = acc(n, a1) {
  match n {
    zero => { rfl; }
    succ(m) => { exact same(m, succ(a1)); }
  }
}
`, "main");
  const shown = name => program.steps("main").filter(step => step.declaration === name)
    .map(step => [step.kind, step.locals.map(local => `${local.name} : ${local.type}`), step.goal]);
  assert.deepEqual(shown("acc_add"), [
    ["matchStatement", ["n : N", "a : N"], "acc(n, a) = add(n, a)"],
    ["rfl", ["n : N", "a : N"], "acc(zero, a) = add(zero, a)"],
    ["exact", ["n : N", "m : N", "m_rec : forall a : N. acc(m, a) = add(m, a)", "a : N"], "acc(succ(m), a) = add(succ(m), a)"],
  ]);
  assert.deepEqual(shown("add_succ").at(-1), ["exact", ["n : N", "a : N", "m : N", "m_rec : add(m, succ(a)) = succ(add(m, a))"],
    "add(succ(m), succ(a)) = succ(add(succ(m), a))"]);
  // Nor a second set of inspector records: the clause binds m once.
  assert.equal(program.declarationBindings.get("main__acc_add").filter(item => item.node.name === "m").length, 1);
  // A parameter whose name ends in a digit is shown once too.
  const clause = program.steps("main").find(step => step.declaration === "same" && step.kind === "exact");
  assert.deepEqual(clause.locals.filter(local => local.name.startsWith("a1")).map(local => local.type), ["N"]);
});

// The refactor shared with the statement keeps the expression's order: the
// declared type, then the motive, then the clauses.
test("the expression reports a missing motive before a missing clause", async t => {
  const { get } = await check(t, `${naturals}
def unknown := match succ(zero) { zero => zero; };
`);
  refused(get("unknown"), /^match needs its result's type: give return T, or use it where its type is known\./);
});

test("without the experimental option, the match statement says what it needs", async t => {
  const program = new CubicalProgram(module, sourceReader());
  t.after(() => program.dispose());
  const result = await program.check("def f(n : Nat) : Nat {\n  match n {\n    zero => { exact n; }\n  }\n}\n", "main");
  refused(result.outputs.find(output => output.name === "f"),
    /^The match statement takes apart a value of a declared type, a kernel extension under review: enable the experimental option h1/);
});

test("the match statement parses and formats, one statement to a line", async () => {
  const { parse } = await import("../web/mathscript/parser.mjs");
  const { formatMathScript } = await import("../web/mathscript/formatter.mjs");
  const source = "def add_zero(n : N) : add(n, zero) = n {\n  match n {\n    zero => {\n      rfl;\n    }\n    succ(m) => {\n      exact cong(succ, add_zero(m));\n    }\n  }\n}\n";
  const statement = parse(source).declarations[0].body[0];
  assert.equal(statement.kind, "matchStatement");
  assert.deepEqual(statement.clauses.map(clause => clause.constructor.text), ["zero", "succ"]);
  assert.equal(formatMathScript(source), source);
  assert.throws(() => parse("def f(n : N) : N {\n  match n as k return N { zero => { exact n; } }\n}\n"),
    /The match statement takes its motive from the goal/);
  assert.throws(() => parse("def f(n : N) : N {\n  match n { zero => n; }\n}\n"),
    /A clause of the match statement is a proof block/);
  assert.throws(() => parse("def f(n, m : N) : N {\n  match n, m { zero => { exact m; } }\n}\n"),
    /The match statement takes apart one value/);
});
