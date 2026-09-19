// Each imported signature is reconstructed and verified against the saved
// axiom-free proof. These annotations cannot grant a theorem a new type.
export const declarations = [
  [
    "add",
    "nat_add",
    "forall a : Nat, forall b : Nat, Nat",
    "Addition",
    "0 + b = b; succ(a) + b = succ(a + b).",
  ],
  [
    "mul",
    "nat_mul",
    "forall a : Nat, forall b : Nat, Nat",
    "Multiplication",
    "0 * b = 0; succ(a) * b = b + a * b.",
  ],
  [
    "le",
    "nat_le",
    "forall a : Nat, forall b : Nat, U0",
    "Natural-number order",
    "0 <= b is Unit; succ(a) <= 0 is Void; succ(a) <= succ(b) is a <= b.",
  ],
  [
    "factorial",
    "nat_factorial",
    "forall n : Nat, Nat",
    "Factorial",
    "factorial(0) = 1; factorial(succ(n)) = succ(n) * factorial(n).",
  ],
  [
    "Divides",
    "Divides",
    "forall d : Nat, forall n : Nat, U0",
    "Divisibility",
    "Divides(d, n) means exists k : Nat, k * d = n.",
  ],
  [
    "Prime",
    "Prime",
    "forall p : Nat, U0",
    "Prime number",
    "Prime(p) means exists i : Nat, (p = 2 + i) and forall j : Nat, j < i -> Divides(2 + j, p) -> Void.",
  ],
  [
    "prime_divisor_exists",
    "prime_divisor_exists",
    "forall m : Nat, 2 <= m -> exists i : Nat, Prime(2 + i) and Divides(2 + i, m)",
    "Prime divisor",
    "A least divisor of m greater than one is prime. The returned i names p = 2+i.",
  ],
  [
    "factorial_positive",
    "factorial_positive",
    "forall n : Nat, 1 <= factorial(n)",
    "Positive factorial",
    "Every factorial is at least one.",
  ],
  [
    "nat_le_total",
    "nat_le_total",
    "forall a : Nat, forall b : Nat, (a <= b) or (b < a)",
    "Compare two naturals",
    "Either a <= b or b < a, with evidence for the selected case.",
  ],
  [
    "bounded_divisor_of_factorial",
    "bounded_divisor_of_factorial",
    "forall i : Nat, forall n : Nat, 2 + i <= n -> Divides(2 + i, factorial(n))",
    "Divisor of a factorial",
    "Every number from 2 through n divides factorial(n).",
  ],
  [
    "nontrivial_divisor_not_consecutive",
    "nontrivial_divisor_not_consecutive",
    "forall i : Nat, forall n : Nat, Divides(2 + i, n) -> Divides(2 + i, succ(n)) -> Void",
    "No consecutive multiples",
    "A number at least two cannot divide both n and n+1.",
  ],
].map(([name, binding, type, title, description]) => ({
  name,
  binding,
  type,
  title,
  description,
  role: ["add", "mul", "le", "factorial", "Divides", "Prime"].includes(name)
    ? "definition"
    : "lemma",
  sourceModule: "primes",
  sourceName: binding,
}));

export const exampleURL = new URL("../proofs/euclid.proof", import.meta.url);
