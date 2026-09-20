// Documentation lives in comments above the mathematical source declarations.
// Each imported signature is reconstructed and verified against the saved
// axiom-free proof. These annotations cannot grant a theorem a new type.
export const declarations = [
  [
    "add",
    "nat_add",
    "forall a : Nat, forall b : Nat, Nat",
  ],
  [
    "mul",
    "nat_mul",
    "forall a : Nat, forall b : Nat, Nat",
  ],
  [
    "le",
    "nat_le",
    "forall a : Nat, forall b : Nat, U0",
  ],
  [
    "factorial",
    "nat_factorial",
    "forall n : Nat, Nat",
  ],
  [
    "Divides",
    "Divides",
    "forall d : Nat, forall n : Nat, U0",
  ],
  [
    "Prime",
    "Prime",
    "forall p : Nat, U0",
  ],
  [
    "prime_divisor_exists",
    "prime_divisor_exists",
    "forall m : Nat, 2 <= m -> exists i : Nat, Prime(2 + i) and Divides(2 + i, m)",
  ],
  [
    "factorial_positive",
    "factorial_positive",
    "forall n : Nat, 1 <= factorial(n)",
  ],
  [
    "nat_le_total",
    "nat_le_total",
    "forall a : Nat, forall b : Nat, (a <= b) or (b < a)",
  ],
  [
    "bounded_divisor_of_factorial",
    "bounded_divisor_of_factorial",
    "forall i : Nat, forall n : Nat, 2 + i <= n -> Divides(2 + i, factorial(n))",
  ],
  [
    "nontrivial_divisor_not_consecutive",
    "nontrivial_divisor_not_consecutive",
    "forall i : Nat, forall n : Nat, Divides(2 + i, n) -> Divides(2 + i, succ(n)) -> Void",
  ],
].map(([name, binding, type]) => ({
  name,
  binding,
  type,
  role: ["add", "mul", "le", "factorial", "Divides", "Prime"].includes(name)
    ? "definition"
    : "lemma",
  sourceModule: "primes",
  sourceName: binding,
}));

export const exampleURL = new URL("../proofs/euclid.proof", import.meta.url);
