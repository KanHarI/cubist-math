// The sources the probe (probe.mjs) and the acceptance report (report.mjs)
// define their cases in.
export const sources = {
  // The rational normalization debugging plan's main-only reproduction of the
  // small inverse, without #283; that plan's probe adds its further queries.
  rational: `import fractions;
import binary_integers;
use bnat;

def binary_rationals : Field(U0) := fraction_field(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one);

def BQ : U0 := binary_rationals.R;

computable def two_thirds : BQ := match bint_decide_zero(bint_of_nat(3)) return BQ {
    left same => binary_rationals.zero;
    right nonzero => class((bint_of_nat(2), bint_of_nat(3), nonzero));
  };

computable def minus_two_thirds : BQ := binary_rationals.neg(two_thirds);

computable def small_inverse : BQ := q_inv{{U0}}(
  binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one, two_thirds
);

computable def small_inverse_neg : BQ := q_inv{{U0}}(
  binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one, minus_two_thirds
);
`,
  // The evaluation baseline's Euclid workloads, and lambdas the weak head
  // contracts by eta or keeps.
  euclid: `import euclid;
use unat;

def euclid_3 := euclid(3);

def euclid_4 := euclid(4);

def euclid_4_prime := euclid(4).1;

def eta_successor := fun (n : UNat) => succ(n);

def identity := fun (n : UNat) => n;
`,
};
