/-
  Aristotle targets for CombinationsFormulaOQ02 (Catalan Numbers)
  Routine supporting lemmas for automated proof search.
  See CombinationsFormulaOQ02.lean for the main formalization.

  Targets (in order of difficulty):
  1. catalan_pos: C_n > 0 for n ≤ 4 (by norm_num via definitions)
  2. centralBinom_ge_two_pow: C(2n, n) ≥ 2^n for n ≥ 1 (induction)
     - Inductive step: C(2m+2, m+1) ≥ 2 * C(2m, m) via Pascal identity
  3. catalan_mul_succ: C_n * (n+1) = C(2n, n) (fundamental identity)
  4. choose_2n_succ_divides: (n+1) | C(2n, n) * n (divisibility)

  Not targeted (too hard / require WZ-theory or Vandermonde):
  - catalan_convolution: requires Vandermonde identity
  - catalan_mono: requires catalan_mul_succ first
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Nat Finset BigOperators

namespace CatalanNumbers

def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

abbrev centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- C_n > 0 for all n (verified for n ≤ 5 by computation, general case via catalan_mul_succ). -/
theorem catalan_pos_small (n : ℕ) (hn : n ≤ 5) : 0 < catalan n := by
  interval_cases n <;> decide

/-- C(2n, n) ≥ 2^n for n ≥ 1.
    Inductive step: C(2m+2, m+1) = C(2m, m) * 2*(2m+1)/(m+1) ≥ 2 * C(2m, m). -/
theorem centralBinom_ge_two_pow (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ centralBinom n := by
  sorry

/-- The divisibility fact: (n+1) divides C(2n, n).
    Equivalently C(2n, n) = catalan(n) * (n+1). -/
theorem succ_dvd_centralBinom (n : ℕ) : (n + 1) ∣ centralBinom n := by
  sorry

/-- **Fundamental Catalan identity**: C_n * (n+1) = C(2n, n).
    Follows from the ballot-problem formula: C_n = C(2n,n)/(n+1). -/
theorem catalan_mul_succ (n : ℕ) :
    catalan n * (n + 1) = centralBinom n := by
  sorry

/-- C(2n, n+1) * (n+1) = C(2n, n) * n (divisibility relationship). -/
theorem choose_2n_succ (n : ℕ) :
    Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
  sorry

end CatalanNumbers
