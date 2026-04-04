/-
  Aristotle targets for Erdős Problem #678 (LCM of Consecutive Integer Intervals)
  Routine supporting lemmas for automated proof search.
  See Erdos678Problem.lean for the main formalization.

  Status: SOLVED (Cambie 2024)

  Criteria for inclusion:
  - Routine LCM properties: divisibility, monotonicity, definitional equalities
  - NOT the main existence results (erdos_678_infinitely_many, cambie_2024)
  - NOT the deep growth bounds (intervalLcm_growth, erdos_growth_rate)
  - NOT the interval_skip_prime_power (complex logical statement)
  - NOT anything involving minimalN (def sorry in main file)

  Targets:
  1. intervalLcm_eq_intervalLcm': two definitions of interval LCM agree
  2. intervalLcm_mono_right: divisibility when extending interval
  3. dvd_intervalLcm: each element in [n+1, n+k] divides intervalLcm n k
  4. prime_power_divides_intervalLcm: prime power in interval → divides LCM
  5. intervalLcm_chebyshev_upper: intervalLcm n k ≤ 4^k (Chebyshev bound)
-/
import Mathlib
import Proofs.Erdos678Problem

open Finset Nat

namespace Erdos678Aristotle

open Erdos678

/-
## Definitional Equality

The two definitions of intervalLcm agree.
intervalLcm n k = (range k).fold lcm 1 (fun i => n+1+i)
intervalLcm' n k = (Icc (n+1) (n+k)).fold lcm 1 id
-/

/-- The range-based and Icc-based definitions of interval LCM agree.
    Strategy: show Finset.range k and Finset.Icc (n+1) (n+k) are in bijection
    via i ↦ n+1+i, and the lcm fold is preserved under this bijection. -/
theorem intervalLcm_eq_intervalLcm' (n k : ℕ) (hk : k ≥ 1) :
    intervalLcm n k = intervalLcm' n k := by
  sorry

/-
## Monotonicity and Divisibility
-/

/-- Each element n+1+i (for i < k) divides intervalLcm n k.
    Strategy: i ∈ Finset.range k, so n+1+i is one of the factors;
    each factor divides the lcm fold (by Finset.dvd_fold_lcm or similar). -/
theorem dvd_intervalLcm (n k i : ℕ) (hi : i < k) :
    (n + 1 + i) ∣ intervalLcm n k := by
  sorry

/-- intervalLcm n k divides intervalLcm n (k+1).
    Strategy: the range k fold divides the range (k+1) fold since
    the former is a sub-fold of the latter and lcm is monotone. -/
theorem intervalLcm_mono_right (n k : ℕ) :
    intervalLcm n k ∣ intervalLcm n (k + 1) := by
  sorry

/-
## Prime Power Divisibility
-/

/-- If p^a ∈ [n+1, n+k], then p^a | intervalLcm n k.
    Strategy: p^a is one of the elements in the interval, so by dvd_intervalLcm
    (applied to the appropriate index), p^a divides the LCM. -/
theorem prime_power_divides_intervalLcm (n k p a : ℕ) (hp : p.Prime)
    (hpa : p ^ a ∈ Finset.Icc (n + 1) (n + k)) :
    p ^ a ∣ intervalLcm n k := by
  sorry

/-
## Chebyshev-type Bound
-/

/-- intervalLcm n k ≤ 4^k for all n, k.
    Strategy: This follows from the Chebyshev function bound: the LCM of
    any k consecutive integers is at most the LCM of 1..k (roughly), which
    is at most 4^k by Chebyshev's theorem (or the central binomial coefficient). -/
theorem intervalLcm_chebyshev_upper (n k : ℕ) :
    intervalLcm n k ≤ 4 ^ k := by
  sorry

end Erdos678Aristotle
