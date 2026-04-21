/-
  Aristotle targets for Erdős Problem #678 (LCM of Consecutive Integer Intervals)
  Routine supporting lemmas for automated proof search.
  See Erdos678Problem.lean for the main formalization.

  Status: SOLVED (Cambie 2024)

  Status (2026-04-21): The 3 false sorry'd theorems in the main file were replaced:
  - interval_skip_prime_power (FALSE) → padicValNat_intervalLcm (correct)
  - intervalLcm_growth (FALSE, no n-independent bound) → intervalLcm_poly_upper (correct)
  - intervalLcm_chebyshev_upper (FALSE, lcm ≤ 4^k fails for large n) → intervalLcm_le_prod (correct)

  Remaining sorries in main file:
  1. erdos_678_infinitely_many — Cambie 2024 theorem, deep combinatorics
  2. cambie_2024 — same
  3. minimalN def sorry — blocked on existence proof for all k
  4. erdos_growth_rate — blocked on minimalN

  These companion file targets are already proved in the main file:
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
    intervalLcm n k = intervalLcm' n k :=
  Erdos678.intervalLcm_eq_intervalLcm' n k hk

/-
## Monotonicity and Divisibility
-/

/-- Each element n+1+i (for i < k) divides intervalLcm n k.
    Strategy: i ∈ Finset.range k, so n+1+i is one of the factors;
    each factor divides the lcm fold (by Finset.dvd_fold_lcm or similar). -/
theorem dvd_intervalLcm (n k i : ℕ) (hi : i < k) :
    (n + 1 + i) ∣ intervalLcm n k :=
  Erdos678.dvd_intervalLcm n k i hi

/-- intervalLcm n k divides intervalLcm n (k+1).
    Strategy: the range k fold divides the range (k+1) fold since
    the former is a sub-fold of the latter and lcm is monotone. -/
theorem intervalLcm_mono_right (n k : ℕ) :
    intervalLcm n k ∣ intervalLcm n (k + 1) :=
  Erdos678.intervalLcm_mono_right n k

/-
## Prime Power Divisibility
-/

/-- If p^a ∈ [n+1, n+k], then p^a | intervalLcm n k.
    Strategy: p^a is one of the elements in the interval, so by dvd_intervalLcm
    (applied to the appropriate index), p^a divides the LCM. -/
theorem prime_power_divides_intervalLcm (n k p a : ℕ) (hp : p.Prime)
    (hpa : p ^ a ∈ Finset.Icc (n + 1) (n + k)) :
    p ^ a ∣ intervalLcm n k :=
  Erdos678.prime_power_divides_intervalLcm n k p a hp hpa

end Erdos678Aristotle
