/-
  Derangements: (n − 1) divides D(n) for all n ≥ 2
  Open Question: derangements-convergence-oq-04

  The number of derangements D(n) = numDerangements n is divisible by n − 1
  for every n ≥ 2.

  ## Main Result

  `sub_one_dvd_numDerangements` (PROVED): For n ≥ 2,
    (n - 1) ∣ numDerangements n

  This is an immediate consequence of the additive derangement recurrence
    D(n) = (n - 1) · (D(n-2) + D(n-1))           (numDerangements_add_two)
  which exhibits n − 1 as an explicit factor of D(n). We also record the
  explicit factorisation `numDerangements_eq_sub_one_mul`.

  ## Companion Result

  `numDerangements_congr_neg_one_pow` (PROVED): For all n,
    (n : ℤ) ∣ (numDerangements n - (-1)^n)
  i.e. D(n) ≡ (-1)^n (mod n). This is the classical companion congruence,
  obtained from the multiplicative recurrence
    D(n+1) = (n+1) · D(n) − (-1)^n             (numDerangements_succ)
  by cancelling the alternating term: D(n+1) − (-1)^{n+1} = (n+1) · D(n).

  Both divisibility facts are read directly off the two standard Mathlib
  recurrences for `numDerangements`; the proofs are fully machine-checked
  with no additional axioms.
-/

import Mathlib

open Nat

namespace DerangementsConvergenceOQ04

/-- Explicit factorisation of D(n) for n ≥ 2: the additive recurrence rewritten
    with the index shifted back so that the factor `n - 1` is visible. -/
theorem numDerangements_eq_sub_one_mul (n : ℕ) (hn : 2 ≤ n) :
    numDerangements n = (n - 1) * (numDerangements (n - 2) + numDerangements (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using numDerangements_add_two m

/-- **Main result.** For every n ≥ 2, the number of derangements D(n) is
    divisible by n − 1.

    Proof: write n = m + 2, so n − 1 = m + 1. The additive recurrence
    `numDerangements_add_two` gives
      D(m+2) = (m+1) · (D(m) + D(m+1)),
    exhibiting m + 1 = n − 1 as an explicit factor. -/
theorem sub_one_dvd_numDerangements (n : ℕ) (hn : 2 ≤ n) :
    (n - 1) ∣ numDerangements n := by
  refine ⟨numDerangements (n - 2) + numDerangements (n - 1), ?_⟩
  exact numDerangements_eq_sub_one_mul n hn

/-- **Companion congruence.** For every n, `n ∣ (D(n) − (-1)^n)`, i.e.
    D(n) ≡ (-1)^n (mod n).

    Proof: from the multiplicative recurrence
      D(n+1) = (n+1) · D(n) − (-1)^n        (numDerangements_succ)
    we compute, using (-1)^{n+1} = −(-1)^n,
      D(n+1) − (-1)^{n+1} = (n+1) · D(n),
    so n + 1 divides D(n+1) − (-1)^{n+1}. The case n = 0 is `0 ∣ 0`. -/
theorem numDerangements_congr_neg_one_pow (n : ℕ) :
    (n : ℤ) ∣ ((numDerangements n : ℤ) - (-1) ^ n) := by
  cases n with
  | zero => simp
  | succ k =>
    refine ⟨numDerangements k, ?_⟩
    rw [numDerangements_succ k, pow_succ]
    push_cast
    ring

/-- Restatement of the companion congruence as a `ZMod` equality:
    D(n) = (-1)^n in ℤ/nℤ. -/
theorem numDerangements_zmod_eq (n : ℕ) :
    (numDerangements n : ZMod n) = (-1) ^ n := by
  have h := numDerangements_congr_neg_one_pow n
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr h
  push_cast at this
  linear_combination this

-- Concrete sanity checks of the main divisibility statement.
example : (2 - 1) ∣ numDerangements 2 := sub_one_dvd_numDerangements 2 (by norm_num)
example : (4 - 1) ∣ numDerangements 4 := sub_one_dvd_numDerangements 4 (by norm_num)
example : numDerangements 4 = 9 := by decide
example : numDerangements 5 = 44 := by decide
-- D(5) = 44 = 4 · 11, so 4 = 5 − 1 divides D(5).
example : (5 - 1) ∣ numDerangements 5 := sub_one_dvd_numDerangements 5 (by norm_num)

end DerangementsConvergenceOQ04
