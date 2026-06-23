/-
Proof: Characterization of irrational nth roots
Research: cube-root-2-irrational-oq-01
Open question: "n√m is irrational iff m is not a perfect n-th power"
Method: Assemble the two directions already proven (0-sorry/0-axiom) in
        `NthRootIrrational.lean` into the single iff characterization the
        open question names, and restate it with the natural-number
        notion of "perfect n-th power".
-/

import Proofs.NthRootIrrational
import Mathlib.NumberTheory.Real.Irrational

/-
# Characterization: ⁿ√m is irrational ⇔ m is not a perfect n-th power

`NthRootIrrational.lean` proves the two halves separately:

* `irrational_nthRoot`        : not a perfect power ⟹ irrational
* `nthRoot_of_perfect_power`  : a perfect power has an integer root (⟹ rational)

This file unifies them into the explicit biconditional named by the open
question, and provides both the integer and natural-number formulations of
"perfect n-th power" (they agree for a natural-number radicand).
-/

namespace NthRootIrrational

/-- "m is a perfect n-th power over ℤ" and "over ℕ" coincide for a
    natural-number radicand `m`: any integer n-th root has the same
    n-th power as its absolute value. -/
theorem isPerfectNthPow_int_iff_nat (n m : ℕ) :
    (∃ k : ℤ, k ^ n = (m : ℤ)) ↔ (∃ k : ℕ, k ^ n = m) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    have h := congrArg Int.natAbs hk
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at h
  · rintro ⟨k, hk⟩
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩

/-- **Characterization of irrational nth roots (integer form).**

    For `n ≥ 2`, the real nth root `m^(1/n)` of a natural number `m` is
    irrational if and only if `m` is not a perfect n-th power (no integer
    `k` satisfies `k ^ n = m`).

    This is the biconditional named by `cube-root-2-irrational-oq-01`. The
    `←` direction is `irrational_nthRoot`; the `→` direction is the
    contrapositive of `nthRoot_of_perfect_power`. -/
theorem irrational_nthRoot_iff (n m : ℕ) (hn : 1 < n) :
    Irrational (nthRoot n m) ↔ ¬ ∃ (k : ℤ), k ^ n = (m : ℤ) := by
  constructor
  · intro hirr
    rintro ⟨k, hk⟩
    have hmnat : m = k.natAbs ^ n := by
      have h := congrArg Int.natAbs hk
      rw [Int.natAbs_pow, Int.natAbs_natCast] at h
      exact h.symm
    have heq : nthRoot n m = (k.natAbs : ℝ) := by
      rw [hmnat]
      exact nthRoot_of_perfect_power n k.natAbs (by omega)
    rw [heq] at hirr
    exact (Nat.not_irrational k.natAbs) hirr
  · exact irrational_nthRoot n m hn

/-- **Characterization of irrational nth roots (natural-number form).**

    For `n ≥ 2`, `m^(1/n)` is irrational iff `m` is not a perfect n-th power
    over the naturals. This is the plain-language statement of the open
    question. -/
theorem irrational_nthRoot_iff_nat (n m : ℕ) (hn : 1 < n) :
    Irrational (nthRoot n m) ↔ ¬ ∃ (k : ℕ), k ^ n = m := by
  rw [irrational_nthRoot_iff n m hn, isPerfectNthPow_int_iff_nat]

/-- Cube root of 2 instance of the characterization: ∛2 is irrational
    precisely because 2 is not a perfect cube. -/
theorem irrational_cbrt2_iff : Irrational (nthRoot 3 2) ↔ ¬ ∃ (k : ℕ), k ^ 3 = 2 :=
  irrational_nthRoot_iff_nat 3 2 (by norm_num)

end NthRootIrrational
