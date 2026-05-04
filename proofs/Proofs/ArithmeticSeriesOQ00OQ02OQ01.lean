import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Proofs.ArithmeticSeriesOQ00

/-
# Alternative Weights for Nicomachus-Type Sums (OQ-00-OQ-02-OQ-01)

## Problem Statement

The parent proof (ArithmeticSeriesOQ00OQ02) showed that w(k) = k² does NOT satisfy
∑_{k=1}^n w(k)·(2k-1) = (∑_{k=1}^n k)² for n ≥ 2.

This file answers: is there ANY other weight w(k) satisfying the identity?

## Answer: YES — and the rational weight is unique

The unique rational weight is **w(k) = k³ / (2k-1)**.

**Why it works**: w(k)·(2k-1) = k³ (the (2k-1) factors cancel), so the sum becomes
∑k³ = (∑k)² — exactly Nicomachus's theorem.

**Uniqueness by telescoping**: If w satisfies the identity for all n, then for each k ≥ 1:
  w(k)·(2k-1) = S_k - S_{k-1} = (k(k+1)/2)² - ((k-1)k/2)² = k³
So w(k) = k³/(2k-1) is the only rational solution.

**No integer weight exists**: The value at k=2 is forced to be 8/3 ∉ ℤ
by the n=1 and n=2 cases.
-/

noncomputable section

namespace ArithmeticSeriesOQ00OQ02OQ01

open Finset BigOperators NicomachusTheorem

-- ============================================================
-- SECTION I: The Rational Weight w(k) = k³ / (2k-1)
-- ============================================================

/-- The unique rational weight satisfying the Nicomachus-type identity. -/
def nicWeight (k : ℕ) : ℚ := (k : ℚ)^3 / (2 * (k : ℚ) - 1)

/-- For k ≥ 1, the denominator 2k - 1 is positive (hence nonzero) over ℚ. -/
private lemma denom_pos (k : ℕ) (hk : 1 ≤ k) : 0 < 2 * (k : ℚ) - 1 := by
  have : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  linarith

/-- **Key cancellation**: w(k) · (2k-1) = k³ for all k ≥ 1. -/
theorem nicWeight_mul (k : ℕ) (hk : 1 ≤ k) :
    nicWeight k * (2 * (k : ℚ) - 1) = (k : ℚ)^3 := by
  unfold nicWeight
  exact div_mul_cancel₀ _ (ne_of_gt (denom_pos k hk))

-- ============================================================
-- SECTION II: Main Identity
-- ============================================================

/-- **Alternative Weight Identity**: For all n,
    ∑_{k=1}^n [k³/(2k-1)] · (2k-1) = (∑_{k=1}^n k)².

    Proof: Each summand simplifies to k³, then Nicomachus applies. -/
theorem nicWeight_sum_eq (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), nicWeight k * (2 * (k : ℚ) - 1)) =
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ))^2 := by
  have h_term : ∀ k ∈ Ico 1 (n + 1),
      nicWeight k * (2 * (k : ℚ) - 1) = (k : ℚ)^3 := fun k hk =>
    nicWeight_mul k (mem_Ico.mp hk).1
  rw [sum_congr rfl h_term]
  exact sum_cubes_eq_sq_sum n

-- ============================================================
-- SECTION III: Concrete Values
-- ============================================================

/-- w(1) = 1. -/
theorem nicWeight_one : nicWeight 1 = 1 := by unfold nicWeight; norm_num

/-- w(2) = 8/3, which is not an integer. -/
theorem nicWeight_two : nicWeight 2 = 8 / 3 := by unfold nicWeight; norm_num

/-- w(3) = 27/5, which is not an integer. -/
theorem nicWeight_three : nicWeight 3 = 27 / 5 := by unfold nicWeight; norm_num

-- ============================================================
-- SECTION IV: No Integer Weight
-- ============================================================

/-- **No Integer Weight**: There is no integer-valued weight satisfying the
    Nicomachus-type identity for all n.

    Proof: The n=1 case forces w(1) = 1; the n=2 case forces w(1) + 3·w(2) = 9.
    Combining: 3·w(2) = 8, which has no solution in ℤ (proved by omega). -/
theorem no_integer_weight (w : ℕ → ℤ)
    (h : ∀ n, ∑ k ∈ Ico 1 (n + 1), w k * (2 * (k : ℤ) - 1) =
             (∑ k ∈ Ico 1 (n + 1), (k : ℤ))^2) : False := by
  have hh1 := h 1
  have hh2 := h 2
  -- Normalize n+1 to concrete values and expand finite sums
  simp only [show (Ico 1 (1 + 1) : Finset ℕ) = {1} from by decide,
             show (Ico 1 (2 + 1) : Finset ℕ) = {1, 2} from by decide,
             sum_singleton,
             sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) from by decide),
             sum_singleton] at hh1 hh2
  -- Evaluate concrete arithmetic: resolve casts, compute 2*1-1=1 and 2*2-1=3
  push_cast at hh1 hh2
  ring_nf at hh1 hh2
  -- hh1 : w 1 = 1, hh2 : w 1 + 3 * w 2 = 9 → 3 * w 2 = 8, impossible in ℤ
  omega

-- ============================================================
-- SECTION V: Uniqueness (Rational Weight is Forced)
-- ============================================================

/-- **Uniqueness**: Any rational weight satisfying the identity for all n must equal
    nicWeight at k=1 and k=2. Forced by the n=1 and n=2 cases via telescoping. -/
theorem nicWeight_unique_at_12 (w : ℕ → ℚ)
    (h : ∀ n, ∑ k ∈ Ico 1 (n + 1), w k * (2 * (k : ℚ) - 1) =
             (∑ k ∈ Ico 1 (n + 1), (k : ℚ))^2) :
    w 1 = nicWeight 1 ∧ w 2 = nicWeight 2 := by
  have hh1 := h 1
  have hh2 := h 2
  simp only [show (Ico 1 (1 + 1) : Finset ℕ) = {1} from by decide,
             show (Ico 1 (2 + 1) : Finset ℕ) = {1, 2} from by decide,
             sum_singleton,
             sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) from by decide),
             sum_singleton] at hh1 hh2
  -- Evaluate concrete arithmetic: resolve casts, compute 2*1-1=1 and 2*2-1=3
  push_cast at hh1 hh2
  ring_nf at hh1 hh2
  -- hh1 : w 1 = 1, hh2 : w 1 + 3 * w 2 = 9
  rw [nicWeight_one, nicWeight_two]
  constructor
  · linarith
  · linarith

end ArithmeticSeriesOQ00OQ02OQ01

end
