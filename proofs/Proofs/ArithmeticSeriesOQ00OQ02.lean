/-
  Arithmetic Series OQ-00 OQ-02: Weighted Generalization — Counterexample

  Open question from ArithmeticSeriesOQ00 (Nicomachus's Theorem):
  "Can we prove the weighted generalization ∑_{k=1}^n (2k-1)·k² = (∑_{k=1}^n k)²?"

  **Answer: No — the identity is FALSE for all n ≥ 2.**

  This file:
  1. Proves a counterexample at n=2: LHS=13, RHS=9 (by `decide`)
  2. Proves the correct closed form: ∑_{k=1}^n (2k-1)·k² = n(n+1)(3n²+n-1)/6
     equivalently: 6·∑(2k-1)k² + n(n+1) = n²(n+1)(3n+1)
  3. Contrasts with Nicomachus: the correct identity is ∑k³ = (∑k)²

  The identity appears plausible because it holds at n=1 (both sides = 1) and
  because (2k-1) is the k-th odd number, connecting to sum-of-odd-numbers identities.
  The failure at n=2 is decisive: 1·1² + 3·2² = 1 + 12 = 13 ≠ (1+2)² = 9.

  Mathematical derivation of the correct formula:
    ∑(2k-1)k² = 2∑k³ - ∑k² = 2·(n(n+1)/2)² - n(n+1)(2n+1)/6
              = n²(n+1)²/2 - n(n+1)(2n+1)/6
              = n(n+1)/6 · [3n(n+1) - (2n+1)]
              = n(n+1)(3n²+n-1)/6
-/
import Mathlib

noncomputable section

namespace ArithmeticSeriesOQ00OQ02

open Finset BigOperators

-- ============================================================
-- SECTION I: Counterexample — Identity is FALSE
-- ============================================================

/-- The conjectured identity fails at n=2: ∑_{k=1}^2 (2k-1)k² = 1+12 = 13 ≠ (1+2)² = 9. -/
theorem counterexample_n2 :
    ∑ k ∈ Ico 1 3, (2 * k - 1) * k ^ 2 ≠ (∑ k ∈ Ico 1 3, k) ^ 2 := by decide

/-- The identity does hold at n=1 (both sides = 1), creating false initial plausibility. -/
theorem holds_n1 :
    ∑ k ∈ Ico 1 2, (2 * k - 1) * k ^ 2 = (∑ k ∈ Ico 1 2, k) ^ 2 := by decide

/-- Verified at n=3: LHS = 1+12+45 = 58, RHS = (1+2+3)² = 36. -/
theorem counterexample_n3 :
    ∑ k ∈ Ico 1 4, (2 * k - 1) * k ^ 2 ≠ (∑ k ∈ Ico 1 4, k) ^ 2 := by decide

-- ============================================================
-- SECTION II: Correct Closed Form
-- ============================================================

/-- **Correct closed form** (subtraction-free formulation over ℤ):
    6 · ∑_{k=1}^n (2k-1)k² + n(n+1) = n²(n+1)(3n+1).

    Equivalently: ∑_{k=1}^n (2k-1)k² = n(n+1)(3n²+n-1)/6.

    Proof: induction, with the inductive step closed algebraically:
    if the formula holds for n, then adding the (n+1)-th term (2n+1)(n+1)² and
    updating the boundary gives the formula for n+1. Verified by `ring`. -/
theorem weighted_sum_closed_form (n : ℕ) :
    6 * (∑ k ∈ range n, ((2 * ((k : ℤ) + 1) - 1) * ((k : ℤ) + 1) ^ 2)) +
    (n : ℤ) * (n + 1) = (n : ℤ) ^ 2 * (n + 1) * (3 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    -- Apply IH (linear in the partial sum S) + ring identity for the inductive step
    -- IH: 6*S + n*(n+1) = n²*(n+1)*(3n+1)
    -- New term: (2*(n+1)-1)*(n+1)² = (2n+1)*(n+1)²
    -- Algebraic identity (proved by ring): n²(n+1)(3n+1) + 6(2n+1)(n+1)² + (n+1)(n+2) - n(n+1)
    --                                    = (n+1)²(n+2)(3n+4) ✓
    nlinarith [ih, sq_nonneg (n : ℤ),
               show (n : ℤ) ^ 2 * (↑n + 1) * (3 * ↑n + 1) +
                    6 * (2 * ↑n + 1) * (↑n + 1) ^ 2 +
                    (↑n + 1) * (↑n + 2) - ↑n * (↑n + 1) =
                    (↑n + 1) ^ 2 * (↑n + 2) * (3 * ↑n + 4) from by ring]

/-- Spot-checks of the closed form. -/
theorem form_n1 :
    6 * ∑ k ∈ Ico 1 2, (2 * (k : ℤ) - 1) * k ^ 2 + 1 * 2 = 1 ^ 2 * 2 * 4 := by decide
theorem form_n2 :
    6 * ∑ k ∈ Ico 1 3, (2 * (k : ℤ) - 1) * k ^ 2 + 2 * 3 = 2 ^ 2 * 3 * 7 := by decide
theorem form_n3 :
    6 * ∑ k ∈ Ico 1 4, (2 * (k : ℤ) - 1) * k ^ 2 + 3 * 4 = 3 ^ 2 * 4 * 10 := by decide
theorem form_n4 :
    6 * ∑ k ∈ Ico 1 5, (2 * (k : ℤ) - 1) * k ^ 2 + 4 * 5 = 4 ^ 2 * 5 * 13 := by decide

-- ============================================================
-- SECTION III: Gap vs Nicomachus
-- ============================================================

/-- The conjectured weight (2k-1)k² does NOT equal k³ in general. -/
theorem weight_ne_cube : (2 * (2 : ℕ) - 1) * 2 ^ 2 ≠ 2 ^ 3 := by decide

/-- Nicomachus's theorem: ∑k³ = (∑k)². This is the CORRECT identity (not the conjectured one). -/
theorem nicomachus (n : ℕ) :
    4 * ∑ k ∈ range n, ((k : ℤ) + 1) ^ 3 = ((n : ℤ) * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    linarith [show ((n : ℤ) * (n + 1)) ^ 2 + 4 * (↑n + 1) ^ 3 = ((↑n + 1) * (↑n + 2)) ^ 2
              from by ring]

/-- The difference: ∑k³ - ∑(2k-1)k² = ∑(k³ - (2k-1)k²) = ∑(k² - k²·(2k-1)... -/
theorem cubes_minus_weighted (n : ℕ) :
    (∑ k ∈ range n, ((k : ℤ) + 1) ^ 3) -
    (∑ k ∈ range n, ((2 * ((k : ℤ) + 1) - 1) * ((k : ℤ) + 1) ^ 2)) =
    (∑ k ∈ range n, (((k : ℤ) + 1) ^ 2 * (1 - (k : ℤ)))) := by
  simp [← sum_sub_distrib]
  congr 1
  ext k
  ring

end ArithmeticSeriesOQ00OQ02

end
