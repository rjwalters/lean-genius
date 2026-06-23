/-
# Unified Osculator Theorem

Open Question (from divisibility-truncation-general):
  Can the positive and negative osculator theorems be merged into a
  single theorem with a signed osculator c ∈ ℤ?

Answer: YES. The key observation is that `truncation_pos` already works with
c ∈ ℤ and the condition d | (10c - 1). The "negative osculator" case is simply
the positive case with c replaced by -c_neg, since d | (10c_neg + 1)
implies d | (10·(-c_neg) - 1).

This gives a single **Unified Osculator Theorem** that subsumes both cases.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

open Nat

namespace UnifiedOsculator

-- ============================================================================
-- Part I: The Unified Osculator Theorem
-- ============================================================================

private lemma div_mod_cast (n : ℕ) : (n : ℤ) = 10 * ↑(n / 10) + ↑(n % 10) := by
  have := Nat.div_add_mod n 10; push_cast; omega

/-- **The Unified Osculator Theorem**

    For any divisor d coprime to 10 and any integer c satisfying d | (10c - 1):

      d | n  ↔  d | (n/10 + c · (n%10))

    This single statement subsumes both positive and negative osculator rules:
    - Positive osculator (c > 0): "add c times the last digit"
    - Negative osculator (c < 0): "subtract |c| times the last digit"

    The proof uses the identity:
      10 · (n/10 + c·(n%10)) = n + (10c-1)·(n%10)
    When d | (10c-1), divisibility transfers through coprimality. -/
theorem unified_osculator (d : ℕ) (c : ℤ) (n : ℕ)
    (hcop : IsCoprime (d : ℤ) 10)
    (hc : (d : ℤ) ∣ 10 * c - 1) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) + c * ↑(n % 10)) := by
  have hdiv := div_mod_cast n
  have hkey : (10 : ℤ) * (↑(n / 10) + c * ↑(n % 10)) = ↑n + (10 * c - 1) * ↑(n % 10) := by
    linear_combination -hdiv
  constructor
  · intro hn
    have h1 : (d : ℤ) ∣ ↑n + (10 * c - 1) * ↑(n % 10) :=
      dvd_add hn (dvd_mul_of_dvd_left hc _)
    rw [← hkey] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  · intro hq
    have h10 : (d : ℤ) ∣ 10 * (↑(n / 10) + c * ↑(n % 10)) :=
      dvd_mul_of_dvd_right hq 10
    rw [hkey] at h10
    have hterm : (d : ℤ) ∣ (10 * c - 1) * ↑(n % 10) := dvd_mul_of_dvd_left hc _
    have hsub := Int.dvd_sub h10 hterm
    simp only [add_sub_cancel_right] at hsub
    exact_mod_cast hsub

-- ============================================================================
-- Part II: Negative Osculator as Special Case
-- ============================================================================

/-- The negative osculator rule is a special case of the unified theorem.

    If d | (10·c_neg + 1), then d | (10·(-c_neg) - 1), so:
      d | n ↔ d | (n/10 + (-c_neg)·(n%10)) = d | (n/10 - c_neg·(n%10))

    No separate theorem needed! -/
theorem neg_osculator_from_unified (d : ℕ) (c : ℤ) (n : ℕ)
    (hcop : IsCoprime (d : ℤ) 10)
    (hc : (d : ℤ) ∣ 10 * c + 1) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) - c * ↑(n % 10)) := by
  -- Use unified_osculator with osculator -c
  have hc' : (d : ℤ) ∣ 10 * (-c) - 1 := by
    rw [show 10 * (-c) - 1 = -(10 * c + 1) by ring]
    exact dvd_neg.mpr hc
  have h := unified_osculator d (-c) n hcop hc'
  simp only [neg_mul] at h
  exact h

-- ============================================================================
-- Part III: Recovering Both Specific Cases
-- ============================================================================

/-- d=7 via unified theorem with c=-2 (negative osculator). -/
theorem seven_unified (n : ℕ) :
    (7 : ℤ) ∣ n ↔ (7 : ℤ) ∣ (↑(n / 10) - 2 * ↑(n % 10)) :=
  neg_osculator_from_unified 7 2 n (by decide) ⟨3, by norm_num⟩

/-- d=11 via unified theorem with c=-1. -/
theorem eleven_unified (n : ℕ) :
    (11 : ℤ) ∣ n ↔ (11 : ℤ) ∣ (↑(n / 10) - 1 * ↑(n % 10)) :=
  neg_osculator_from_unified 11 1 n (by decide) ⟨1, by norm_num⟩

/-- d=13 via unified theorem with c=4 (positive osculator). -/
theorem thirteen_unified (n : ℕ) :
    (13 : ℤ) ∣ n ↔ (13 : ℤ) ∣ (↑(n / 10) + 4 * ↑(n % 10)) :=
  unified_osculator 13 4 n (by decide) ⟨3, by norm_num⟩

/-- d=17 via unified theorem with c=-5. -/
theorem seventeen_unified (n : ℕ) :
    (17 : ℤ) ∣ n ↔ (17 : ℤ) ∣ (↑(n / 10) - 5 * ↑(n % 10)) :=
  neg_osculator_from_unified 17 5 n (by decide) ⟨3, by norm_num⟩

/-- d=19 via unified theorem with c=2. -/
theorem nineteen_unified (n : ℕ) :
    (19 : ℤ) ∣ n ↔ (19 : ℤ) ∣ (↑(n / 10) + 2 * ↑(n % 10)) :=
  unified_osculator 19 2 n (by decide) ⟨1, by norm_num⟩

-- ============================================================================
-- Part V: Dual Osculator Relationship
-- ============================================================================

/-- For d coprime to 10, the positive and negative osculators c₊ and c₋ satisfy
    c₊ + c₋ = d (when both are taken in {1,...,d-1}).

    This is because 10c₊ ≡ 1 and 10c₋ ≡ -1 (mod d), so 10(c₊ + c₋) ≡ 0 (mod d),
    and since gcd(10,d) = 1, we get d | (c₊ + c₋). For the smallest values,
    c₊ + c₋ = d. -/
theorem dual_osculators_sum (d : ℕ) (c_pos c_neg : ℤ)
    (hcop : IsCoprime (d : ℤ) 10)
    (hp : (d : ℤ) ∣ 10 * c_pos - 1)
    (hn : (d : ℤ) ∣ 10 * c_neg + 1) :
    (d : ℤ) ∣ (c_pos + c_neg) := by
  have h : (d : ℤ) ∣ 10 * (c_pos + c_neg) := by
    have := dvd_add hp hn
    rw [show 10 * c_pos - 1 + (10 * c_neg + 1) = 10 * (c_pos + c_neg) by ring] at this
    exact this
  exact hcop.dvd_of_dvd_mul_left h

/-- Verification: 7's osculators sum to 7. c₊=5 and c₋=2, 5+2=7. -/
example : (7 : ℤ) ∣ (5 + 2) := ⟨1, by norm_num⟩

/-- Verification: 13's osculators sum to 13. c₊=4 and c₋=9, 4+9=13. -/
example : (13 : ℤ) ∣ (4 + 9) := ⟨1, by norm_num⟩

/-- Verification: 17's osculators sum to 17. c₊=12 and c₋=5, 12+5=17. -/
example : (17 : ℤ) ∣ (12 + 5) := ⟨1, by norm_num⟩

-- ============================================================================
-- Part VI: Sanity Checks
-- ============================================================================

example : 7 ∣ 49 := by native_decide
example : 13 ∣ 169 := by native_decide
example : 19 ∣ 57 := by native_decide
example : ¬(7 ∣ 50) := by native_decide

#check unified_osculator
#check neg_osculator_from_unified
#check dual_osculators_sum

end UnifiedOsculator
