/-
Copyright (c) 2024-2025 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.ElementaryQuadraticReciprocityOQ03OQ02

/-
# Multiplicativity of the Kronecker Symbol (First Argument)

## Open Question (elementary-quadratic-reciprocity-oq-03-oq-02-oq-01)
Prove multiplicativity of the Kronecker symbol in the first argument:
  kronecker (a * b) n = kronecker a n * kronecker b n
for all integers a, b, n with a * b ≠ 0.

## What This Proves
The Kronecker symbol extends the Jacobi symbol to all integer moduli.
Multiplicativity in the first argument (the "numerator") means:
  (ab/n) = (a/n)(b/n)

This is proved by case analysis on n, using:
- n = 0: kronecker0(ab) = kronecker0(a) · kronecker0(b) (unit character)
- n = -1: kroneckerNeg1(ab) = kroneckerNeg1(a) · kroneckerNeg1(b) (sign character)
- n = 1: trivially 1 = 1·1
- else: Jacobi multiplicativity jacobiSym.mul_left + sign character multiplicativity

The hypothesis a*b ≠ 0 is necessary (see OQ03OQ02 for the counterexample at
a=-3, b=0, n=-1 where kroneckerNeg1(0)=1 but the product gives -1).

## Status
- [x] kronecker0_mul_of_ne_zero
- [x] kroneckerNeg1_mul_of_ne_zero
- [x] kronecker_mul_left_proved (main theorem)
- 0 sorries, 0 axioms

## References
- Kronecker (1885)
- Hardy-Wright, Chapter 6
-/

namespace KroneckerSymbol

open Nat Int

/-
## Part 1: Multiplicativity of kronecker0

kronecker0 a = if |a| = 1 then 1 else 0

For a*b ≠ 0: |a*b| = 1 iff |a| = |b| = 1 (in ℤ, units are ±1).
Product: kronecker0(a) * kronecker0(b) = 1*1 = 1 if both units, 0 otherwise.
-/

/-- kronecker0 is multiplicative for nonzero arguments. -/
theorem kronecker0_mul_of_ne_zero (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    kronecker0 (a * b) = kronecker0 a * kronecker0 b := by
  simp only [kronecker0]
  -- Case analysis: a = ±1, b = ±1, or not
  by_cases ha1 : a = 1 ∨ a = -1 <;> by_cases hb1 : b = 1 ∨ b = -1 <;> simp_all
  · -- Both units: ab = ±1
    rcases ha1 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> simp
  · -- a is unit, b is not: |ab| ≠ 1 since |b| > 1
    push_neg at hb1
    rcases ha1 with rfl | rfl
    · simp at hb1 ⊢; exact hb1
    · simp at hb1 ⊢; intro h; exact hb1 (Or.symm h)
  · -- a is not unit, b is unit: |ab| ≠ 1 since |a| > 1
    push_neg at ha1
    rcases hb1 with rfl | rfl
    · simp at ha1 ⊢; exact ha1
    · simp at ha1 ⊢; intro h
      rcases h with rfl | rfl
      · exact ha1 (Or.inr rfl)
      · exact ha1 (Or.inl rfl)
  · -- Neither is unit: product is 0 * anything = 0
    push_neg at ha1 hb1
    simp [ha1]

/-
## Part 2: Multiplicativity of kroneckerNeg1

kroneckerNeg1 a = if a < 0 then -1 else 1

This is the sign character: maps positive to 1, negative to -1.
Product of signs = sign of product (for nonzero arguments).
-/

/-- kroneckerNeg1 is multiplicative for nonzero arguments.
    This is the standard sign character: sgn(ab) = sgn(a)·sgn(b). -/
theorem kroneckerNeg1_mul_of_ne_zero (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    kroneckerNeg1 (a * b) = kroneckerNeg1 a * kroneckerNeg1 b := by
  simp only [kroneckerNeg1]
  by_cases ha0 : a < 0 <;> by_cases hb0 : b < 0 <;> simp_all
  · -- a < 0, b < 0: ab > 0, (-1)*(-1) = 1  ✓
    constructor
    · linarith [Int.mul_pos_of_neg_of_neg ha0 hb0]
    · ring
  · -- a < 0, b ≥ 0: b > 0, ab < 0, (-1)*1 = -1  ✓
    push_neg at hb0
    have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    exact Int.mul_neg_of_neg_of_pos ha0 hbpos
  · -- a ≥ 0, b < 0: a > 0, ab < 0, 1*(-1) = -1  ✓
    push_neg at ha0
    have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    exact Int.mul_neg_of_pos_of_neg hapos hb0
  · -- a ≥ 0, b ≥ 0: a,b > 0, ab > 0, 1*1 = 1  ✓
    push_neg at ha0 hb0
    have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    linarith [Int.mul_pos hapos hbpos]

/-
## Part 3: Main Theorem — kronecker_mul_left

Case analysis on n, using the case-specific multiplicativity results
and Mathlib's jacobiSym.mul_left for the Jacobi symbol.
-/

/-- **Multiplicativity of the Kronecker symbol in the first argument.**

    This proves the axiom `kronecker_mul_left` from OQ03OQ02.
    The proof proceeds by case analysis on n:
    - n = 0: uses kronecker0_mul_of_ne_zero
    - n = -1: uses kroneckerNeg1_mul_of_ne_zero
    - n = 1: trivial (both sides are 1)
    - else: uses jacobiSym.mul_left + kroneckerNeg1_mul_of_ne_zero -/
theorem kronecker_mul_left_proved (a b n : ℤ) (hab : a * b ≠ 0) :
    kronecker (a * b) n = kronecker a n * kronecker b n := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb : b ≠ 0 := right_ne_zero_of_mul hab
  -- Unfold kronecker and case split on n
  simp only [kronecker]
  split_ifs with h0 h1 h2 h0' h1' h2' h0'' h1'' h2''
  · -- n = 0: kronecker0 multiplicativity
    exact kronecker0_mul_of_ne_zero a b ha hb
  · -- n = -1: kroneckerNeg1 multiplicativity
    exact kroneckerNeg1_mul_of_ne_zero a b ha hb
  · -- n = 1: both sides are 1
    ring
  · -- General case: sign * jacobiSym
    -- Split on whether n < 0 (determines the sign factor)
    by_cases hn_neg : n < 0
    · -- n < 0: sign factor is kroneckerNeg1
      simp only [hn_neg, ite_true]
      rw [kroneckerNeg1_mul_of_ne_zero a b ha hb, jacobiSym.mul_left]
      ring
    · -- n ≥ 0: sign factor is 1
      simp only [hn_neg, ite_false]
      rw [jacobiSym.mul_left]
      ring

-- Verify the type matches the axiom
#check @kronecker_mul_left_proved

/-
## Part 4: Multiplicativity in the Second Argument

kronecker a (m * n) = kronecker a m * kronecker a n

This is the second multiplicativity axiom from OQ03OQ02.
The proof is more involved than the first argument because the
sign factor (kroneckerNeg1) depends on the sign of the modulus.
-/

/-- kroneckerNeg1 is an involution: kroneckerNeg1(a)² = 1. -/
private lemma kroneckerNeg1_sq (a : ℤ) : kroneckerNeg1 a * kroneckerNeg1 a = 1 := by
  simp only [kroneckerNeg1]; split_ifs <;> ring

/-- For n ≠ 0 and n ≠ ±1, kronecker a (-n) = kroneckerNeg1 a * kronecker a n.
    Negating the modulus introduces (or removes) the sign character. -/
private lemma kronecker_neg_modulus (a n : ℤ) (hn : n ≠ 0) (hn1 : n ≠ 1) (hn_neg1 : n ≠ -1) :
    kronecker a (-n) = kroneckerNeg1 a * kronecker a n := by
  have h_neg_ne : -n ≠ 0 := by omega
  have h_neg_ne1 : -n ≠ 1 := by omega
  have h_neg_ne_neg1 : -n ≠ -1 := by omega
  simp only [kronecker, h_neg_ne, hn, hn1, hn_neg1, h_neg_ne1, h_neg_ne_neg1,
    ite_false, Int.natAbs_neg]
  by_cases h : n < 0
  · -- n < 0: -n > 0, so sign(-n) = 1, sign(n) = kroneckerNeg1 a
    have : ¬(-n < 0) := by omega
    simp [h, this, kroneckerNeg1_sq]
  · -- n ≥ 0: n > 0 (since n ≠ 0), -n < 0, sign(-n) = kroneckerNeg1 a, sign(n) = 1
    push_neg at h
    have hpos : 0 < n := lt_of_le_of_ne h (Ne.symm hn)
    have : -n < 0 := by omega
    simp [this, hpos, show ¬(n < 0) from by omega]; ring

/-- **Multiplicativity of the Kronecker symbol in the second argument.**

    This proves the axiom `kronecker_mul_right` from OQ03OQ02.
    kronecker a (m * n) = kronecker a m * kronecker a n for m * n ≠ 0.

    Proof: case analysis on m,n being ±1 or general, then
    sign factor multiplicativity + jacobiSym.mul_right. -/
theorem kronecker_mul_right_proved (a m n : ℤ) (hmn : m * n ≠ 0) :
    kronecker a (m * n) = kronecker a m * kronecker a n := by
  have hm : m ≠ 0 := left_ne_zero_of_mul hmn
  have hn : n ≠ 0 := right_ne_zero_of_mul hmn
  -- Case: m = 1
  by_cases hm1 : m = 1
  · subst hm1; simp only [one_mul, kronecker, show (1 : ℤ) ≠ 0 by omega,
      show (1 : ℤ) ≠ -1 by omega, ite_true, ite_false]; ring
  -- Case: n = 1
  by_cases hn1 : n = 1
  · subst hn1; simp only [mul_one, kronecker, show (1 : ℤ) ≠ 0 by omega,
      show (1 : ℤ) ≠ -1 by omega, ite_true, ite_false]; ring
  -- Case: m = -1
  by_cases hm_neg1 : m = -1
  · subst hm_neg1
    simp only [neg_one_mul, kronecker, show (-1 : ℤ) ≠ 0 by omega,
      show (-1 : ℤ) = -1 from rfl, ite_true, ite_false]
    -- RHS: kroneckerNeg1 a * kronecker a n
    -- LHS: kronecker a (-n)
    by_cases hn_neg1 : n = -1
    · subst hn_neg1; simp [kroneckerNeg1_sq]
    · rw [show kronecker a (-n) = kroneckerNeg1 a * kronecker a n from
        kronecker_neg_modulus a n hn hn1 hn_neg1]
  -- Case: n = -1
  by_cases hn_neg1 : n = -1
  · subst hn_neg1
    simp only [mul_neg_one, kronecker, show (-1 : ℤ) ≠ 0 by omega,
      show (-1 : ℤ) = -1 from rfl, ite_true, ite_false]
    rw [show kronecker a (-m) = kroneckerNeg1 a * kronecker a m from
      kronecker_neg_modulus a m hm hm1 hm_neg1]
    ring
  -- General case: m, n ≠ 0, ±1
  -- kronecker a (m*n) = sign(m*n) * jacobiSym a |m*n|
  -- = sign(m) * sign(n) * jacobiSym a |m| * jacobiSym a |n|   (sign mult + Jacobi mult)
  -- = kronecker a m * kronecker a n
  have hmn0 : m * n ≠ 0 := hmn
  have hmn1 : m * n ≠ 1 := by
    intro h; rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
    · exact hm1 rfl
    · exact hm_neg1 rfl
  have hmn_neg1 : m * n ≠ -1 := by
    intro h; rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hm1 rfl
    · exact hm_neg1 rfl
  simp only [kronecker, hmn0, hmn1, hmn_neg1, hm, hn, hm1, hm_neg1, hn1, hn_neg1,
    ite_false, Int.natAbs_mul]
  -- Now: sign(m*n) * jacobiSym a (|m|*|n|) = (sign(m) * jacobiSym a |m|) * (sign(n) * jacobiSym a |n|)
  rw [jacobiSym.mul_right]
  -- Handle sign factors
  by_cases hm_neg : m < 0 <;> by_cases hn_neg : n < 0
  · -- m < 0, n < 0: m*n > 0, sign = 1, product of signs = kroneckerNeg1² = 1
    have : ¬(m * n < 0) := by nlinarith [Int.mul_pos_of_neg_of_neg hm_neg hn_neg]
    simp [hm_neg, hn_neg, this, kroneckerNeg1_sq]
  · -- m < 0, n > 0: m*n < 0
    push_neg at hn_neg
    have hn_pos : 0 < n := lt_of_le_of_ne hn_neg (Ne.symm hn)
    have : m * n < 0 := Int.mul_neg_of_neg_of_pos hm_neg hn_pos
    simp [hm_neg, hn_neg, this, show ¬(n < 0) from not_lt.mpr hn_neg.le]; ring
  · -- m > 0, n < 0: m*n < 0
    push_neg at hm_neg
    have hm_pos : 0 < m := lt_of_le_of_ne hm_neg (Ne.symm hm)
    have : m * n < 0 := Int.mul_neg_of_pos_of_neg hm_pos hn_neg
    simp [hm_neg, hn_neg, this, show ¬(m < 0) from not_lt.mpr hm_neg.le]; ring
  · -- m > 0, n > 0: m*n > 0
    push_neg at hm_neg hn_neg
    have hm_pos : 0 < m := lt_of_le_of_ne hm_neg (Ne.symm hm)
    have hn_pos : 0 < n := lt_of_le_of_ne hn_neg (Ne.symm hn)
    have : ¬(m * n < 0) := not_lt.mpr (le_of_lt (Int.mul_pos hm_pos hn_pos))
    simp [hm_neg, hn_neg, this, show ¬(m < 0) from not_lt.mpr hm_neg.le,
      show ¬(n < 0) from not_lt.mpr hn_neg.le]; ring

#check @kronecker_mul_right_proved

end KroneckerSymbol
