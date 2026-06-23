/-
  Failure of Unique Factorization in ℤ[√(-5)]
  Open Question: fundamental-arithmetic-oq-02

  The Fundamental Theorem of Arithmetic states that factorization is unique
  in ℤ. This OQ asks: can we formalize a counterexample showing that
  unique factorization FAILS in some ring extensions?

  The classic counterexample is ℤ[√(-5)]:
    6 = 2 · 3 = (1 + √(-5)) · (1 - √(-5))

  Both factorizations are into irreducible elements, but the two
  factorizations are essentially different (no unit relates the factors).

  This file proves the key properties using the norm function
  N(a + b√(-5)) = a² + 5b² and its multiplicativity.

  References:
  - Hardy-Wright, Chapter 14: Non-unique factorization
  - Mathlib: Zsqrtd (ℤ[√d] ring)
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

namespace FundamentalArithmeticOQ02

open Zsqrtd

-- ============================================================
-- Part I: The Ring ℤ[√(-5)]
-- ============================================================

-- We work in Zsqrtd (-5), which is ℤ[√(-5)].
-- Elements have the form ⟨a, b⟩ representing a + b√(-5).

/-- The norm N(a + b√(-5)) = a² + 5b². This is always non-negative. -/
def normZ5 (z : ℤ√(-5)) : ℤ := z.re * z.re + 5 * z.im * z.im

/-- The norm is multiplicative: N(z · w) = N(z) · N(w). -/
theorem normZ5_mul (z w : ℤ√(-5)) : normZ5 (z * w) = normZ5 z * normZ5 w := by
  simp only [normZ5, Zsqrtd.mul_def, Zsqrtd.re, Zsqrtd.im]
  ring

/-- The norm of a unit is 1: if z · z⁻¹ = 1, then N(z) · N(z⁻¹) = 1. -/
theorem normZ5_eq_one_of_isUnit (z : ℤ√(-5)) (hu : IsUnit z) : normZ5 z = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have h := normZ5_mul u.val u.inv
  rw [show u.val * u.inv = 1 from Units.val_inv_eq_inv_val u ▸ by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]] at h
  simp only [normZ5, Zsqrtd.one_re, Zsqrtd.one_im, mul_zero, add_zero, mul_one] at h
  have hpos_z : 0 ≤ normZ5 u.val := by unfold normZ5; nlinarith [sq_nonneg u.val.re, sq_nonneg u.val.im]
  have hpos_w : 0 ≤ normZ5 u.inv := by unfold normZ5; nlinarith [sq_nonneg u.inv.re, sq_nonneg u.inv.im]
  omega

-- ============================================================
-- Part II: The Two Factorizations of 6
-- ============================================================

/-- 6 as an element of ℤ[√(-5)]: 6 + 0·√(-5). -/
def six : ℤ√(-5) := ⟨6, 0⟩

/-- First factorization: 6 = 2 · 3. -/
theorem factorization_1 : six = ⟨2, 0⟩ * ⟨3, 0⟩ := by
  simp [six, Zsqrtd.ext_iff, Zsqrtd.mul_def]; ring_nf; constructor <;> ring

/-- Second factorization: 6 = (1 + √(-5)) · (1 - √(-5)).
    (1 + √(-5)) · (1 - √(-5)) = 1 - (-5) = 6. -/
theorem factorization_2 : six = ⟨1, 1⟩ * ⟨1, -1⟩ := by
  simp [six, Zsqrtd.ext_iff, Zsqrtd.mul_def]; ring_nf; constructor <;> ring

-- ============================================================
-- Part III: Norms of the Factors
-- ============================================================

/-- N(2) = 4. -/
theorem norm_two : normZ5 ⟨2, 0⟩ = 4 := by unfold normZ5; ring

/-- N(3) = 9. -/
theorem norm_three : normZ5 ⟨3, 0⟩ = 9 := by unfold normZ5; ring

/-- N(1 + √(-5)) = 6. -/
theorem norm_one_plus : normZ5 ⟨1, 1⟩ = 6 := by unfold normZ5; ring

/-- N(1 - √(-5)) = 6. -/
theorem norm_one_minus : normZ5 ⟨1, -1⟩ = 6 := by unfold normZ5; ring

/-- N(6) = 36 = 4 · 9 = 6 · 6. -/
theorem norm_six : normZ5 six = 36 := by unfold normZ5 six; ring

-- ============================================================
-- Part IV: Irreducibility of the Factors
-- ============================================================

/-- 2 is not a unit in ℤ[√(-5)]: N(2) = 4 ≠ 1. -/
theorem two_not_unit : ¬IsUnit (⟨2, 0⟩ : ℤ√(-5)) := by
  intro h
  have := normZ5_eq_one_of_isUnit ⟨2, 0⟩ h
  rw [norm_two] at this
  omega

/-- 3 is not a unit in ℤ[√(-5)]: N(3) = 9 ≠ 1. -/
theorem three_not_unit : ¬IsUnit (⟨3, 0⟩ : ℤ√(-5)) := by
  intro h
  have := normZ5_eq_one_of_isUnit ⟨3, 0⟩ h
  rw [norm_three] at this
  omega

/-- (1 + √(-5)) is not a unit: N = 6 ≠ 1. -/
theorem one_plus_not_unit : ¬IsUnit (⟨1, 1⟩ : ℤ√(-5)) := by
  intro h
  have := normZ5_eq_one_of_isUnit ⟨1, 1⟩ h
  rw [norm_one_plus] at this
  omega

/-- (1 - √(-5)) is not a unit: N = 6 ≠ 1. -/
theorem one_minus_not_unit : ¬IsUnit (⟨1, -1⟩ : ℤ√(-5)) := by
  intro h
  have := normZ5_eq_one_of_isUnit ⟨1, -1⟩ h
  rw [norm_one_minus] at this
  omega

/-- No element of ℤ[√(-5)] has norm 2 or 3.
    If a² + 5b² = 2 or 3, then b = 0 and a² = 2 or 3, which has no integer solution. -/
theorem no_norm_two_or_three (z : ℤ√(-5)) :
    normZ5 z ≠ 2 ∧ normZ5 z ≠ 3 := by
  unfold normZ5
  constructor <;> intro h <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- If normZ5 z = 1, then z is a unit (±1 are the only units in ℤ[√(-5)]).
    a² + 5b² = 1 forces b = 0 and a² = 1, so z · z = 1. -/
private theorem isUnit_of_normZ5_eq_one {z : ℤ√(-5)} (h : normZ5 z = 1) : IsUnit z := by
  unfold normZ5 at h
  have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hre : z.re * z.re = 1 := by nlinarith
  exact isUnit_of_mul_eq_one z z (by ext <;> simp [him] <;> linarith)

/-- 2 is irreducible in ℤ[√(-5)]: if 2 = a·b, then a or b is a unit.
    Proof: N(2) = 4 = N(a)·N(b). Since no element has norm 2 or 3,
    one of N(a), N(b) must be 1 (making that factor a unit). -/
theorem two_irreducible : Irreducible (⟨2, 0⟩ : ℤ√(-5)) := by
  constructor
  · exact two_not_unit
  · intro a b hab
    have hn := normZ5_mul a b
    rw [← hab, norm_two] at hn
    have hna := no_norm_two_or_three a
    have hnb := no_norm_two_or_three b
    have ha_pos : 0 ≤ normZ5 a := by unfold normZ5; nlinarith [sq_nonneg a.re, sq_nonneg a.im]
    have hb_pos : 0 ≤ normZ5 b := by unfold normZ5; nlinarith [sq_nonneg b.re, sq_nonneg b.im]
    -- Both norms positive (zero would give product 0 ≠ 4)
    have ha1 : 0 < normZ5 a := by
      have : normZ5 a ≠ 0 := by intro h; rw [h, zero_mul] at hn; norm_num at hn
      omega
    have hb1 : 0 < normZ5 b := by
      have : normZ5 b ≠ 0 := by intro h; rw [h, mul_zero] at hn; norm_num at hn
      omega
    -- Upper bound from product: N(a) ≤ 4
    have ha_le : normZ5 a ≤ 4 := by
      nlinarith [mul_nonneg ha_pos (show (0 : ℤ) ≤ normZ5 b - 1 from by linarith)]
    -- Only 1 and 4 possible (omega eliminates 2 and 3)
    obtain ⟨hna2, hna3⟩ := hna
    have : normZ5 a = 1 ∨ normZ5 a = 4 := by omega
    rcases this with h1 | h4
    · left; exact isUnit_of_normZ5_eq_one h1
    · right; exact isUnit_of_normZ5_eq_one (show normZ5 b = 1 by rw [h4] at hn; linarith)

/-- 2 does not divide (1 + √(-5)) in ℤ[√(-5)].
    If (1 + √(-5)) = 2 · z, then z = (1/2, 1/2), which is not in ℤ[√(-5)]. -/
theorem two_not_dvd_one_plus : ¬(⟨2, 0⟩ : ℤ√(-5)) ∣ ⟨1, 1⟩ := by
  intro ⟨z, hz⟩
  have hre : 2 * z.re + (-5) * 0 * z.im = 1 := by
    have := congr_arg Zsqrtd.re hz
    simp [Zsqrtd.mul_def] at this
    linarith
  have him : 2 * z.im = 1 := by
    have := congr_arg Zsqrtd.im hz
    simp [Zsqrtd.mul_def] at this
    linarith
  omega

-- ============================================================
-- Part V: The Factorizations Are Essentially Different
-- ============================================================

/-- The two factorizations of 6 are not related by units:
    2 does not divide (1 + √(-5)), so the factorizations
    2·3 and (1+√(-5))·(1-√(-5)) are genuinely different. -/
theorem factorizations_essentially_different :
    ¬(⟨2, 0⟩ : ℤ√(-5)) ∣ ⟨1, 1⟩ := two_not_dvd_one_plus

end FundamentalArithmeticOQ02
