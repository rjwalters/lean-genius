/-
  A concrete small-prime witness for Gauss's hard sign theorem: the prime `p = 5`.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, the quadratic Gauss sum `g = gaussSum (chiC p) ψ` is pinned by the
  elementary dichotomy + magnitude (see `QuadraticGaussSumSignReduction`) to one of four
  points: `±√p` for `p ≡ 1 (mod 4)`, or `±i√p` for `p ≡ 3 (mod 4)`.  Gauss's *hard* sign
  theorem fixes the leading sign,
      g = √p     (p ≡ 1 mod 4),     g = i·√p   (p ≡ 3 mod 4).
  The general positivity `0 < Re g` / `0 < Im g` is open and needs heavy DFT/theta
  infrastructure absent from Mathlib.

  The companion file `QuadraticGaussSumSignSmall` settles the smallest case `p = 3`
  (≡ 3 mod 4), confirming the open crux `0 < Im g` there.  This file settles the smallest
  case of the OTHER residue class, `p = 5` (≡ 1 mod 4), confirming the open crux
  `0 < Re g` — the first sign determination for the `p ≡ 1 (mod 4)` branch.

  Method (sign estimate, not exact trig).  For the standard character `ψ(x) = ζ^x` with
  `ζ = exp(2πi/5)`, the values of `quadraticChar (ZMod 5)` are `0, 1, -1, -1, 1` at
  `0,1,2,3,4`, so the five-term sum collapses to

      g = ζ - ζ² - ζ³ + ζ⁴.

  Taking real parts and folding `cos(6π/5) = cos(4π/5)`, `cos(8π/5) = cos(2π/5)` gives

      Re g = 2·cos(2π/5) - 2·cos(4π/5).

  Crucially we do NOT need the exact values `cos(2π/5) = (√5-1)/4` etc.: positivity follows
  from the coarse sign facts `cos(2π/5) > 0` (angle in `(0, π/2)`) and `cos(4π/5) < 0`
  (since `cos(4π/5) = -cos(π/5) < 0`).  Combined with the four-point pinning `g = ±√5`,
  this forces `g = +√5`.

  Sorry-free and axiom-free.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare
import Proofs.QuadraticGaussSumSignReduction

open scoped BigOperators Real
open Complex QuadraticGaussSumSquare QuadraticGaussSumSignReduction

namespace QuadraticGaussSumSignSmallFive

/-- `5` is prime; needed for `chiC 5` and the Gauss-sum machinery. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The standard primitive fifth root of unity `ζ = exp(2πi/5)`. -/
noncomputable def ζ : ℂ := Complex.exp (2 * π * Complex.I / 5)

theorem ζ_pow_five : ζ ^ 5 = 1 := by
  have h : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / 5)) 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [ζ] using h.pow_eq_one

/-- The standard additive character of `ZMod 5` valued in `ℂ`, `ψ(x) = ζ^x`. -/
noncomputable def ψ₅ : AddChar (ZMod 5) ℂ := AddChar.zmodChar 5 ζ_pow_five

theorem ψ₅_isPrimitive : ψ₅.IsPrimitive := by
  have hroot : IsPrimitiveRoot ζ 5 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 5 (by norm_num)
  exact AddChar.zmodChar_primitive_of_primitive_root 5 hroot

/-! ### The Gauss sum for `p = 5` collapses to `ζ - ζ² - ζ³ + ζ⁴` -/

/-- `chiC 5` takes values `0, 1, -1, -1, 1` at `0, 1, 2, 3, 4`, so the five-term Gauss
sum is `ζ - ζ² - ζ³ + ζ⁴`. -/
theorem gaussSum_five_eq :
    gaussSum (chiC 5) ψ₅ = ζ - ζ ^ 2 - ζ ^ 3 + ζ ^ 4 := by
  have huniv : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  rw [gaussSum, huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  -- character values
  have h0 : chiC 5 (0 : ZMod 5) = 0 := by simp [chiC]
  have h1 : chiC 5 (1 : ZMod 5) = 1 := by simp
  have h4 : chiC 5 (4 : ZMod 5) = 1 := by
    have h4neg : (4 : ZMod 5) = -1 := by decide
    rw [h4neg, chiC_neg_one (by norm_num)]
    norm_num
  have h2 : chiC 5 (2 : ZMod 5) = -1 := by
    have hns : ¬ IsSquare (2 : ZMod 5) := by decide
    have hq : (quadraticChar (ZMod 5)) 2 = -1 :=
      (quadraticChar_neg_one_iff_not_isSquare).mpr hns
    simp [chiC, MulChar.ringHomComp_apply, hq]
  have h3 : chiC 5 (3 : ZMod 5) = -1 := by
    have hns : ¬ IsSquare (3 : ZMod 5) := by decide
    have hq : (quadraticChar (ZMod 5)) 3 = -1 :=
      (quadraticChar_neg_one_iff_not_isSquare).mpr hns
    simp [chiC, MulChar.ringHomComp_apply, hq]
  -- additive character values
  have e0 : ψ₅ (0 : ZMod 5) = 1 := by simp [ψ₅]
  have e1 : ψ₅ (1 : ZMod 5) = ζ := by
    rw [ψ₅, AddChar.zmodChar_apply, show ZMod.val (1 : ZMod 5) = 1 from by decide, pow_one]
  have e2 : ψ₅ (2 : ZMod 5) = ζ ^ 2 := by
    rw [ψ₅, AddChar.zmodChar_apply, show ZMod.val (2 : ZMod 5) = 2 from by decide]
  have e3 : ψ₅ (3 : ZMod 5) = ζ ^ 3 := by
    rw [ψ₅, AddChar.zmodChar_apply, show ZMod.val (3 : ZMod 5) = 3 from by decide]
  have e4 : ψ₅ (4 : ZMod 5) = ζ ^ 4 := by
    rw [ψ₅, AddChar.zmodChar_apply, show ZMod.val (4 : ZMod 5) = 4 from by decide]
  rw [h0, h1, h2, h3, h4, e0, e1, e2, e3, e4]
  ring

/-! ### Folding the redundant cosines -/

theorem cos_six_pi_div_five : Real.cos (6 * π / 5) = Real.cos (4 * π / 5) := by
  -- `Real.cos_add_pi` is stated as `cos (x + π) = -cos x`; fold both angles to `-cos(π/5)`.
  have h6 : (6 * π / 5 : ℝ) = π / 5 + π := by ring
  have h4 : (4 * π / 5 : ℝ) = π - π / 5 := by ring
  rw [h6, h4, Real.cos_add_pi, Real.cos_pi_sub]

theorem cos_eight_pi_div_five : Real.cos (8 * π / 5) = Real.cos (2 * π / 5) := by
  -- both angles fold to `-cos(3π/5)`.
  have h8 : (8 * π / 5 : ℝ) = 3 * π / 5 + π := by ring
  have h2 : (2 * π / 5 : ℝ) = π - 3 * π / 5 := by ring
  rw [h8, h2, Real.cos_add_pi, Real.cos_pi_sub]

/-! ### The real part of the Gauss sum -/

/-- The Gauss sum for `p = 5` is real with `Re g = 2·cos(2π/5) - 2·cos(4π/5)`. -/
theorem gaussSum_five_re :
    (gaussSum (chiC 5) ψ₅).re = 2 * Real.cos (2 * π / 5) - 2 * Real.cos (4 * π / 5) := by
  rw [gaussSum_five_eq]
  have hz1 : ζ = Complex.exp ((↑(2 * π / 5) : ℂ) * Complex.I) := by
    rw [ζ]; congr 1; push_cast; ring
  have hz2 : ζ ^ 2 = Complex.exp ((↑(4 * π / 5) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz3 : ζ ^ 3 = Complex.exp ((↑(6 * π / 5) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz4 : ζ ^ 4 = Complex.exp ((↑(8 * π / 5) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- resolve the higher powers first so `hz1` does not fire inside `ζ^k`
  rw [hz4, hz3, hz2, hz1]
  simp only [Complex.add_re, Complex.sub_re, Complex.exp_ofReal_mul_I_re]
  rw [cos_six_pi_div_five, cos_eight_pi_div_five]
  ring

/-! ### Positivity of the real part, hence the sign theorem for `p = 5` -/

/-- The open positivity crux `0 < Re g`, verified in the base case `p = 5`. -/
theorem gaussSum_five_re_pos : 0 < (gaussSum (chiC 5) ψ₅).re := by
  rw [gaussSum_five_re]
  have hcos2 : 0 < Real.cos (2 * π / 5) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcos4 : Real.cos (4 * π / 5) < 0 := by
    have h4 : (4 * π / 5 : ℝ) = π - π / 5 := by ring
    rw [h4, Real.cos_pi_sub]
    have : 0 < Real.cos (π / 5) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    linarith
  linarith

/-- **Gauss's hard sign theorem, base case `p = 5`.** For the standard additive character
`ψ₅(x) = exp(2πi/5)^x`, the quadratic Gauss sum equals exactly `+√5` (not `-√5`).  This is
the first sign *determination* for the `p ≡ 1 (mod 4)` branch — earlier work only reduced
the theorem to the positivity `0 < Re g`, which is confirmed here. -/
theorem gaussSum_five_eq_sqrt_five :
    gaussSum (chiC 5) ψ₅ = (Real.sqrt 5 : ℂ) := by
  have hp4 : (5 : ℕ) % 4 = 1 := by norm_num
  exact (gaussSum_eq_sqrt_iff_re_pos hp4 ψ₅_isPrimitive).mpr gaussSum_five_re_pos

end QuadraticGaussSumSignSmallFive
