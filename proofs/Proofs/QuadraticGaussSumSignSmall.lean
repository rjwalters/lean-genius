/-
  A concrete small-prime witness for Gauss's hard sign theorem.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, the quadratic Gauss sum `g = gaussSum (chiC p) ψ` is pinned by
  the elementary dichotomy + magnitude (see `QuadraticGaussSumSignReduction`) to one
  of four points: `±√p` for `p ≡ 1 (mod 4)`, or `±i√p` for `p ≡ 3 (mod 4)`.  Gauss's
  *hard* sign theorem fixes the leading sign,
      g = √p     (p ≡ 1 mod 4),     g = i·√p   (p ≡ 3 mod 4),
  but only for the STANDARD additive character `ψ(x) = ζ_p^x` (for a general primitive
  `ψ_a(x) = ζ_p^{a x}` the sum is multiplied by the Legendre symbol `χ(a) = ±1`, which
  can flip the sign).  The general positivity `0 < Re g` / `0 < Im g` is open and needs
  heavy DFT/theta infrastructure absent from Mathlib.

  This file does NOT attempt the general theorem.  Instead it establishes the smallest
  case `p = 3` (≡ 3 mod 4) **by direct computation** for the standard character built
  from `ζ = exp(2πi/3)`:

      gaussSum (chiC 3) ψ  =  ζ - ζ²  =  i·√3.

  Concretely `quadraticChar (ZMod 3)` is `(0, 1, -1)` at `(0, 1, 2)`, so the three-term
  sum collapses to `ζ - ζ²`, and `ζ - ζ² = i·√3` is plain trigonometry
  (`sin(2π/3) - sin(4π/3) = √3`, `cos(2π/3) - cos(4π/3) = 0`).  This is the first actual
  sign *determination* for this entry (everything prior was a reduction), and it
  confirms `0 < Im g`, the open crux, in the base case.

  Sorry-free and axiom-free.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare

open scoped BigOperators Real
open Complex QuadraticGaussSumSquare

namespace QuadraticGaussSumSignSmall

/-- The standard primitive cube root of unity `ζ = exp(2πi/3)`. -/
noncomputable def ζ : ℂ := Complex.exp (2 * π * Complex.I / 3)

theorem ζ_pow_three : ζ ^ 3 = 1 := by
  have h : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [ζ] using h.pow_eq_one

/-- The standard additive character of `ZMod 3` valued in `ℂ`, `ψ(x) = ζ^x`. -/
noncomputable def ψ₃ : AddChar (ZMod 3) ℂ := AddChar.zmodChar 3 ζ_pow_three

theorem ψ₃_isPrimitive : ψ₃.IsPrimitive := by
  have hroot : IsPrimitiveRoot ζ 3 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 3 (by norm_num)
  exact AddChar.zmodChar_primitive_of_primitive_root 3 hroot

/-! ### Trigonometric values used in the evaluation -/

theorem cos_two_pi_div_three : Real.cos (2 * π / 3) = -(1 / 2) := by
  have : (2 * π / 3) = π - π / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem sin_two_pi_div_three : Real.sin (2 * π / 3) = √3 / 2 := by
  have : (2 * π / 3) = π - π / 3 := by ring
  rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem cos_four_pi_div_three : Real.cos (4 * π / 3) = -(1 / 2) := by
  have h : (4 * π / 3) = π + π / 3 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  ring

theorem sin_four_pi_div_three : Real.sin (4 * π / 3) = -(√3 / 2) := by
  have h : (4 * π / 3) = π + π / 3 := by ring
  rw [h, Real.sin_add, Real.cos_pi, Real.sin_pi, Real.sin_pi_div_three]
  ring

/-! ### The Gauss sum for `p = 3` collapses to `ζ - ζ²` -/

/-- `chiC 3` takes values `0, 1, -1` at `0, 1, 2`, so the three-term Gauss sum is
`ζ - ζ²`. -/
theorem gaussSum_three_eq : gaussSum (chiC 3) ψ₃ = ζ - ζ ^ 2 := by
  -- `Fin.sum_univ_three` does not fire directly: the sum is over `ZMod 3`, whose
  -- `Fintype` instance is not syntactically `Fin.fintype`.  Enumerate `univ` explicitly.
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [gaussSum, huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h0 : chiC 3 (0 : ZMod 3) = 0 := by
    simp [chiC]
  have h1 : chiC 3 (1 : ZMod 3) = 1 := by simp
  have h2 : chiC 3 (2 : ZMod 3) = -1 := by
    have h2neg : (2 : ZMod 3) = -1 := by decide
    rw [h2neg, chiC_neg_one (by norm_num)]
    norm_num
  have e0 : ψ₃ (0 : ZMod 3) = 1 := by
    simp [ψ₃]
  have e1 : ψ₃ (1 : ZMod 3) = ζ := by
    rw [ψ₃, AddChar.zmodChar_apply, show ZMod.val (1 : ZMod 3) = 1 from by decide, pow_one]
  have e2 : ψ₃ (2 : ZMod 3) = ζ ^ 2 := by
    rw [ψ₃, AddChar.zmodChar_apply, show ZMod.val (2 : ZMod 3) = 2 from by decide]
  rw [h0, h1, h2, e0, e1, e2]
  ring

/-! ### `ζ - ζ² = i·√3`, hence the sign theorem holds for `p = 3` -/

theorem zeta_sub_zeta_sq : ζ - ζ ^ 2 = (√3 : ℂ) * Complex.I := by
  have hz1 : ζ = Complex.exp ((↑(2 * π / 3) : ℂ) * Complex.I) := by
    rw [ζ]; congr 1; push_cast; ring
  have hz2 : ζ ^ 2 = Complex.exp ((↑(4 * π / 3) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- Resolve the power FIRST (rw hz2), then ζ (rw hz1); doing both inside a single
  -- `simp only` would let `hz1` fire inside `ζ^2` before `hz2` can match.
  rw [hz2, hz1]
  apply Complex.ext
  · -- real part: cos(2π/3) - cos(4π/3) = 0
    simp only [Complex.sub_re, Complex.exp_ofReal_mul_I_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    rw [cos_two_pi_div_three, cos_four_pi_div_three]
    ring
  · -- imaginary part: sin(2π/3) - sin(4π/3) = √3
    simp only [Complex.sub_im, Complex.exp_ofReal_mul_I_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    rw [sin_two_pi_div_three, sin_four_pi_div_three]
    ring

/-- **Gauss's hard sign theorem, base case `p = 3`.** For the standard additive
character `ψ₃(x) = exp(2πi/3)^x`, the quadratic Gauss sum equals exactly `i·√3`
(not `-i·√3`).  This is the first sign *determination* for this entry — earlier work
only reduced the theorem to the positivity `0 < Im g`, which is confirmed here. -/
theorem gaussSum_three_eq_I_sqrt_three :
    gaussSum (chiC 3) ψ₃ = (√3 : ℂ) * Complex.I := by
  rw [gaussSum_three_eq, zeta_sub_zeta_sq]

/-- The open positivity crux `0 < Im g`, verified in the base case `p = 3`. -/
theorem gaussSum_three_im_pos : 0 < (gaussSum (chiC 3) ψ₃).im := by
  rw [gaussSum_three_eq_I_sqrt_three]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
  positivity

end QuadraticGaussSumSignSmall
