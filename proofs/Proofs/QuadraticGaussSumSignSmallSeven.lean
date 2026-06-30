/-
  A concrete small-prime witness for Gauss's hard sign theorem: the prime `p = 7`.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, the quadratic Gauss sum `g = gaussSum (chiC p) ψ` is pinned by the
  elementary dichotomy + magnitude (see `QuadraticGaussSumSignReduction`) to one of four
  points: `±√p` for `p ≡ 1 (mod 4)`, or `±i√p` for `p ≡ 3 (mod 4)`.  Gauss's *hard* sign
  theorem fixes the leading sign,
      g = √p     (p ≡ 1 mod 4),     g = i·√p   (p ≡ 3 mod 4).
  The general positivity `0 < Re g` / `0 < Im g` is open and needs heavy DFT/theta
  infrastructure absent from Mathlib.

  The companion files settle the smallest cases of each residue class: `p = 3`
  (`QuadraticGaussSumSignSmall`, confirming `0 < Im g`) and `p = 5`
  (`QuadraticGaussSumSignSmallFive`, confirming `0 < Re g`).  This file adds the next
  witness on the `p ≡ 3 (mod 4)` branch, `p = 7`, a further confirmation of the open
  crux `0 < Im g`.

  Method (sign estimate, not exact trig).  For the standard character `ψ(x) = ζ^x` with
  `ζ = exp(2πi/7)`, the values of `quadraticChar (ZMod 7)` are `0, 1, 1, -1, 1, -1, -1`
  at `0,1,2,3,4,5,6` (the quadratic residues mod 7 are `1, 2, 4`), so the seven-term sum
  collapses to

      g = ζ + ζ² - ζ³ + ζ⁴ - ζ⁵ - ζ⁶.

  Taking imaginary parts and folding `sin(8π/7) = -sin(6π/7)`, `sin(10π/7) = -sin(4π/7)`,
  `sin(12π/7) = -sin(2π/7)` gives

      Im g = 2·sin(2π/7) + 2·sin(4π/7) - 2·sin(6π/7).

  As in the `p = 5` case we do NOT need exact radical values: positivity follows from the
  coarse facts `sin(2π/7) > 0` and `sin(4π/7) > sin(6π/7)` (both angles fold to `(0, π/2)`
  where `sin` is strictly monotone, and `4π/7 ↦ 3π/7 > π/7 ↤ 6π/7`).  Combined with the
  four-point pinning `g = ±i√7`, this forces `g = +i√7`.

  Sorry-free and axiom-free.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare
import Proofs.QuadraticGaussSumSignReduction

open scoped BigOperators Real
open Complex QuadraticGaussSumSquare QuadraticGaussSumSignReduction

namespace QuadraticGaussSumSignSmallSeven

/-- `7` is prime; needed for `chiC 7` and the Gauss-sum machinery. -/
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The standard primitive seventh root of unity `ζ = exp(2πi/7)`. -/
noncomputable def ζ : ℂ := Complex.exp (2 * π * Complex.I / 7)

theorem ζ_pow_seven : ζ ^ 7 = 1 := by
  have h : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / 7)) 7 :=
    Complex.isPrimitiveRoot_exp 7 (by norm_num)
  simpa [ζ] using h.pow_eq_one

/-- The standard additive character of `ZMod 7` valued in `ℂ`, `ψ(x) = ζ^x`. -/
noncomputable def ψ₇ : AddChar (ZMod 7) ℂ := AddChar.zmodChar 7 ζ_pow_seven

theorem ψ₇_isPrimitive : ψ₇.IsPrimitive := by
  have hroot : IsPrimitiveRoot ζ 7 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 7 (by norm_num)
  exact AddChar.zmodChar_primitive_of_primitive_root 7 hroot

/-! ### The Gauss sum for `p = 7` collapses to `ζ + ζ² - ζ³ + ζ⁴ - ζ⁵ - ζ⁶` -/

/-- `chiC 7` takes values `0, 1, 1, -1, 1, -1, -1` at `0, 1, 2, 3, 4, 5, 6` (residues
`1, 2, 4`), so the seven-term Gauss sum is `ζ + ζ² - ζ³ + ζ⁴ - ζ⁵ - ζ⁶`. -/
theorem gaussSum_seven_eq :
    gaussSum (chiC 7) ψ₇ = ζ + ζ ^ 2 - ζ ^ 3 + ζ ^ 4 - ζ ^ 5 - ζ ^ 6 := by
  have huniv : (Finset.univ : Finset (ZMod 7)) = {0, 1, 2, 3, 4, 5, 6} := by decide
  rw [gaussSum, huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  -- character values (residues mod 7 are 1, 2, 4)
  have h0 : chiC 7 (0 : ZMod 7) = 0 := by simp [chiC]
  have h1 : chiC 7 (1 : ZMod 7) = 1 := by simp
  have h2 : chiC 7 (2 : ZMod 7) = 1 := by
    have hsq : IsSquare (2 : ZMod 7) := by decide
    have hq : (quadraticChar (ZMod 7)) 2 = 1 :=
      (quadraticChar_one_iff_isSquare (by decide)).mpr hsq
    simp [chiC, MulChar.ringHomComp_apply, hq]
  have h3 : chiC 7 (3 : ZMod 7) = -1 := by
    have hns : ¬ IsSquare (3 : ZMod 7) := by decide
    have hq : (quadraticChar (ZMod 7)) 3 = -1 :=
      (quadraticChar_neg_one_iff_not_isSquare).mpr hns
    simp [chiC, MulChar.ringHomComp_apply, hq]
  have h4 : chiC 7 (4 : ZMod 7) = 1 := by
    have hsq : IsSquare (4 : ZMod 7) := by decide
    have hq : (quadraticChar (ZMod 7)) 4 = 1 :=
      (quadraticChar_one_iff_isSquare (by decide)).mpr hsq
    simp [chiC, MulChar.ringHomComp_apply, hq]
  have h5 : chiC 7 (5 : ZMod 7) = -1 := by
    have hns : ¬ IsSquare (5 : ZMod 7) := by decide
    have hq : (quadraticChar (ZMod 7)) 5 = -1 :=
      (quadraticChar_neg_one_iff_not_isSquare).mpr hns
    simp [chiC, MulChar.ringHomComp_apply, hq]
  have h6 : chiC 7 (6 : ZMod 7) = -1 := by
    have hns : ¬ IsSquare (6 : ZMod 7) := by decide
    have hq : (quadraticChar (ZMod 7)) 6 = -1 :=
      (quadraticChar_neg_one_iff_not_isSquare).mpr hns
    simp [chiC, MulChar.ringHomComp_apply, hq]
  -- additive character values
  have e0 : ψ₇ (0 : ZMod 7) = 1 := by simp [ψ₇]
  have e1 : ψ₇ (1 : ZMod 7) = ζ := by
    rw [ψ₇, AddChar.zmodChar_apply, show ZMod.val (1 : ZMod 7) = 1 from by decide, pow_one]
  have e2 : ψ₇ (2 : ZMod 7) = ζ ^ 2 := by
    rw [ψ₇, AddChar.zmodChar_apply, show ZMod.val (2 : ZMod 7) = 2 from by decide]
  have e3 : ψ₇ (3 : ZMod 7) = ζ ^ 3 := by
    rw [ψ₇, AddChar.zmodChar_apply, show ZMod.val (3 : ZMod 7) = 3 from by decide]
  have e4 : ψ₇ (4 : ZMod 7) = ζ ^ 4 := by
    rw [ψ₇, AddChar.zmodChar_apply, show ZMod.val (4 : ZMod 7) = 4 from by decide]
  have e5 : ψ₇ (5 : ZMod 7) = ζ ^ 5 := by
    rw [ψ₇, AddChar.zmodChar_apply, show ZMod.val (5 : ZMod 7) = 5 from by decide]
  have e6 : ψ₇ (6 : ZMod 7) = ζ ^ 6 := by
    rw [ψ₇, AddChar.zmodChar_apply, show ZMod.val (6 : ZMod 7) = 6 from by decide]
  rw [h0, h1, h2, h3, h4, h5, h6, e0, e1, e2, e3, e4, e5, e6]
  ring

/-! ### Folding the redundant sines into `sin(2π/7), sin(4π/7), sin(6π/7)` -/

theorem sin_eight_pi_div_seven : Real.sin (8 * π / 7) = - Real.sin (6 * π / 7) := by
  have h8 : (8 * π / 7 : ℝ) = π / 7 + π := by ring
  have h6 : (6 * π / 7 : ℝ) = π - π / 7 := by ring
  rw [h8, h6, Real.sin_add_pi, Real.sin_pi_sub]

theorem sin_ten_pi_div_seven : Real.sin (10 * π / 7) = - Real.sin (4 * π / 7) := by
  have h10 : (10 * π / 7 : ℝ) = 3 * π / 7 + π := by ring
  have h4 : (4 * π / 7 : ℝ) = π - 3 * π / 7 := by ring
  rw [h10, h4, Real.sin_add_pi, Real.sin_pi_sub]

theorem sin_twelve_pi_div_seven : Real.sin (12 * π / 7) = - Real.sin (2 * π / 7) := by
  have h12 : (12 * π / 7 : ℝ) = 5 * π / 7 + π := by ring
  have h2 : (2 * π / 7 : ℝ) = π - 5 * π / 7 := by ring
  rw [h12, h2, Real.sin_add_pi, Real.sin_pi_sub]

/-! ### The imaginary part of the Gauss sum -/

/-- The Gauss sum for `p = 7` is imaginary with
`Im g = 2·sin(2π/7) + 2·sin(4π/7) - 2·sin(6π/7)`. -/
theorem gaussSum_seven_im :
    (gaussSum (chiC 7) ψ₇).im =
      2 * Real.sin (2 * π / 7) + 2 * Real.sin (4 * π / 7) - 2 * Real.sin (6 * π / 7) := by
  rw [gaussSum_seven_eq]
  have hz1 : ζ = Complex.exp ((↑(2 * π / 7) : ℂ) * Complex.I) := by
    rw [ζ]; congr 1; push_cast; ring
  have hz2 : ζ ^ 2 = Complex.exp ((↑(4 * π / 7) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz3 : ζ ^ 3 = Complex.exp ((↑(6 * π / 7) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz4 : ζ ^ 4 = Complex.exp ((↑(8 * π / 7) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz5 : ζ ^ 5 = Complex.exp ((↑(10 * π / 7) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz6 : ζ ^ 6 = Complex.exp ((↑(12 * π / 7) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- resolve the higher powers first so `hz1` does not fire inside `ζ^k`
  rw [hz6, hz5, hz4, hz3, hz2, hz1]
  simp only [Complex.add_im, Complex.sub_im, Complex.exp_ofReal_mul_I_im]
  rw [sin_eight_pi_div_seven, sin_ten_pi_div_seven, sin_twelve_pi_div_seven]
  ring

/-! ### Positivity of the imaginary part, hence the sign theorem for `p = 7` -/

/-- The open positivity crux `0 < Im g`, verified in the base case `p = 7`. -/
theorem gaussSum_seven_im_pos : 0 < (gaussSum (chiC 7) ψ₇).im := by
  rw [gaussSum_seven_im]
  -- `sin(2π/7) > 0`: angle in `(0, π)`.
  have hsin2 : 0 < Real.sin (2 * π / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  -- `sin(4π/7) > sin(6π/7)`: fold both to `(0, π/2)`, where `sin` is strictly monotone,
  -- via `sin(4π/7) = sin(3π/7)` and `sin(6π/7) = sin(π/7)`, then `π/7 < 3π/7`.
  have e4 : Real.sin (4 * π / 7) = Real.sin (3 * π / 7) := by
    have : (4 * π / 7 : ℝ) = π - 3 * π / 7 := by ring
    rw [this, Real.sin_pi_sub]
  have e6 : Real.sin (6 * π / 7) = Real.sin (π / 7) := by
    have : (6 * π / 7 : ℝ) = π - π / 7 := by ring
    rw [this, Real.sin_pi_sub]
  have hmono : Real.sin (π / 7) < Real.sin (3 * π / 7) := by
    apply Real.strictMonoOn_sin
    · constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    · constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have hsin46 : Real.sin (6 * π / 7) < Real.sin (4 * π / 7) := by
    rw [e4, e6]; exact hmono
  linarith

/-- **Gauss's hard sign theorem, witness `p = 7`.** For the standard additive character
`ψ₇(x) = exp(2πi/7)^x`, the quadratic Gauss sum equals exactly `+i·√7` (not `-i·√7`).
This is a second witness on the `p ≡ 3 (mod 4)` branch (after `p = 3`), confirming the
open positivity crux `0 < Im g`. -/
theorem gaussSum_seven_eq_I_sqrt_seven :
    gaussSum (chiC 7) ψ₇ = (Real.sqrt 7 : ℂ) * Complex.I := by
  have hp4 : (7 : ℕ) % 4 = 3 := by norm_num
  exact (gaussSum_eq_I_sqrt_iff_im_pos hp4 ψ₇_isPrimitive).mpr gaussSum_seven_im_pos

end QuadraticGaussSumSignSmallSeven
