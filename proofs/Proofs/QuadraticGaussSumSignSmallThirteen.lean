/-
  A concrete small-prime witness for Gauss's hard sign theorem: the prime `p = 13`.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, the quadratic Gauss sum `g = gaussSum (chiC p) ψ` is pinned by the
  elementary dichotomy + magnitude (see `QuadraticGaussSumSignReduction`) to one of four
  points: `±√p` for `p ≡ 1 (mod 4)`, or `±i√p` for `p ≡ 3 (mod 4)`.  Gauss's *hard* sign
  theorem fixes the leading sign,
      g = √p     (p ≡ 1 mod 4),     g = i·√p   (p ≡ 3 mod 4).
  The general positivity `0 < Re g` / `0 < Im g` is open and needs heavy DFT/theta
  infrastructure absent from Mathlib.

  The companion files settle `p = 3, 5, 7, 11`.  This file adds the SECOND witness on the
  `p ≡ 1 (mod 4)` branch, `p = 13` (after `p = 5`), a further confirmation of the open
  crux `0 < Re g`.

  Method (sign estimate, not exact trig).  For the standard character `ψ(x) = ζ^x` with
  `ζ = exp(2πi/13)`, the quadratic residues mod 13 are `{1,3,4,9,10,12}`, so the
  thirteen-term sum collapses to

      g = ζ - ζ² + ζ³ + ζ⁴ - ζ⁵ - ζ⁶ - ζ⁷ - ζ⁸ + ζ⁹ + ζ¹⁰ - ζ¹¹ + ζ¹².

  Taking real parts and folding the conjugate pairs `cos(2π·k/13) = cos(2π·(13−k)/13)`
  gives

      Re g = 2·cos(2π/13) - 2·cos(4π/13) + 2·cos(6π/13)
             + 2·cos(8π/13) - 2·cos(10π/13) - 2·cos(12π/13).

  As in the smaller cases we do NOT need exact radical values.  Rewriting the three obtuse
  cosines `cos(8π/13) = -cos(5π/13)`, `cos(10π/13) = -cos(3π/13)`, `cos(12π/13) = -cos(π/13)`
  turns this into

      Re g / 2 = [cos(π/13) + cos(2π/13) + cos(3π/13) + cos(6π/13)]
                 - [cos(4π/13) + cos(5π/13)],

  all six angles lying in `(0, π/2)` where `cos` is positive and strictly decreasing.
  Positivity then follows from `cos(π/13) > cos(4π/13)`, `cos(2π/13) > cos(5π/13)`
  (strict anti-monotonicity) and `cos(3π/13), cos(6π/13) > 0`.  Combined with the
  four-point pinning `g = ±√13`, this forces `g = +√13`.

  Sorry-free and axiom-free.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare
import Proofs.QuadraticGaussSumSignReduction

open scoped BigOperators Real
open Complex QuadraticGaussSumSquare QuadraticGaussSumSignReduction

namespace QuadraticGaussSumSignSmallThirteen

/-- `13` is prime; needed for `chiC 13` and the Gauss-sum machinery. -/
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The standard primitive thirteenth root of unity `ζ = exp(2πi/13)`. -/
noncomputable def ζ : ℂ := Complex.exp (2 * π * Complex.I / 13)

theorem ζ_pow_thirteen : ζ ^ 13 = 1 := by
  have h : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / 13)) 13 :=
    Complex.isPrimitiveRoot_exp 13 (by norm_num)
  simpa [ζ] using h.pow_eq_one

/-- The standard additive character of `ZMod 13` valued in `ℂ`, `ψ(x) = ζ^x`. -/
noncomputable def ψ₁₃ : AddChar (ZMod 13) ℂ := AddChar.zmodChar 13 ζ_pow_thirteen

theorem ψ₁₃_isPrimitive : ψ₁₃.IsPrimitive := by
  have hroot : IsPrimitiveRoot ζ 13 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 13 (by norm_num)
  exact AddChar.zmodChar_primitive_of_primitive_root 13 hroot

/-! ### The Gauss sum for `p = 13` collapses to the residue pattern -/

/-- `chiC 13` realises the quadratic residues `{1,3,4,9,10,12}` (value `+1`) and
non-residues `{2,5,6,7,8,11}` (value `-1`), so the thirteen-term Gauss sum is
`ζ - ζ² + ζ³ + ζ⁴ - ζ⁵ - ζ⁶ - ζ⁷ - ζ⁸ + ζ⁹ + ζ¹⁰ - ζ¹¹ + ζ¹²`. -/
theorem gaussSum_thirteen_eq :
    gaussSum (chiC 13) ψ₁₃ =
      ζ - ζ ^ 2 + ζ ^ 3 + ζ ^ 4 - ζ ^ 5 - ζ ^ 6 - ζ ^ 7 - ζ ^ 8
        + ζ ^ 9 + ζ ^ 10 - ζ ^ 11 + ζ ^ 12 := by
  have huniv : (Finset.univ : Finset (ZMod 13)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  rw [gaussSum, huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  -- character values (residues mod 13 are 1,3,4,9,10,12)
  have h0 : chiC 13 (0 : ZMod 13) = 0 := by simp [chiC]
  have h1 : chiC 13 (1 : ZMod 13) = 1 := by simp
  have hQR : ∀ k : ZMod 13, k ≠ 0 → IsSquare k → chiC 13 k = 1 := by
    intro k hk hsq
    have hq : (quadraticChar (ZMod 13)) k = 1 :=
      (quadraticChar_one_iff_isSquare hk).mpr hsq
    simp [chiC, MulChar.ringHomComp_apply, hq]
  have hNR : ∀ k : ZMod 13, ¬ IsSquare k → chiC 13 k = -1 := by
    intro k hns
    have hq : (quadraticChar (ZMod 13)) k = -1 :=
      (quadraticChar_neg_one_iff_not_isSquare).mpr hns
    simp [chiC, MulChar.ringHomComp_apply, hq]
  have h2 : chiC 13 (2 : ZMod 13) = -1 := hNR 2 (by decide)
  have h3 : chiC 13 (3 : ZMod 13) = 1 := hQR 3 (by decide) (by decide)
  have h4 : chiC 13 (4 : ZMod 13) = 1 := hQR 4 (by decide) (by decide)
  have h5 : chiC 13 (5 : ZMod 13) = -1 := hNR 5 (by decide)
  have h6 : chiC 13 (6 : ZMod 13) = -1 := hNR 6 (by decide)
  have h7 : chiC 13 (7 : ZMod 13) = -1 := hNR 7 (by decide)
  have h8 : chiC 13 (8 : ZMod 13) = -1 := hNR 8 (by decide)
  have h9 : chiC 13 (9 : ZMod 13) = 1 := hQR 9 (by decide) (by decide)
  have h10 : chiC 13 (10 : ZMod 13) = 1 := hQR 10 (by decide) (by decide)
  have h11 : chiC 13 (11 : ZMod 13) = -1 := hNR 11 (by decide)
  have h12 : chiC 13 (12 : ZMod 13) = 1 := hQR 12 (by decide) (by decide)
  -- additive character values
  have e0 : ψ₁₃ (0 : ZMod 13) = 1 := by simp [ψ₁₃]
  have e1 : ψ₁₃ (1 : ZMod 13) = ζ := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (1 : ZMod 13) = 1 from by decide, pow_one]
  have e2 : ψ₁₃ (2 : ZMod 13) = ζ ^ 2 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (2 : ZMod 13) = 2 from by decide]
  have e3 : ψ₁₃ (3 : ZMod 13) = ζ ^ 3 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (3 : ZMod 13) = 3 from by decide]
  have e4 : ψ₁₃ (4 : ZMod 13) = ζ ^ 4 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (4 : ZMod 13) = 4 from by decide]
  have e5 : ψ₁₃ (5 : ZMod 13) = ζ ^ 5 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (5 : ZMod 13) = 5 from by decide]
  have e6 : ψ₁₃ (6 : ZMod 13) = ζ ^ 6 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (6 : ZMod 13) = 6 from by decide]
  have e7 : ψ₁₃ (7 : ZMod 13) = ζ ^ 7 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (7 : ZMod 13) = 7 from by decide]
  have e8 : ψ₁₃ (8 : ZMod 13) = ζ ^ 8 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (8 : ZMod 13) = 8 from by decide]
  have e9 : ψ₁₃ (9 : ZMod 13) = ζ ^ 9 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (9 : ZMod 13) = 9 from by decide]
  have e10 : ψ₁₃ (10 : ZMod 13) = ζ ^ 10 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (10 : ZMod 13) = 10 from by decide]
  have e11 : ψ₁₃ (11 : ZMod 13) = ζ ^ 11 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (11 : ZMod 13) = 11 from by decide]
  have e12 : ψ₁₃ (12 : ZMod 13) = ζ ^ 12 := by
    rw [ψ₁₃, AddChar.zmodChar_apply, show ZMod.val (12 : ZMod 13) = 12 from by decide]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  ring

/-! ### Folding the conjugate cosines `cos(2π·k/13) = cos(2π·(13−k)/13)` -/

theorem cos_fourteen : Real.cos (14 * π / 13) = Real.cos (12 * π / 13) := by
  have ha : (14 * π / 13 : ℝ) = π / 13 + π := by ring
  have hb : (12 * π / 13 : ℝ) = π - π / 13 := by ring
  rw [ha, hb, Real.cos_add_pi, Real.cos_pi_sub]

theorem cos_sixteen : Real.cos (16 * π / 13) = Real.cos (10 * π / 13) := by
  have ha : (16 * π / 13 : ℝ) = 3 * π / 13 + π := by ring
  have hb : (10 * π / 13 : ℝ) = π - 3 * π / 13 := by ring
  rw [ha, hb, Real.cos_add_pi, Real.cos_pi_sub]

theorem cos_eighteen : Real.cos (18 * π / 13) = Real.cos (8 * π / 13) := by
  have ha : (18 * π / 13 : ℝ) = 5 * π / 13 + π := by ring
  have hb : (8 * π / 13 : ℝ) = π - 5 * π / 13 := by ring
  rw [ha, hb, Real.cos_add_pi, Real.cos_pi_sub]

theorem cos_twenty : Real.cos (20 * π / 13) = Real.cos (6 * π / 13) := by
  have ha : (20 * π / 13 : ℝ) = 7 * π / 13 + π := by ring
  have hb : (6 * π / 13 : ℝ) = π - 7 * π / 13 := by ring
  rw [ha, hb, Real.cos_add_pi, Real.cos_pi_sub]

theorem cos_twentytwo : Real.cos (22 * π / 13) = Real.cos (4 * π / 13) := by
  have ha : (22 * π / 13 : ℝ) = 9 * π / 13 + π := by ring
  have hb : (4 * π / 13 : ℝ) = π - 9 * π / 13 := by ring
  rw [ha, hb, Real.cos_add_pi, Real.cos_pi_sub]

theorem cos_twentyfour : Real.cos (24 * π / 13) = Real.cos (2 * π / 13) := by
  have ha : (24 * π / 13 : ℝ) = 11 * π / 13 + π := by ring
  have hb : (2 * π / 13 : ℝ) = π - 11 * π / 13 := by ring
  rw [ha, hb, Real.cos_add_pi, Real.cos_pi_sub]

/-! ### The real part of the Gauss sum -/

/-- The Gauss sum for `p = 13` is real with
`Re g = 2·cos(2π/13) - 2·cos(4π/13) + 2·cos(6π/13) + 2·cos(8π/13) - 2·cos(10π/13)
        - 2·cos(12π/13)`. -/
theorem gaussSum_thirteen_re :
    (gaussSum (chiC 13) ψ₁₃).re =
      2 * Real.cos (2 * π / 13) - 2 * Real.cos (4 * π / 13) + 2 * Real.cos (6 * π / 13)
        + 2 * Real.cos (8 * π / 13) - 2 * Real.cos (10 * π / 13)
        - 2 * Real.cos (12 * π / 13) := by
  rw [gaussSum_thirteen_eq]
  have hz1 : ζ = Complex.exp ((↑(2 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ]; congr 1; push_cast; ring
  have hz2 : ζ ^ 2 = Complex.exp ((↑(4 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz3 : ζ ^ 3 = Complex.exp ((↑(6 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz4 : ζ ^ 4 = Complex.exp ((↑(8 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz5 : ζ ^ 5 = Complex.exp ((↑(10 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz6 : ζ ^ 6 = Complex.exp ((↑(12 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz7 : ζ ^ 7 = Complex.exp ((↑(14 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz8 : ζ ^ 8 = Complex.exp ((↑(16 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz9 : ζ ^ 9 = Complex.exp ((↑(18 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz10 : ζ ^ 10 = Complex.exp ((↑(20 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz11 : ζ ^ 11 = Complex.exp ((↑(22 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz12 : ζ ^ 12 = Complex.exp ((↑(24 * π / 13) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- resolve the higher powers first so `hz1` does not fire inside `ζ^k`
  rw [hz12, hz11, hz10, hz9, hz8, hz7, hz6, hz5, hz4, hz3, hz2, hz1]
  simp only [Complex.add_re, Complex.sub_re, Complex.exp_ofReal_mul_I_re]
  rw [cos_fourteen, cos_sixteen, cos_eighteen, cos_twenty, cos_twentytwo, cos_twentyfour]
  ring

/-! ### Positivity of the real part, hence the sign theorem for `p = 13` -/

/-- The open positivity crux `0 < Re g`, verified in the case `p = 13`. -/
theorem gaussSum_thirteen_re_pos : 0 < (gaussSum (chiC 13) ψ₁₃).re := by
  rw [gaussSum_thirteen_re]
  -- rewrite the three obtuse cosines as negatives of acute ones
  have e8 : Real.cos (8 * π / 13) = - Real.cos (5 * π / 13) := by
    have : (8 * π / 13 : ℝ) = π - 5 * π / 13 := by ring
    rw [this, Real.cos_pi_sub]
  have e10 : Real.cos (10 * π / 13) = - Real.cos (3 * π / 13) := by
    have : (10 * π / 13 : ℝ) = π - 3 * π / 13 := by ring
    rw [this, Real.cos_pi_sub]
  have e12 : Real.cos (12 * π / 13) = - Real.cos (π / 13) := by
    have : (12 * π / 13 : ℝ) = π - π / 13 := by ring
    rw [this, Real.cos_pi_sub]
  -- the two acute cosines that survive with a positive coefficient
  have pos3 : 0 < Real.cos (3 * π / 13) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have pos6 : 0 < Real.cos (6 * π / 13) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- strict anti-monotonicity of `cos` on `[0, π]` dominates the two negative terms
  have m1 : (π / 13 : ℝ) ∈ Set.Icc 0 π := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have m2 : (2 * π / 13 : ℝ) ∈ Set.Icc 0 π :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have m4 : (4 * π / 13 : ℝ) ∈ Set.Icc 0 π :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have m5 : (5 * π / 13 : ℝ) ∈ Set.Icc 0 π :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcmp1 : Real.cos (4 * π / 13) < Real.cos (π / 13) :=
    Real.strictAntiOn_cos m1 m4 (by linarith [Real.pi_pos])
  have hcmp2 : Real.cos (5 * π / 13) < Real.cos (2 * π / 13) :=
    Real.strictAntiOn_cos m2 m5 (by linarith [Real.pi_pos])
  rw [e8, e10, e12]
  linarith [hcmp1, hcmp2, pos3, pos6]

/-- **Gauss's hard sign theorem, witness `p = 13`.** For the standard additive character
`ψ₁₃(x) = exp(2πi/13)^x`, the quadratic Gauss sum equals exactly `+√13` (not `-√13`).
This is the second sign *determination* on the `p ≡ 1 (mod 4)` branch (after `p = 5`),
confirming the open positivity crux `0 < Re g`. -/
theorem gaussSum_thirteen_eq_sqrt_thirteen :
    gaussSum (chiC 13) ψ₁₃ = (Real.sqrt 13 : ℂ) := by
  have hp4 : (13 : ℕ) % 4 = 1 := by norm_num
  exact (gaussSum_eq_sqrt_iff_re_pos hp4 ψ₁₃_isPrimitive).mpr gaussSum_thirteen_re_pos

end QuadraticGaussSumSignSmallThirteen
