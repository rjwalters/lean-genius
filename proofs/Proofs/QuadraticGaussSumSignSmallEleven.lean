/-
  A concrete small-prime witness for Gauss's hard sign theorem: the prime `p = 11`.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, the quadratic Gauss sum `g = gaussSum (chiC p) ψ` is pinned by the
  elementary dichotomy + magnitude (see `QuadraticGaussSumSignReduction`) to one of four
  points: `±√p` for `p ≡ 1 (mod 4)`, or `±i√p` for `p ≡ 3 (mod 4)`.  Gauss's *hard* sign
  theorem fixes the leading sign,
      g = √p     (p ≡ 1 mod 4),     g = i·√p   (p ≡ 3 mod 4).
  The general positivity `0 < Re g` / `0 < Im g` is open and needs heavy DFT/theta
  infrastructure absent from Mathlib.

  Earlier companion files settle the smallest cases by direct computation: `p = 3` and
  `p = 7` on the `p ≡ 3 (mod 4)` branch, and `p = 5` on the `p ≡ 1 (mod 4)` branch.  This
  file adds the next `p ≡ 3 (mod 4)` witness, `p = 11`, determining the leading sign

      gaussSum (chiC 11) ψ₁₁ = +i·√11   (not −i·√11).

  Method (coarse sign estimate, not exact radicals).  For the standard character
  `ψ(x) = ζ^x` with `ζ = exp(2πi/11)`, the quadratic residues mod `11` are `{1,3,4,5,9}`,
  so `chiC 11 = (0,1,-1,1,1,1,-1,-1,-1,1,-1)` and the eleven-term sum collapses to

      g = ζ - ζ² + ζ³ + ζ⁴ + ζ⁵ - ζ⁶ - ζ⁷ - ζ⁸ + ζ⁹ - ζ¹⁰.

  Folding the upper-half sines (`sin(2π(11-k)/11) = -sin(2πk/11)`, together with the
  sign flips `chiC(11-k) = -chiC(k)` valid since `11 ≡ 3 mod 4`) gives

      Im g = 2·sin(2π/11) - 2·sin(4π/11) + 2·sin(6π/11) + 2·sin(8π/11) + 2·sin(10π/11).

  Positivity follows from **coarse sign facts only** — no exact value like `cos(2π/11)`
  (a cubic irrational) is needed.  The three sines `sin(2π/11), sin(8π/11), sin(10π/11)`
  are positive (angles in `(0, π)`), and the lone negative term `-sin(4π/11)` is dominated
  by `sin(6π/11) = sin(5π/11) > sin(4π/11)` (both `5π/11, 4π/11 ∈ (0, π/2)`, where `sin`
  is strictly increasing).  Feeding `0 < Im g` into the reduction lemma
  `gaussSum_eq_I_sqrt_iff_im_pos` (with `11 % 4 = 3`) forces `g = +i√11`.

  Sorry-free and axiom-free.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare
import Proofs.QuadraticGaussSumSignReduction

open scoped BigOperators Real
open Complex QuadraticGaussSumSquare QuadraticGaussSumSignReduction

namespace QuadraticGaussSumSignSmallEleven

/-- `11` is prime; needed for `chiC 11` and the Gauss-sum machinery. -/
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The standard primitive eleventh root of unity `ζ = exp(2πi/11)`. -/
noncomputable def ζ : ℂ := Complex.exp (2 * π * Complex.I / 11)

theorem ζ_pow_eleven : ζ ^ 11 = 1 := by
  have h : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / 11)) 11 :=
    Complex.isPrimitiveRoot_exp 11 (by norm_num)
  simpa [ζ] using h.pow_eq_one

/-- The standard additive character of `ZMod 11` valued in `ℂ`, `ψ(x) = ζ^x`. -/
noncomputable def ψ₁₁ : AddChar (ZMod 11) ℂ := AddChar.zmodChar 11 ζ_pow_eleven

theorem ψ₁₁_isPrimitive : ψ₁₁.IsPrimitive := by
  have hroot : IsPrimitiveRoot ζ 11 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 11 (by norm_num)
  exact AddChar.zmodChar_primitive_of_primitive_root 11 hroot

/-! ### The Gauss sum for `p = 11` collapses to an explicit `ζ`-polynomial -/

/-- `chiC 11` takes the quadratic-residue pattern `(0,1,-1,1,1,1,-1,-1,-1,1,-1)`, so the
eleven-term Gauss sum is `ζ - ζ² + ζ³ + ζ⁴ + ζ⁵ - ζ⁶ - ζ⁷ - ζ⁸ + ζ⁹ - ζ¹⁰`. -/
theorem gaussSum_eleven_eq :
    gaussSum (chiC 11) ψ₁₁ =
      ζ - ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 - ζ ^ 6 - ζ ^ 7 - ζ ^ 8 + ζ ^ 9 - ζ ^ 10 := by
  have huniv : (Finset.univ : Finset (ZMod 11)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by
    decide
  rw [gaussSum, huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  -- character values (quadratic residues mod 11 are {1,3,4,5,9})
  have h0 : chiC 11 (0 : ZMod 11) = 0 := by simp [chiC]
  have h1 : chiC 11 (1 : ZMod 11) = 1 := by simp
  have hsq : ∀ k : ZMod 11, (quadraticChar (ZMod 11)) k = 1 → chiC 11 k = 1 := by
    intro k hk; simp [chiC, MulChar.ringHomComp_apply, hk]
  have hns : ∀ k : ZMod 11, (quadraticChar (ZMod 11)) k = -1 → chiC 11 k = -1 := by
    intro k hk; simp [chiC, MulChar.ringHomComp_apply, hk]
  have h2 : chiC 11 (2 : ZMod 11) = -1 := hns 2 (by decide)
  have h3 : chiC 11 (3 : ZMod 11) = 1 := hsq 3 (by decide)
  have h4 : chiC 11 (4 : ZMod 11) = 1 := hsq 4 (by decide)
  have h5 : chiC 11 (5 : ZMod 11) = 1 := hsq 5 (by decide)
  have h6 : chiC 11 (6 : ZMod 11) = -1 := hns 6 (by decide)
  have h7 : chiC 11 (7 : ZMod 11) = -1 := hns 7 (by decide)
  have h8 : chiC 11 (8 : ZMod 11) = -1 := hns 8 (by decide)
  have h9 : chiC 11 (9 : ZMod 11) = 1 := hsq 9 (by decide)
  have h10 : chiC 11 (10 : ZMod 11) = -1 := hns 10 (by decide)
  -- additive character values
  have e0 : ψ₁₁ (0 : ZMod 11) = 1 := by simp [ψ₁₁]
  have e1 : ψ₁₁ (1 : ZMod 11) = ζ := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (1 : ZMod 11) = 1 from by decide, pow_one]
  have e2 : ψ₁₁ (2 : ZMod 11) = ζ ^ 2 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (2 : ZMod 11) = 2 from by decide]
  have e3 : ψ₁₁ (3 : ZMod 11) = ζ ^ 3 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (3 : ZMod 11) = 3 from by decide]
  have e4 : ψ₁₁ (4 : ZMod 11) = ζ ^ 4 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (4 : ZMod 11) = 4 from by decide]
  have e5 : ψ₁₁ (5 : ZMod 11) = ζ ^ 5 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (5 : ZMod 11) = 5 from by decide]
  have e6 : ψ₁₁ (6 : ZMod 11) = ζ ^ 6 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (6 : ZMod 11) = 6 from by decide]
  have e7 : ψ₁₁ (7 : ZMod 11) = ζ ^ 7 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (7 : ZMod 11) = 7 from by decide]
  have e8 : ψ₁₁ (8 : ZMod 11) = ζ ^ 8 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (8 : ZMod 11) = 8 from by decide]
  have e9 : ψ₁₁ (9 : ZMod 11) = ζ ^ 9 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (9 : ZMod 11) = 9 from by decide]
  have e10 : ψ₁₁ (10 : ZMod 11) = ζ ^ 10 := by
    rw [ψ₁₁, AddChar.zmodChar_apply, show ZMod.val (10 : ZMod 11) = 10 from by decide]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  ring

/-! ### Folding the redundant upper-half sines -/

theorem sin_fold_12 : Real.sin (12 * π / 11) = -Real.sin (10 * π / 11) := by
  have h12 : (12 * π / 11 : ℝ) = π / 11 + π := by ring
  have h10 : (10 * π / 11 : ℝ) = π - π / 11 := by ring
  rw [h12, h10, Real.sin_pi_sub, Real.sin_add, Real.cos_pi, Real.sin_pi]; ring

theorem sin_fold_14 : Real.sin (14 * π / 11) = -Real.sin (8 * π / 11) := by
  have h14 : (14 * π / 11 : ℝ) = 3 * π / 11 + π := by ring
  have h8 : (8 * π / 11 : ℝ) = π - 3 * π / 11 := by ring
  rw [h14, h8, Real.sin_pi_sub, Real.sin_add, Real.cos_pi, Real.sin_pi]; ring

theorem sin_fold_16 : Real.sin (16 * π / 11) = -Real.sin (6 * π / 11) := by
  have h16 : (16 * π / 11 : ℝ) = 5 * π / 11 + π := by ring
  have h6 : (6 * π / 11 : ℝ) = π - 5 * π / 11 := by ring
  rw [h16, h6, Real.sin_pi_sub, Real.sin_add, Real.cos_pi, Real.sin_pi]; ring

theorem sin_fold_18 : Real.sin (18 * π / 11) = -Real.sin (4 * π / 11) := by
  have h18 : (18 * π / 11 : ℝ) = 7 * π / 11 + π := by ring
  have h4 : (4 * π / 11 : ℝ) = π - 7 * π / 11 := by ring
  rw [h18, h4, Real.sin_pi_sub, Real.sin_add, Real.cos_pi, Real.sin_pi]; ring

theorem sin_fold_20 : Real.sin (20 * π / 11) = -Real.sin (2 * π / 11) := by
  have h20 : (20 * π / 11 : ℝ) = 9 * π / 11 + π := by ring
  have h2 : (2 * π / 11 : ℝ) = π - 9 * π / 11 := by ring
  rw [h20, h2, Real.sin_pi_sub, Real.sin_add, Real.cos_pi, Real.sin_pi]; ring

/-! ### The imaginary part of the Gauss sum -/

/-- The Gauss sum for `p = 11` is imaginary with
`Im g = 2·sin(2π/11) - 2·sin(4π/11) + 2·sin(6π/11) + 2·sin(8π/11) + 2·sin(10π/11)`. -/
theorem gaussSum_eleven_im :
    (gaussSum (chiC 11) ψ₁₁).im =
      2 * Real.sin (2 * π / 11) - 2 * Real.sin (4 * π / 11) + 2 * Real.sin (6 * π / 11)
        + 2 * Real.sin (8 * π / 11) + 2 * Real.sin (10 * π / 11) := by
  rw [gaussSum_eleven_eq]
  have hz1 : ζ = Complex.exp ((↑(2 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ]; congr 1; push_cast; ring
  have hz2 : ζ ^ 2 = Complex.exp ((↑(4 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz3 : ζ ^ 3 = Complex.exp ((↑(6 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz4 : ζ ^ 4 = Complex.exp ((↑(8 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz5 : ζ ^ 5 = Complex.exp ((↑(10 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz6 : ζ ^ 6 = Complex.exp ((↑(12 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz7 : ζ ^ 7 = Complex.exp ((↑(14 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz8 : ζ ^ 8 = Complex.exp ((↑(16 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz9 : ζ ^ 9 = Complex.exp ((↑(18 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz10 : ζ ^ 10 = Complex.exp ((↑(20 * π / 11) : ℂ) * Complex.I) := by
    rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- resolve higher powers first so `hz1` does not fire inside `ζ^k`
  rw [hz10, hz9, hz8, hz7, hz6, hz5, hz4, hz3, hz2, hz1]
  simp only [Complex.add_im, Complex.sub_im, Complex.exp_ofReal_mul_I_im]
  rw [sin_fold_12, sin_fold_14, sin_fold_16, sin_fold_18, sin_fold_20]
  ring

/-! ### Positivity of the imaginary part, hence the sign theorem for `p = 11` -/

/-- The open positivity crux `0 < Im g`, verified in the case `p = 11`. -/
theorem gaussSum_eleven_im_pos : 0 < (gaussSum (chiC 11) ψ₁₁).im := by
  rw [gaussSum_eleven_im]
  have hpi := Real.pi_pos
  -- the three unconditionally positive sines (angles in `(0, π)`)
  have hs2 : 0 < Real.sin (2 * π / 11) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs8 : 0 < Real.sin (8 * π / 11) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs10 : 0 < Real.sin (10 * π / 11) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- the lone negative term is dominated: sin(6π/11) = sin(5π/11) > sin(4π/11)
  have h6eq : Real.sin (6 * π / 11) = Real.sin (5 * π / 11) := by
    have : (6 * π / 11 : ℝ) = π - 5 * π / 11 := by ring
    rw [this, Real.sin_pi_sub]
  have hmono : Real.sin (4 * π / 11) < Real.sin (5 * π / 11) := by
    apply Real.strictMonoOn_sin
    · exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · linarith
  have hdom : Real.sin (4 * π / 11) < Real.sin (6 * π / 11) := by rw [h6eq]; exact hmono
  linarith

/-- **Gauss's hard sign theorem, case `p = 11`.** For the standard additive character
`ψ₁₁(x) = exp(2πi/11)^x`, the quadratic Gauss sum equals exactly `+i·√11` (not `-i·√11`).
This is the next sign *determination* on the `p ≡ 3 (mod 4)` branch (after `p = 3, 7`),
confirming the open crux `0 < Im g` for `p = 11` by a coarse-sign argument that needs no
exact (cubic-irrational) trigonometric value. -/
theorem gaussSum_eleven_eq_I_sqrt_eleven :
    gaussSum (chiC 11) ψ₁₁ = (Real.sqrt 11 : ℂ) * Complex.I := by
  have hp4 : (11 : ℕ) % 4 = 3 := by norm_num
  have h := (gaussSum_eq_I_sqrt_iff_im_pos hp4 ψ₁₁_isPrimitive).mpr gaussSum_eleven_im_pos
  simpa using h

end QuadraticGaussSumSignSmallEleven
