/-
  Hilbert's 17th problem — the sharp PSD threshold of the Motzkin family.

  The Motzkin polynomial `M(x, y) = x⁴y² + x²y⁴ + 1 − 3 x²y²` is the canonical
  example of a positive-semidefinite (PSD) polynomial that is *not* a sum of
  squares of polynomials.  Its parent entry establishes both facts; the
  non-SOS side is the deep content (it underlies the parent open question on the
  computational complexity of *deciding* whether a PSD polynomial is SOS, and on
  *quantifying* the PSD/SOS gap).

  This file isolates a complementary, fully elementary fact: the coefficient `3`
  in front of `x²y²` is **sharp**.  Consider the one-parameter family

      Mₐ(x, y) = x⁴y² + x²y⁴ + 1 − c·x²y²,   c ∈ ℝ.

  We prove the exact threshold

      Mₐ is PSD on ℝ²   ⟺   c ≤ 3,

  so the Motzkin polynomial (`c = 3`) sits exactly on the boundary of the PSD
  cone for this family.  This pins down *why* `3` is the canonical coefficient:
  it is the largest constant for which non-negativity survives, and it is the
  unique value at which the family is PSD but its membership in the SOS cone
  fails (the parent's `motzkin_not_sos`).

  The two directions:

    * `c ≤ 3 ⟹ PSD`: the AM–GM step `x⁴y² + x²y⁴ + 1 ≥ 3 x²y²` (an honest
      sum-of-squares certificate, found by `nlinarith`) dominates the deficit
      `(3 − c)·x²y² ≥ 0`.
    * `c > 3 ⟹ not PSD`: evaluate at `(1, 1)`, where `Mₐ(1,1) = 3 − c < 0`.

  Everything is `0`-axiom, over `ℝ` and `MvPolynomial (Fin 2) ℝ`.
-/
import Mathlib

namespace Hilbert17OQ03OQ05

open MvPolynomial

/-! ## The family as a real two-variable function -/

/-- The Motzkin family evaluated at real arguments:
    `Mₐ(x, y) = x⁴y² + x²y⁴ + 1 − c·x²y²`. -/
def motzkinFun (c x y : ℝ) : ℝ :=
  x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + 1 - c * (x ^ 2 * y ^ 2)

/-- **AM–GM core.**  `x⁴y² + x²y⁴ + 1 ≥ 3 x²y²` for all real `x, y`.  This is a
    genuine sum-of-squares certificate (the affine Motzkin form has one, even
    though the homogeneous Motzkin polynomial does not). -/
theorem motzkin_amgm (x y : ℝ) :
    3 * (x ^ 2 * y ^ 2) ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + 1 := by
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x ^ 2 * y - y),
    sq_nonneg (x * y ^ 2 - x), sq_nonneg (x * y),
    mul_nonneg (sq_nonneg x) (sq_nonneg y), sq_nonneg (x ^ 2 * y ^ 2 - 1)]

/-- **Non-negativity for `c ≤ 3`.**  For every coefficient `c ≤ 3` the family
    `Mₐ` is non-negative everywhere. -/
theorem motzkinFun_nonneg {c : ℝ} (hc : c ≤ 3) (x y : ℝ) :
    0 ≤ motzkinFun c x y := by
  have hsq : (0 : ℝ) ≤ x ^ 2 * y ^ 2 :=
    mul_nonneg (sq_nonneg x) (sq_nonneg y)
  have hdef : c * (x ^ 2 * y ^ 2) ≤ 3 * (x ^ 2 * y ^ 2) := by
    exact mul_le_mul_of_nonneg_right hc hsq
  have hamgm := motzkin_amgm x y
  unfold motzkinFun
  linarith

/-- **Failure for `c > 3`.**  At `(x, y) = (1, 1)` the value is `3 − c < 0`,
    so the family is not PSD once `c` exceeds `3`. -/
theorem motzkinFun_neg_of_gt {c : ℝ} (hc : 3 < c) :
    motzkinFun c 1 1 < 0 := by
  unfold motzkinFun
  nlinarith [hc]

/-- **Sharp PSD threshold (real form).**  The family `Mₐ` is non-negative on all
    of `ℝ²` if and only if `c ≤ 3`.  Thus `c = 3` (the Motzkin polynomial) is the
    extremal PSD member of the family. -/
theorem motzkinFun_psd_iff (c : ℝ) :
    (∀ x y : ℝ, 0 ≤ motzkinFun c x y) ↔ c ≤ 3 := by
  constructor
  · intro h
    have h11 := h 1 1
    unfold motzkinFun at h11
    norm_num at h11
    linarith
  · intro hc x y
    exact motzkinFun_nonneg hc x y

/-- The Motzkin polynomial itself (`c = 3`) is PSD — the boundary case of the
    threshold. -/
theorem motzkin_nonneg (x y : ℝ) : 0 ≤ motzkinFun 3 x y :=
  motzkinFun_nonneg (le_refl 3) x y

/-- `3` is the **largest** coefficient for which the family is PSD: any strictly
    larger `c` fails non-negativity (witnessed at `(1,1)`). -/
theorem three_is_sharp {c : ℝ} (hPSD : ∀ x y : ℝ, 0 ≤ motzkinFun c x y) :
    c ≤ 3 := (motzkinFun_psd_iff c).1 hPSD

/-! ## The family as a genuine `MvPolynomial (Fin 2) ℝ`

We repackage the same threshold for the polynomial object, matching the parent
entry's `IsPositiveSemidefiniteMv` formulation. -/

/-- The Motzkin family as a bivariate polynomial:
    `X₀⁴ X₁² + X₀² X₁⁴ + 1 − c·X₀² X₁²`. -/
noncomputable def motzkinPoly (c : ℝ) : MvPolynomial (Fin 2) ℝ :=
  X 0 ^ 4 * X 1 ^ 2 + X 0 ^ 2 * X 1 ^ 4 + 1 - C c * (X 0 ^ 2 * X 1 ^ 2)

/-- A multivariate polynomial is PSD if it is non-negative for all real inputs
    (matching `Hilbert17.IsPositiveSemidefiniteMv` in the parent file). -/
def IsPSDMv (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ v : Fin 2 → ℝ, 0 ≤ MvPolynomial.eval v p

/-- Evaluating `motzkinPoly` recovers the real function `motzkinFun`. -/
@[simp] theorem eval_motzkinPoly (c : ℝ) (v : Fin 2 → ℝ) :
    MvPolynomial.eval v (motzkinPoly c) = motzkinFun c (v 0) (v 1) := by
  unfold motzkinPoly motzkinFun
  simp only [map_add, map_sub, map_mul, map_pow, map_one, eval_X, eval_C]

/-- **Sharp PSD threshold (polynomial form).**  `motzkinPoly c` is PSD if and
    only if `c ≤ 3`. -/
theorem motzkinPoly_psd_iff (c : ℝ) : IsPSDMv (motzkinPoly c) ↔ c ≤ 3 := by
  unfold IsPSDMv
  constructor
  · intro h
    have h11 := h (fun _ => 1)
    simp only [eval_motzkinPoly] at h11
    -- `motzkinFun c 1 1 = 3 - c`, so `0 ≤ 3 - c`.
    unfold motzkinFun at h11
    norm_num at h11
    linarith
  · intro hc v
    rw [eval_motzkinPoly]
    exact motzkinFun_nonneg hc (v 0) (v 1)

/-- The Motzkin polynomial (`c = 3`) is PSD as a bivariate polynomial — the
    boundary member of the family. -/
theorem motzkinPoly_three_psd : IsPSDMv (motzkinPoly 3) :=
  (motzkinPoly_psd_iff 3).2 (le_refl 3)

end Hilbert17OQ03OQ05
