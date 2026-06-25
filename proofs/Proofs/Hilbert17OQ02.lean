/-
  Hilbert's 17th problem — quantifying the PSD/SOS gap for the homogeneous
  Choi–Lam form.

  The two existing canonical gap members in the gallery are *affine*: the Motzkin
  polynomial `x⁴y² + x²y⁴ + 1 − 3x²y²` and Robinson's form.  The genuine
  *homogeneous* member of the gap on `ℝ³` is the cyclic Choi–Lam form

      CL(x, y, z) = x⁴y² + y⁴z² + z⁴x² − 3·x²y²z²       (Choi–Lam, 1977)

  which is positive-semidefinite (PSD) on all of `ℝ³` yet is **not** a sum of
  squares of polynomials: there is no degree-6 SOS certificate, exactly because
  the underlying inequality `x⁴y² + y⁴z² + z⁴x² ≥ 3x²y²z²` is the three-term
  AM–GM, which has no polynomial SOS proof.  (That non-SOS fact is the classical
  Choi–Lam result, established for the sibling Motzkin/Robinson forms by the
  Gram-matrix technique of `Hilbert17MotzkinNotSOS` / `Hilbert17RobinsonNotSOS`;
  it is *not* re-derived here.)

  This file quantifies the gap with a sharp, fully explicit certificate.  By
  Artin's theorem CL is a sum of squares of *rational* functions; the question
  "how complex is the certificate?" is answered here by an explicit **degree-2
  denominator**: multiplying CL by the single quadratic form `x² + y² + z²`
  turns it into an honest polynomial sum of squares,

      (x² + y² + z²)·CL
        = (x³y − xyz²)² + (y³z − x²yz)² + (z³x − xy²z)²
          + ½[(x²y² − y²z²)² + (y²z² − z²x²)² + (z²x² − x²y²)²].

  So the PSD/SOS gap for CL is bridged by a multiplier of degree exactly `2` —
  the minimal possible, since CL itself is not SOS.  From this identity we read
  off:

    * `multiplier_sos_identity` — the exact `ring` identity above (the heart).
    * `choiLam_three_nonneg` — CL is PSD on `ℝ³` (divide the identity by the
      strictly-positive multiplier off the origin; the origin is the zero of CL).
    * `choiLam_psd_iff` — the family `x⁴y² + y⁴z² + z⁴x² − c·x²y²z²` is PSD
      **iff** `c ≤ 3`, so `c = 3` is the sharp boundary coefficient (the same
      AM–GM threshold pinned down for the affine Motzkin family in the sibling
      entry `Hilbert17OQ03OQ05`, here in its genuine homogeneous ternary form).

  Everything is `0`-axiom, over `ℝ` and `MvPolynomial (Fin 3) ℝ`.
-/
import Mathlib

namespace Hilbert17OQ02

open MvPolynomial

/-! ## The Choi–Lam family as a real three-variable function -/

/-- The Choi–Lam family evaluated at real arguments:
    `CLₐ(x, y, z) = x⁴y² + y⁴z² + z⁴x² − c·x²y²z²`.  The classical Choi–Lam
    form is the boundary member `c = 3`. -/
def choiLam (c x y z : ℝ) : ℝ :=
  x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2 + z ^ 4 * x ^ 2 - c * (x ^ 2 * y ^ 2 * z ^ 2)

/-! ## The explicit degree-2 multiplier certificate (the gap quantification) -/

/-- **Multiplier SOS identity.**  Multiplying the Choi–Lam form `CL = choiLam 3`
    by the single quadratic `x² + y² + z²` produces an honest polynomial sum of
    squares.  This is the exact, machine-checked Positivstellensatz certificate
    behind Artin's theorem for CL, with a denominator of degree `2`. -/
theorem multiplier_sos_identity (x y z : ℝ) :
    (x ^ 2 + y ^ 2 + z ^ 2) * choiLam 3 x y z
      = (x ^ 3 * y - x * y * z ^ 2) ^ 2
        + (y ^ 3 * z - x ^ 2 * y * z) ^ 2
        + (z ^ 3 * x - x * y ^ 2 * z) ^ 2
        + ((x ^ 2 * y ^ 2 - y ^ 2 * z ^ 2) ^ 2
            + (y ^ 2 * z ^ 2 - z ^ 2 * x ^ 2) ^ 2
            + (z ^ 2 * x ^ 2 - x ^ 2 * y ^ 2) ^ 2) / 2 := by
  unfold choiLam
  ring

/-- The product `(x²+y²+z²)·CL` is non-negative everywhere — it is a sum of
    squares by `multiplier_sos_identity`. -/
theorem multiplier_mul_nonneg (x y z : ℝ) :
    0 ≤ (x ^ 2 + y ^ 2 + z ^ 2) * choiLam 3 x y z := by
  rw [multiplier_sos_identity]
  positivity

/-! ## Positive-semidefiniteness of the Choi–Lam form -/

/-- **CL is PSD.**  The classical Choi–Lam form `c = 3` is non-negative on all of
    `ℝ³`.  Off the origin the strictly-positive multiplier `x²+y²+z²` divides out
    of `multiplier_mul_nonneg`; at the origin CL vanishes. -/
theorem choiLam_three_nonneg (x y z : ℝ) : 0 ≤ choiLam 3 x y z := by
  rcases eq_or_ne (x ^ 2 + y ^ 2 + z ^ 2) 0 with h | h
  · -- `x² + y² + z² = 0` forces `x² = y² = z² = 0`, so every monomial of CL
    -- vanishes.  We work with the squares directly (no `pow_eq_zero_iff`).
    have hx2 : x ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg y, sq_nonneg z]) (sq_nonneg x)
    have hy2 : y ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg x, sq_nonneg z]) (sq_nonneg y)
    have hz2 : z ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg x, sq_nonneg y]) (sq_nonneg z)
    have hzero : choiLam 3 x y z = 0 := by
      have e : choiLam 3 x y z
          = (x ^ 2) ^ 2 * y ^ 2 + (y ^ 2) ^ 2 * z ^ 2 + (z ^ 2) ^ 2 * x ^ 2
            - 3 * (x ^ 2 * y ^ 2 * z ^ 2) := by
        unfold choiLam; ring
      rw [e, hx2, hy2, hz2]; ring
    exact le_of_eq hzero.symm
  · -- `x² + y² + z² > 0`, so non-negativity transfers from the product.
    have hpos : 0 < x ^ 2 + y ^ 2 + z ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm h)
    by_contra hc
    push_neg at hc
    have : (x ^ 2 + y ^ 2 + z ^ 2) * choiLam 3 x y z < 0 :=
      mul_neg_of_pos_of_neg hpos hc
    linarith [multiplier_mul_nonneg x y z]

/-! ## The sharp PSD threshold `c ≤ 3` -/

/-- **Non-negativity for `c ≤ 3`.**  For every coefficient `c ≤ 3` the family
    `CLₐ` is non-negative everywhere: the deficit `(3 − c)·x²y²z² ≥ 0` only adds
    to the PSD boundary member `CL = choiLam 3`. -/
theorem choiLam_nonneg_of_le {c : ℝ} (hc : c ≤ 3) (x y z : ℝ) :
    0 ≤ choiLam c x y z := by
  have hbase := choiLam_three_nonneg x y z
  have hsq : (0 : ℝ) ≤ x ^ 2 * y ^ 2 * z ^ 2 := by positivity
  have hdiff : 0 ≤ (3 - c) * (x ^ 2 * y ^ 2 * z ^ 2) :=
    mul_nonneg (by linarith) hsq
  -- `choiLam c = choiLam 3 + (3 − c)·x²y²z²`.
  have : choiLam c x y z = choiLam 3 x y z + (3 - c) * (x ^ 2 * y ^ 2 * z ^ 2) := by
    unfold choiLam; ring
  rw [this]; linarith

/-- **Failure for `c > 3`.**  At `(x, y, z) = (1, 1, 1)` the value is `3 − c < 0`,
    so the family leaves the PSD cone once `c` exceeds `3`. -/
theorem choiLam_neg_of_gt {c : ℝ} (hc : 3 < c) : choiLam c 1 1 1 < 0 := by
  unfold choiLam; nlinarith [hc]

/-- **Sharp PSD threshold.**  The Choi–Lam family is non-negative on all of `ℝ³`
    if and only if `c ≤ 3`.  Thus `c = 3` (the classical Choi–Lam form) is the
    extremal PSD member — the genuine homogeneous analogue of the affine Motzkin
    threshold. -/
theorem choiLam_psd_iff (c : ℝ) :
    (∀ x y z : ℝ, 0 ≤ choiLam c x y z) ↔ c ≤ 3 := by
  constructor
  · intro h
    have h111 := h 1 1 1
    unfold choiLam at h111
    norm_num at h111
    linarith
  · intro hc x y z
    exact choiLam_nonneg_of_le hc x y z

/-- `3` is the **largest** coefficient for which the family is PSD. -/
theorem three_is_sharp {c : ℝ} (hPSD : ∀ x y z : ℝ, 0 ≤ choiLam c x y z) :
    c ≤ 3 := (choiLam_psd_iff c).1 hPSD

/-! ## The family as a genuine `MvPolynomial (Fin 3) ℝ`

We repackage the same facts for the polynomial object, matching the parent
entry's `IsPositiveSemidefiniteMv` formulation. -/

/-- The Choi–Lam family as a trivariate polynomial:
    `X₀⁴X₁² + X₁⁴X₂² + X₂⁴X₀² − c·X₀²X₁²X₂²`. -/
noncomputable def choiLamPoly (c : ℝ) : MvPolynomial (Fin 3) ℝ :=
  X 0 ^ 4 * X 1 ^ 2 + X 1 ^ 4 * X 2 ^ 2 + X 2 ^ 4 * X 0 ^ 2
    - C c * (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2)

/-- A multivariate polynomial is PSD if it is non-negative for all real inputs
    (matching `Hilbert17.IsPositiveSemidefiniteMv` in the parent file). -/
def IsPSDMv (p : MvPolynomial (Fin 3) ℝ) : Prop :=
  ∀ v : Fin 3 → ℝ, 0 ≤ MvPolynomial.eval v p

/-- Evaluating `choiLamPoly` recovers the real function `choiLam`. -/
@[simp] theorem eval_choiLamPoly (c : ℝ) (v : Fin 3 → ℝ) :
    MvPolynomial.eval v (choiLamPoly c) = choiLam c (v 0) (v 1) (v 2) := by
  unfold choiLamPoly choiLam
  simp only [map_add, map_sub, map_mul, map_pow, eval_X, eval_C]

/-- **Sharp PSD threshold (polynomial form).**  `choiLamPoly c` is PSD if and
    only if `c ≤ 3`. -/
theorem choiLamPoly_psd_iff (c : ℝ) : IsPSDMv (choiLamPoly c) ↔ c ≤ 3 := by
  unfold IsPSDMv
  constructor
  · intro h
    have h111 := h (fun _ => 1)
    simp only [eval_choiLamPoly] at h111
    unfold choiLam at h111
    norm_num at h111
    linarith
  · intro hc v
    rw [eval_choiLamPoly]
    exact choiLam_nonneg_of_le hc (v 0) (v 1) (v 2)

/-- The classical Choi–Lam form (`c = 3`) is PSD as a trivariate polynomial — the
    boundary member of the family, and the canonical homogeneous element of the
    PSD/SOS gap. -/
theorem choiLamPoly_three_psd : IsPSDMv (choiLamPoly 3) :=
  (choiLamPoly_psd_iff 3).2 (le_refl 3)

end Hilbert17OQ02
