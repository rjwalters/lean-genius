import Mathlib.NumberTheory.Transcendental.Liouville.Measure

/-
  The symmetric Oxtoby decomposition is ℚ-affine equivariant
  (algebraic-reals-meager — OQ-02 → OQ-01, structural follow-up)

  The sibling files record the **symmetric Oxtoby decomposition** of ℝ

      ℝ  =  L  ⊔  Lᶜ
            └ comeagre & null      (topologically large, measure-small)
                 └ meagre & conull (topologically small, measure-large)

  with `L = {x | Liouville x}`, and sharpen it by showing both pieces are
  *dense*. This file adds the missing **symmetry group**: the entire
  decomposition is invariant under the natural action of the rational affine
  group

      Aff(ℚ)  ↷  ℝ,      x ↦ q·x + r     (q ∈ ℚˣ, r ∈ ℚ).

  Every such map is a homeomorphism of `ℝ` that also preserves Lebesgue measure
  up to a positive scalar, so *a priori* it could permute the two Oxtoby pieces
  or blur the measure/category contrast. It does neither: it fixes `L` and `Lᶜ`
  **setwise**. Hence the Oxtoby pathology is not an artifact of a particular
  base point or scale — it is a genuinely `Aff(ℚ)`-equivariant partition of the
  line.

  ## The mechanism

  The classical predicate `Liouville` is `LiouvilleWith p` for *every* exponent
  `p` (`forall_liouvilleWith_iff`). Mathlib already proves each `LiouvilleWith p`
  is invariant under adding a rational (`add_rat_iff`) and multiplying by a
  nonzero rational (`mul_rat_iff`), and under negation (`neg_iff`). Quantifying
  those `iff`s over `p` transports them verbatim to `Liouville`, giving the
  pointwise equivariance

      Liouville (q·x + r) ↔ Liouville x        (q ≠ 0, q,r ∈ ℚ).

  Set-theoretically this says `f ⁻¹' L = L` for every rational affine `f`; since
  each such `f` is a bijection with a rational affine inverse, also `f '' L = L`.
  Complementation gives the same for `Lᶜ`, so the whole decomposition is fixed.

  ## Honesty / novelty

  No new mathematics: Part I is `forall_congr'` over Mathlib's existing
  `LiouvilleWith` transfer lemmas; Parts II–III are `Set.ext` / bijection
  bookkeeping. The value is the explicit, machine-checked statement that the
  measure/category anomaly is `Aff(ℚ)`-equivariant — a structural fact the
  sibling files leave unstated. Presented as a modest structural follow-up, not
  a new result.

  No new axioms (standard Mathlib triple inherited).

  References:
  - Oxtoby, J.C. (1980). "Measure and Category", Springer GTM 2.
  - Mathlib: NumberTheory.Transcendental.Liouville.{LiouvilleWith,Residual,
             Measure} (`forall_liouvilleWith_iff`, `LiouvilleWith.add_rat_iff`,
             `mul_rat_iff`, `neg_iff`, `eventually_residual_liouville`,
             `volume_setOf_liouville`).

  Tags: liouville-numbers, measure-theory, baire-category, group-action,
        affine-group, equivariance, oxtoby-duality, sharp-boundary
-/

set_option maxHeartbeats 400000

namespace AlgebraicRealsMeagerOQ02OQ01Equivariant

open MeasureTheory Filter Set

-- ============================================================================
-- Part I: pointwise ℚ-affine equivariance of the `Liouville` predicate
-- ============================================================================

/-- **Rational translation invariance.** `Liouville (x + r) ↔ Liouville x` for
    `r : ℚ`. Obtained by quantifying Mathlib's `LiouvilleWith.add_rat_iff` over
    the exponent `p` through `forall_liouvilleWith_iff`. -/
theorem liouville_add_rat_iff (x : ℝ) (r : ℚ) :
    Liouville (x + r) ↔ Liouville x := by
  rw [← forall_liouvilleWith_iff, ← forall_liouvilleWith_iff]
  exact forall_congr' fun _ => LiouvilleWith.add_rat_iff

/-- **Rational translation invariance (left form).** `Liouville (r + x) ↔
    Liouville x` for `r : ℚ`. -/
theorem liouville_rat_add_iff (r : ℚ) (x : ℝ) :
    Liouville (r + x) ↔ Liouville x := by
  rw [add_comm]; exact liouville_add_rat_iff x r

/-- **Reflection invariance.** `Liouville (-x) ↔ Liouville x`. -/
theorem liouville_neg_iff (x : ℝ) : Liouville (-x) ↔ Liouville x := by
  rw [← forall_liouvilleWith_iff, ← forall_liouvilleWith_iff]
  exact forall_congr' fun _ => LiouvilleWith.neg_iff

/-- **Nonzero rational scaling invariance.** `Liouville (x * r) ↔ Liouville x`
    for `r : ℚ`, `r ≠ 0`. -/
theorem liouville_mul_rat_iff {r : ℚ} (hr : r ≠ 0) (x : ℝ) :
    Liouville (x * r) ↔ Liouville x := by
  rw [← forall_liouvilleWith_iff, ← forall_liouvilleWith_iff]
  exact forall_congr' fun _ => LiouvilleWith.mul_rat_iff hr

/-- **Nonzero rational scaling invariance (left form).** `Liouville (r * x) ↔
    Liouville x` for `r : ℚ`, `r ≠ 0`. -/
theorem liouville_rat_mul_iff {r : ℚ} (hr : r ≠ 0) (x : ℝ) :
    Liouville (r * x) ↔ Liouville x := by
  rw [mul_comm]; exact liouville_mul_rat_iff hr x

/-- **Full rational affine equivariance.** For `q, r : ℚ` with `q ≠ 0`,
    `Liouville (q·x + r) ↔ Liouville x`. This is the pointwise invariance of the
    Liouville numbers under the action of the rational affine group `Aff(ℚ)`. -/
theorem liouville_rat_affine_iff {q : ℚ} (hq : q ≠ 0) (r : ℚ) (x : ℝ) :
    Liouville ((q : ℝ) * x + r) ↔ Liouville x := by
  rw [liouville_add_rat_iff, liouville_rat_mul_iff hq]

-- ============================================================================
-- Part II: set-level invariance of `L` and `Lᶜ`
-- ============================================================================

/-- **`L` is invariant under rational affine preimages.** For every
    `f : x ↦ q·x + r` with `q ≠ 0` (`q, r ∈ ℚ`), `f ⁻¹' L = L`. -/
theorem setOf_liouville_rat_affine_preimage {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    (fun x : ℝ => (q : ℝ) * x + r) ⁻¹' {x : ℝ | Liouville x}
      = {x : ℝ | Liouville x} := by
  ext x
  simp only [mem_preimage, mem_setOf_eq]
  exact liouville_rat_affine_iff hq r x

/-- **`Lᶜ` is invariant under rational affine preimages.** Complementation of
    the previous lemma: the *non*-Liouville reals are also `Aff(ℚ)`-invariant. -/
theorem setOf_liouville_compl_rat_affine_preimage {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    (fun x : ℝ => (q : ℝ) * x + r) ⁻¹' {x : ℝ | Liouville x}ᶜ
      = {x : ℝ | Liouville x}ᶜ := by
  rw [preimage_compl, setOf_liouville_rat_affine_preimage hq r]

/-- **`L` is invariant under rational affine images.** Each `f : x ↦ q·x + r`
    (`q ≠ 0`, `q, r ∈ ℚ`) is a bijection whose inverse `y ↦ q⁻¹·y - q⁻¹·r` is
    again rational affine, so `f '' L = L` follows from preimage invariance for
    the inverse map. -/
theorem setOf_liouville_rat_affine_image {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    (fun x : ℝ => (q : ℝ) * x + r) '' {x : ℝ | Liouville x}
      = {x : ℝ | Liouville x} := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [Set.image_eq_preimage_of_inverse
        (g := fun y : ℝ => ((q⁻¹ : ℚ) : ℝ) * y + ((-(q⁻¹ * r) : ℚ) : ℝ))
        (fun x => by push_cast; field_simp; ring)
        (fun y => by push_cast; field_simp; ring)]
  exact setOf_liouville_rat_affine_preimage (inv_ne_zero hq) (-(q⁻¹ * r))

-- ============================================================================
-- Part III: the equivariant symmetric Oxtoby decomposition
-- ============================================================================

/-- **The symmetric Oxtoby decomposition is `Aff(ℚ)`-equivariant.** For every
    rational affine map `f : x ↦ q·x + r` (`q ≠ 0`, `q, r ∈ ℚ`):

    * `f` fixes both pieces setwise (preimage and image), for `L` and for `Lᶜ`;
    * the invariant facts persist — `L` is comeagre and null, `Lᶜ` is meagre and
      conull.

    Thus the measure/category pathology `ℝ = L ⊔ Lᶜ` is not tied to any base
    point or scale: the whole rational affine group acts on `ℝ` preserving the
    decomposition. -/
theorem oxtoby_rat_affine_equivariant {q : ℚ} (hq : q ≠ 0) (r : ℚ) :
    (fun x : ℝ => (q : ℝ) * x + r) ⁻¹' {x : ℝ | Liouville x}
        = {x : ℝ | Liouville x} ∧
    (fun x : ℝ => (q : ℝ) * x + r) '' {x : ℝ | Liouville x}
        = {x : ℝ | Liouville x} ∧
    (fun x : ℝ => (q : ℝ) * x + r) ⁻¹' {x : ℝ | Liouville x}ᶜ
        = {x : ℝ | Liouville x}ᶜ ∧
    {x : ℝ | Liouville x} ∈ residual ℝ ∧
    volume {x : ℝ | Liouville x} = 0 ∧
    IsMeagre {x : ℝ | Liouville x}ᶜ ∧
    volume ({x : ℝ | Liouville x}ᶜ)ᶜ = 0 :=
  ⟨setOf_liouville_rat_affine_preimage hq r,
   setOf_liouville_rat_affine_image hq r,
   setOf_liouville_compl_rat_affine_preimage hq r,
   eventually_residual_liouville,
   volume_setOf_liouville,
   by rw [IsMeagre, compl_compl]; exact eventually_residual_liouville,
   by rw [compl_compl]; exact volume_setOf_liouville⟩

#check @liouville_rat_affine_iff
#check @setOf_liouville_rat_affine_preimage
#check @setOf_liouville_rat_affine_image
#check @setOf_liouville_compl_rat_affine_preimage
#check @oxtoby_rat_affine_equivariant

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `liouville_add_rat_iff` | `Liouville (x+r) ↔ Liouville x` | Proved |
  | `liouville_rat_add_iff` | `Liouville (r+x) ↔ Liouville x` | Proved |
  | `liouville_neg_iff` | `Liouville (-x) ↔ Liouville x` | Proved |
  | `liouville_mul_rat_iff` | `Liouville (x*r) ↔ Liouville x` (r≠0) | Proved |
  | `liouville_rat_mul_iff` | `Liouville (r*x) ↔ Liouville x` (r≠0) | Proved |
  | `liouville_rat_affine_iff` | `Liouville (q*x+r) ↔ Liouville x` (q≠0) | Proved |
  | `setOf_liouville_rat_affine_preimage` | `f ⁻¹' L = L` | Proved |
  | `setOf_liouville_compl_rat_affine_preimage` | `f ⁻¹' Lᶜ = Lᶜ` | Proved |
  | `setOf_liouville_rat_affine_image` | `f '' L = L` | Proved |
  | `oxtoby_rat_affine_equivariant` | full equivariant decomposition | Proved |

  **Sorries**: 0
  **Axioms**: 0 declared (Mathlib triple inherited)
-/

end AlgebraicRealsMeagerOQ02OQ01Equivariant
