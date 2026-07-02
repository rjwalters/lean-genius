/-
  Bessel's inequality via summed rank-one projections onto an orthonormal family
  Open Question: cauchy-schwarz-oq-04-oq-02-oq-01

  The grandparent (cauchy-schwarz-oq-04) hand-rolls the one-dimensional rank-one projection
      proj u v = (⟪u, v⟫ / ‖v‖²) • v
  and the parent (cauchy-schwarz-oq-04-oq-02) identifies it with Mathlib's orthogonal
  projection `(ℝ ∙ v).starProjection`, deriving the single-vector Bessel bound
  `‖proj u v‖ ≤ ‖u‖` as `norm_starProjection_apply_le` for the line `ℝ ∙ v`.

  This entry answers the parent's open question: *lift the one-line projection to an
  orthonormal family and recover the full Bessel inequality.* For an orthonormal family
  `e : ι → E` and a finite index set `s`, the natural generalisation of the rank-one
  projection is the **summed rank-one projection**

      besselSum e s u = ∑ i ∈ s, ⟪e i, u⟫ • e i.

  We prove, entirely from first principles (no appeal to Mathlib's `sum_inner_products_le`):

    * `besselSum_inner_left` — the residual `u − besselSum e s u` is orthogonal to each `e j`
      (`j ∈ s`), the family analogue of the parent's `sub_proj_orthogonal`;
    * `norm_besselSum_sq` — the Pythagorean coefficient identity
      `‖besselSum e s u‖² = ∑ i ∈ s, ⟪e i, u⟫²` (orthonormality collapses the double sum);
    * `norm_add_besselSum` — the orthogonal decomposition `‖u‖² = ‖besselSum e s u‖² + ‖residual‖²`;
    * `bessel_inequality` — Bessel: `∑ i ∈ s, ⟪e i, u⟫² ≤ ‖u‖²`, obtained by *dropping* the
      nonnegative residual term rather than by algebraic expansion.

  The central bridge, generalising the parent's `proj_eq_starProjection`, is

      besselSum_eq_starProjection :
        besselSum e s u = (span ℝ (e '' s)).starProjection u,

  identifying the summed rank-one map with Mathlib's genuine orthogonal projection onto the
  finite-dimensional span of the family. The span is finite-dimensional, hence complete
  (`FiniteDimensional.proper_real`), so `HasOrthogonalProjection` is automatic — no ambient
  completeness assumption on `E` is needed. Once the bridge is in place, Bessel is exactly
  `norm_starProjection_apply_le` for the subspace `span ℝ (e '' s)`, exhibiting the family
  inequality as the projection-never-lengthens principle, precisely as the parent exhibited
  the one-line case.

  Finally `bessel_inequality_eq_mathlib` records that our coefficient sum agrees with
  Mathlib's `Orthonormal.sum_inner_products_le` (whose statement uses `‖⟪e i, u⟫‖²`), and
  `bessel_singleton` specialises `s = {j}` back to the parent's one-term bound.

  References:
  - Steele, "The Cauchy-Schwarz Master Class" (2004), Ch. 2 (projection viewpoint)
  - Mathlib.Analysis.InnerProductSpace.Orthonormal (`Orthonormal.sum_inner_products_le`)
  - Mathlib.Analysis.InnerProductSpace.Projection.Basic (`norm_starProjection_apply_le`)
  - Parent: CauchySchwarzOQ04OQ02.lean (`proj_eq_starProjection`, one-line Bessel)
-/

import Mathlib

namespace CauchySchwarzOQ04OQ02OQ01

open scoped InnerProductSpace RealInnerProductSpace
open Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

-- ============================================================================
-- Part I: The summed rank-one projection onto an orthonormal family
-- ============================================================================

/-- The **summed rank-one projection** of `u` onto the orthonormal family `e` restricted to the
finite index set `s`.  Each summand `⟪e i, u⟫ • e i` is the rank-one projection of `u` onto the
line `ℝ ∙ e i` (the grandparent's `proj u (e i)`, since `‖e i‖ = 1`); the family projection is
their sum. -/
noncomputable def besselSum (e : ι → E) (s : Finset ι) (u : E) : E :=
  ∑ i ∈ s, ⟪e i, u⟫_ℝ • e i

/-- The Fourier coefficient `⟪e j, u⟫` is recovered as the `j`-th coordinate of the projection:
`⟪e j, besselSum e s u⟫ = ⟪e j, u⟫` for `j ∈ s`.  This is the family analogue of the parent's
`starProjection_eq_projCoeff_smul` coordinate read-off. -/
theorem inner_left_besselSum {e : ι → E} (hv : Orthonormal ℝ e) {s : Finset ι} {j : ι}
    (hj : j ∈ s) (u : E) : ⟪e j, besselSum e s u⟫_ℝ = ⟪e j, u⟫_ℝ := by
  simpa [besselSum] using hv.inner_right_sum (fun i => ⟪e i, u⟫_ℝ) hj

-- ============================================================================
-- Part II: Orthogonality of the residual (the family analogue of the parent)
-- ============================================================================

/-- **Residual orthogonality (to each basis vector).**  For `j ∈ s`, the residual
`u − besselSum e s u` is orthogonal to `e j`.  Generalises the parent's `sub_proj_orthogonal`
from the single line `ℝ ∙ v` to every member of the orthonormal family. -/
theorem besselSum_inner_left {e : ι → E} (hv : Orthonormal ℝ e) {s : Finset ι} {j : ι}
    (hj : j ∈ s) (u : E) : ⟪e j, u - besselSum e s u⟫_ℝ = 0 := by
  rw [inner_sub_right, inner_left_besselSum hv hj u, sub_self]

/-- **Residual orthogonality (to the projection).**  The residual is orthogonal to the projection
itself — the Pythagorean orthogonality underlying the decomposition of `u`. -/
theorem besselSum_inner_self {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E) :
    ⟪besselSum e s u, u - besselSum e s u⟫_ℝ = 0 := by
  simp only [besselSum]
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [inner_smul_left, inner_sub_right, hv.inner_right_sum (fun j => ⟪e j, u⟫_ℝ) hi, sub_self,
    mul_zero]

-- ============================================================================
-- Part III: The Pythagorean coefficient identity and Bessel's inequality
-- ============================================================================

/-- **Coefficient identity (Pythagoras for the projection).**  Orthonormality collapses the
double sum `⟪∑ cᵢ eᵢ, ∑ cⱼ eⱼ⟫` to `∑ cᵢ²`:
`‖besselSum e s u‖² = ∑ i ∈ s, ⟪e i, u⟫²`.  This is the family generalisation of the parent's
`(projCoeff u v)² ‖v‖²` term, now a genuine sum of squared Fourier coefficients. -/
theorem norm_besselSum_sq {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E) :
    ‖besselSum e s u‖ ^ 2 = ∑ i ∈ s, ⟪e i, u⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [besselSum]
  rw [hv.inner_sum (fun i => ⟪e i, u⟫_ℝ) (fun i => ⟪e i, u⟫_ℝ) s]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [pow_two]

/-- **Orthogonal decomposition of `u`.**  The Pythagorean split
`‖u‖² = ‖besselSum e s u‖² + ‖u − besselSum e s u‖²`, from the orthogonality of the projection
and the residual.  The family analogue of the parent's `norm_sq_split`. -/
theorem norm_add_besselSum {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E) :
    ‖u‖ ^ 2 = ‖besselSum e s u‖ ^ 2 + ‖u - besselSum e s u‖ ^ 2 := by
  have hsplit :
      ‖besselSum e s u + (u - besselSum e s u)‖ ^ 2
        = ‖besselSum e s u‖ ^ 2 + ‖u - besselSum e s u‖ ^ 2 := by
    rw [norm_add_sq_real, besselSum_inner_self hv s u]
    ring
  have hcancel : besselSum e s u + (u - besselSum e s u) = u := by abel
  rwa [hcancel] at hsplit

/-- **Bessel's inequality.**  For an orthonormal family `e` and any finite index set `s`,
`∑ i ∈ s, ⟪e i, u⟫² ≤ ‖u‖²`.  The proof drops the nonnegative residual term of the orthogonal
decomposition — Bessel as "the projection never lengthens a vector", exactly the mechanism of the
parent's single-line bound, now summed over the family. -/
theorem bessel_inequality {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E) :
    ∑ i ∈ s, ⟪e i, u⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [← norm_besselSum_sq hv s u, norm_add_besselSum hv s u]
  have : (0 : ℝ) ≤ ‖u - besselSum e s u‖ ^ 2 := sq_nonneg _
  linarith

-- ============================================================================
-- Part IV: The bridge to Mathlib's orthogonal projection
-- ============================================================================

/-- The projection lands in the span of the family. -/
theorem besselSum_mem_span (e : ι → E) (s : Finset ι) (u : E) :
    besselSum e s u ∈ span ℝ (e '' s) := by
  simp only [besselSum]
  refine sum_mem fun i hi => ?_
  exact smul_mem _ _ (subset_span (Set.mem_image_of_mem e hi))

/-- The residual lies in the orthogonal complement of the span of the family.  Orthogonality to
each generator `e i` (`besselSum_inner_left`) propagates to the whole span by linearity. -/
theorem sub_besselSum_mem_orthogonal {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E) :
    u - besselSum e s u ∈ (span ℝ (e '' s))ᗮ := by
  rw [mem_orthogonal]
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact besselSum_inner_left hv (Finset.mem_coe.mp hi) u
  | zero => exact inner_zero_left _
  | add x y _ _ ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
  | smul a x _ ihx => rw [inner_smul_left, ihx, mul_zero]

/-- **Central bridge.**  The summed rank-one projection is exactly Mathlib's orthogonal projection
onto the finite-dimensional span of the family:
`besselSum e s u = (span ℝ (e '' s)).starProjection u`.

The span is finite-dimensional (`FiniteDimensional.span_of_finite`), hence complete
(`FiniteDimensional.proper_real`), so `HasOrthogonalProjection` is inferred automatically — no
ambient completeness of `E` is required.  Generalises the parent's `proj_eq_starProjection`. -/
theorem besselSum_eq_starProjection {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E)
    [(span ℝ (e '' (s : Set ι))).HasOrthogonalProjection] :
    besselSum e s u = (span ℝ (e '' s)).starProjection u :=
  (eq_starProjection_of_mem_orthogonal (besselSum_mem_span e s u)
    (sub_besselSum_mem_orthogonal hv s u)).symm

/-- **Bessel as projection non-expansiveness.**  Via the bridge, the norm bound
`‖besselSum e s u‖ ≤ ‖u‖` is precisely `norm_starProjection_apply_le` for the span — the
projection form of Bessel, exactly the parent's mechanism for the single line. -/
theorem norm_besselSum_le {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E) :
    ‖besselSum e s u‖ ≤ ‖u‖ := by
  haveI : FiniteDimensional ℝ (span ℝ (e '' (s : Set ι))) :=
    FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image e)
  rw [besselSum_eq_starProjection hv s u]
  exact (span ℝ (e '' (s : Set ι))).norm_starProjection_apply_le u

-- ============================================================================
-- Part V: Agreement with Mathlib's Bessel and the one-term parent case
-- ============================================================================

/-- Our coefficient sum agrees with the sum in Mathlib's `Orthonormal.sum_inner_products_le`
(stated with `‖⟪e i, u⟫‖²`), since over `ℝ` the norm of a real is its absolute value and
`|r|² = r²`.  Thus `bessel_inequality` is the same statement, proved here through the projection. -/
theorem bessel_sum_eq_mathlib_sum (e : ι → E) (s : Finset ι) (u : E) :
    ∑ i ∈ s, ⟪e i, u⟫_ℝ ^ 2 = ∑ i ∈ s, ‖⟪e i, u⟫_ℝ‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

/-- Consistency check: our `bessel_inequality` and Mathlib's `Orthonormal.sum_inner_products_le`
bound the identical quantity, so the two Bessel statements coincide. -/
theorem bessel_inequality_eq_mathlib {e : ι → E} (hv : Orthonormal ℝ e) (s : Finset ι) (u : E) :
    ∑ i ∈ s, ‖⟪e i, u⟫_ℝ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [← bessel_sum_eq_mathlib_sum e s u]
  exact bessel_inequality hv s u

/-- **One-term specialisation (the parent's case).**  For the singleton `s = {j}`, the summed
projection collapses to the single rank-one projection `⟪e j, u⟫ • e j`, and Bessel reduces to
`⟪e j, u⟫² ≤ ‖u‖²` — the parent entry's one-line Cauchy–Schwarz bound for the unit vector `e j`. -/
theorem bessel_singleton {e : ι → E} (hv : Orthonormal ℝ e) (j : ι) (u : E) :
    ⟪e j, u⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 := by
  have := bessel_inequality hv {j} u
  simpa using this

/-- The singleton projection is the rank-one projection onto `e j`, matching the grandparent's
`proj u (e j)` (here with unit `e j`, so the coefficient is simply `⟪e j, u⟫`). -/
theorem besselSum_singleton (e : ι → E) (j : ι) (u : E) :
    besselSum e {j} u = ⟪e j, u⟫_ℝ • e j := by
  simp [besselSum]

-- ============================================================================
-- Part VI: The empty family and monotonicity in the index set
-- ============================================================================

/-- The projection over the empty index set is `0`, and Bessel reads `0 ≤ ‖u‖²`. -/
theorem besselSum_empty (e : ι → E) (u : E) : besselSum e ∅ u = 0 := by
  simp [besselSum]

/-- **Monotonicity.**  Enlarging the (finite) index set only increases the Bessel coefficient sum;
the whole family bound `∑' i, ⟪e i, u⟫² ≤ ‖u‖²` is the supremum over finite `s`.  Here we record
the finite monotonicity `s ⊆ t ⟹ ∑_{s} ≤ ∑_{t}` that drives that passage to the limit. -/
theorem bessel_sum_mono {e : ι → E} (s t : Finset ι) (hst : s ⊆ t) (u : E) :
    ∑ i ∈ s, ⟪e i, u⟫_ℝ ^ 2 ≤ ∑ i ∈ t, ⟪e i, u⟫_ℝ ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg hst fun i _ _ => sq_nonneg _

end CauchySchwarzOQ04OQ02OQ01
