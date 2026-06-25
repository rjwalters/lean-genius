import Mathlib
import Proofs.GramLinearIndependenceOQ01OQ03

/-!
# The Gram–Schmidt height is the distance to the span of the earlier vectors

The parent entry `gram-linear-independence-iff-oq-01-oq-03` proved the `k`-dimensional
content factorization

> `content_eq_prod_gramSchmidt_norm` :
> `√(det gram v) = ∏ i, ‖gramSchmidt ℝ v i‖`,

and *called* each factor `‖gramSchmidt ℝ v i‖` the **height** of `vᵢ` above the span of the
earlier vectors.  Its third open question asks to make that geometric reading literal:

> "Identify each Gram–Schmidt height with the distance `dist(vᵢ, span of the earlier
> vectors)`, giving the literal base × height recursion."

This entry proves exactly that.  Writing `Kᵢ = span ℝ {v j | j < i}` for the span of the
strictly earlier vectors, we show

> **`gramSchmidt_eq_sub_starProjection`** :
> `gramSchmidt ℝ v i = v i - Kᵢ.starProjection (v i)`,

i.e. the Gram–Schmidt vector is literally the residual of `vᵢ` after orthogonal projection
onto `Kᵢ`, and consequently

> **`norm_gramSchmidt_eq_infDist`** :
> `‖gramSchmidt ℝ v i‖ = Metric.infDist (v i) Kᵢ`,

the perpendicular distance from `vᵢ` to the earlier span.  Combined with the parent's
content factorization this gives the textbook *base × height* recursion for the volume:

> **`content_eq_prod_infDist`** :
> `√(det gram v) = ∏ i, Metric.infDist (v i) Kᵢ`.

## Proof

`Kᵢ` is finite-dimensional (it is the span of a finite set), hence complete, hence has an
orthogonal projection.  The Gram–Schmidt formula `gramSchmidt_def` writes
`gramSchmidt ℝ v i = v i - p` with `p` a sum of projections onto the lines spanned by earlier
Gram–Schmidt vectors, so `v i - gramSchmidt ℝ v i = p ∈ Kᵢ`.  Orthogonality of the
Gram–Schmidt family (`gramSchmidt_orthogonal`) gives `gramSchmidt ℝ v i ∈ Kᵢᗮ` (using
`span_gramSchmidt_Iio` to identify `Kᵢ` with the span of the earlier Gram–Schmidt vectors).
The orthogonal decomposition `v i = (v i - gramSchmidt ℝ v i) + gramSchmidt ℝ v i` then
characterizes the projection (`eq_starProjection_of_mem_orthogonal'`), and
`starProjection_minimal` turns the residual norm into the infimal distance.

All results hold with **no** assumption relating `n` to `finrank ℝ F`, and are fully
machine-checked with no `sorry` and no extra axioms.
-/

namespace GramLinearIndependenceOQ01OQ03OQ01

open InnerProductSpace Submodule Finset Matrix
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The span of the input vectors strictly before index `i` — the subspace whose
perpendicular distance to `v i` is the Gram–Schmidt height. -/
def earlierSpan (v : Fin n → F) (i : Fin n) : Submodule ℝ F :=
  Submodule.span ℝ (v '' Set.Iio i)

/-- `earlierSpan` is finite-dimensional: it is spanned by a finite set. -/
instance finiteDimensional_earlierSpan (v : Fin n → F) (i : Fin n) :
    FiniteDimensional ℝ (earlierSpan v i) :=
  FiniteDimensional.span_of_finite ℝ (Set.Finite.image v (Set.toFinite _))

/-- Gram–Schmidt preserves the earlier span: `Kᵢ` is also the span of the earlier
*orthogonalized* vectors. -/
theorem earlierSpan_eq_gramSchmidt (v : Fin n → F) (i : Fin n) :
    earlierSpan v i = Submodule.span ℝ (gramSchmidt ℝ v '' Set.Iio i) :=
  (span_gramSchmidt_Iio ℝ v i).symm

/-- The earlier Gram–Schmidt vectors lie in the earlier span. -/
theorem gramSchmidt_mem_earlierSpan (v : Fin n → F) {i j : Fin n} (hji : j < i) :
    gramSchmidt ℝ v j ∈ earlierSpan v i := by
  rw [earlierSpan_eq_gramSchmidt]
  exact subset_span (Set.mem_image_of_mem _ (Set.mem_Iio.mpr hji))

/-- The residual `v i - gramSchmidt ℝ v i` lies in the earlier span: it is the sum of the
projections of `v i` onto the lines of the earlier Gram–Schmidt vectors. -/
theorem sub_gramSchmidt_mem_earlierSpan (v : Fin n → F) (i : Fin n) :
    v i - gramSchmidt ℝ v i ∈ earlierSpan v i := by
  have hsub : v i - gramSchmidt ℝ v i
      = ∑ j ∈ Iio i, (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) := by
    rw [gramSchmidt_def ℝ v i, sub_sub_cancel]
  rw [hsub]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hji : j < i := Finset.mem_Iio.mp hj
  rw [starProjection_singleton]
  exact Submodule.smul_mem _ _ (gramSchmidt_mem_earlierSpan v hji)

/-- The Gram–Schmidt vector is orthogonal to the earlier span. -/
theorem gramSchmidt_mem_earlierSpan_orthogonal (v : Fin n → F) (i : Fin n) :
    gramSchmidt ℝ v i ∈ (earlierSpan v i)ᗮ := by
  rw [earlierSpan_eq_gramSchmidt, mem_orthogonal']
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact gramSchmidt_orthogonal ℝ v (Set.mem_Iio.mp hj).ne'
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- **Gram–Schmidt as a residual.**  `gramSchmidt ℝ v i` is exactly `v i` minus its
orthogonal projection onto the span of the earlier vectors. -/
theorem gramSchmidt_eq_sub_starProjection (v : Fin n → F) (i : Fin n) :
    gramSchmidt ℝ v i = v i - (earlierSpan v i).starProjection (v i) := by
  have hproj : (earlierSpan v i).starProjection (v i) = v i - gramSchmidt ℝ v i :=
    eq_starProjection_of_mem_orthogonal' (z := gramSchmidt ℝ v i)
      (sub_gramSchmidt_mem_earlierSpan v i)
      (gramSchmidt_mem_earlierSpan_orthogonal v i)
      (sub_add_cancel (v i) (gramSchmidt ℝ v i)).symm
  rw [hproj, sub_sub_cancel]

/-- The Gram–Schmidt height equals the norm of the projection residual. -/
theorem norm_gramSchmidt_eq_norm_sub_starProjection (v : Fin n → F) (i : Fin n) :
    ‖gramSchmidt ℝ v i‖ = ‖v i - (earlierSpan v i).starProjection (v i)‖ := by
  rw [gramSchmidt_eq_sub_starProjection]

/-- **The Gram–Schmidt height is the distance to the earlier span.**  This is the literal
geometric content of the "height" in the parent's base × height factorization. -/
theorem norm_gramSchmidt_eq_infDist (v : Fin n → F) (i : Fin n) :
    ‖gramSchmidt ℝ v i‖ = Metric.infDist (v i) (earlierSpan v i) := by
  rw [norm_gramSchmidt_eq_norm_sub_starProjection, starProjection_minimal,
    Metric.infDist_eq_iInf]
  exact iInf_congr fun x => (dist_eq_norm _ _).symm

/-! ## Base × height form of the content

Combine the new distance identity with the parent's content factorization, so the heights are
now read as genuine perpendicular distances. -/

/-- The Gram determinant as the squared product of distances to the earlier spans. -/
theorem det_gram_eq_prod_infDist_sq (v : Fin n → F) :
    (gram ℝ v).det = ∏ i, Metric.infDist (v i) (earlierSpan v i) ^ 2 := by
  rw [GramLinearIndependenceOQ01OQ03.det_gram_eq_prod_gramSchmidt_norm_sq]
  exact Finset.prod_congr rfl fun i _ => by rw [norm_gramSchmidt_eq_infDist]

/-- **Content as a product of distances (base × height volume).**
`√(det gram v) = ∏ i, dist(v i, span of earlier vectors)`, the literal base × height volume
of the parallelepiped, valid in any dimension. -/
theorem content_eq_prod_infDist (v : Fin n → F) :
    GramLinearIndependenceOQ01OQ03.content v
      = ∏ i, Metric.infDist (v i) (earlierSpan v i) := by
  rw [GramLinearIndependenceOQ01OQ03.content_eq_prod_gramSchmidt_norm]
  exact Finset.prod_congr rfl fun i _ => norm_gramSchmidt_eq_infDist v i

end

end GramLinearIndependenceOQ01OQ03OQ01
