/-
# From Rank-One to Finite-Rank — Projection onto a Subspace as a Sum of Rank-One Projectors

Open Question (cauchy-schwarz-oq-01-oq-02-oq-01-oq-03), a follow-up to
`CauchySchwarzOQ01OQ02OQ01.lean` (one Gram-Schmidt step is an orthogonal projector).

The parent file established, for a single non-zero vector `v`, that
`orthProj v x = (⟪v,x⟫/⟪v,v⟫) • v` is the orthogonal projector onto `span{v}`
(idempotent, complementary residual, exact norm). This file proves the **finite-rank
generalization**: the orthogonal projection onto the span of a finite orthonormal family
`e : Fin k → E` is the **sum of the rank-one projectors** over that family, together with
the **Parseval / Bessel equality on the subspace**. Zero axioms, zero sorries.

Concretely, writing `subProj e x = ∑ i, ⟪e i, x⟫ • e i` and
`S = span 𝕜 (range e)`:

* **Sum-of-rank-one-projectors identity** `S.starProjection x = ∑ i, ⟪e i, x⟫ • e i`
  (`subProj_eq_starProjection`) — the headline: Mathlib's orthogonal projection *is*
  the sum of the one-line projectors. Also as `orthogonalProjection`
  (`coe_orthogonalProjection_eq_subProj`).
* **Residual orthogonality** `⟪e j, x - subProj e x⟫ = 0` and, extended to the whole
  subspace, `∀ w ∈ S, ⟪x - subProj e x, w⟫ = 0`.
* **Parseval equality on `S`** `‖subProj e x‖² = ∑ i, ‖⟪e i, x⟫‖²`
  (`norm_subProj_sq`) — the attained (equality) case of Bessel's inequality, with the
  Bessel bound `‖subProj e x‖² ≤ ‖x‖²` as a corollary.
* **Idempotency** `subProj e (subProj e x) = subProj e x` and **reconstruction**
  `subProj e x + (x - subProj e x) = x`.
* **`k = 1` recovery** `subProj e x = ⟪e 0, x⟫ • e 0` — the one-term sum is exactly the
  parent's rank-one projector.

The subspace `S = span (range e)` is finite-dimensional, hence complete, so
`orthogonalProjection`/`starProjection` are well defined with no completeness hypothesis
on `E`. The scalar field `𝕜` is an arbitrary `RCLike` field (so `ℝ` and `ℂ` at once),
kept as an explicit argument of `subProj` as in the parent file.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped InnerProductSpace
open RCLike

namespace CauchySchwarzOQ01OQ02OQ01OQ03

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## The span of a finite family is finite-dimensional, hence complete -/

/-- The span of a finite family is finite-dimensional (so `orthogonalProjection` exists
without any completeness hypothesis on the ambient space `E`). -/
instance finiteDimensional_span_range {k : ℕ} (e : Fin k → E) :
    FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range e)) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range e)

/-- A finite-dimensional subspace over the complete field `𝕜` is complete, so it has an
orthogonal projection. -/
instance completeSpace_span_range {k : ℕ} (e : Fin k → E) :
    CompleteSpace (Submodule.span 𝕜 (Set.range e)) :=
  FiniteDimensional.complete 𝕜 _

/-! ## Definition: the finite-rank projection as a sum of rank-one projectors -/

/-- The finite-rank projection of `x` onto the family `e`: the sum of the rank-one
projectors `x ↦ ⟪e i, x⟫ • e i`. For an orthonormal `e` this is the orthogonal
projection onto `span (range e)` (`subProj_eq_starProjection`). -/
noncomputable def subProj {k : ℕ} (e : Fin k → E) (x : E) : E :=
  ∑ i, ⟪e i, x⟫_𝕜 • e i

/-! ## Membership and coordinates -/

/-- `subProj e x` lies in the span of the family. -/
theorem subProj_mem_span {k : ℕ} (e : Fin k → E) (x : E) :
    subProj 𝕜 e x ∈ Submodule.span 𝕜 (Set.range e) := by
  refine Submodule.sum_mem _ ?_
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- Coordinate extraction: for an orthonormal family, `⟪e j, subProj e x⟫ = ⟪e j, x⟫`.
The projection has the same coordinates as `x` along each `e j`. -/
theorem inner_subProj {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) (x : E) (j : Fin k) :
    ⟪e j, subProj 𝕜 e x⟫_𝕜 = ⟪e j, x⟫_𝕜 := by
  unfold subProj
  exact he.inner_right_fintype (fun i => ⟪e i, x⟫_𝕜) j

/-! ## Residual orthogonality -/

/-- The residual `x - subProj e x` is orthogonal to every basis vector `e j`. -/
theorem inner_residual {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) (x : E) (j : Fin k) :
    ⟪e j, x - subProj 𝕜 e x⟫_𝕜 = 0 := by
  rw [inner_sub_right, inner_subProj 𝕜 he x j, sub_self]

/-- The residual `x - subProj e x` is orthogonal to the *whole* subspace `span (range e)`,
not merely to each `e j`. This is the defining orthogonality property of the projection. -/
theorem residual_orthogonal_span {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) (x : E) :
    ∀ w ∈ Submodule.span 𝕜 (Set.range e), ⟪x - subProj 𝕜 e x, w⟫_𝕜 = 0 := by
  intro w hw
  refine Submodule.span_induction
    (p := fun w _ => ⟪x - subProj 𝕜 e x, w⟫_𝕜 = 0) ?_ ?_ ?_ ?_ hw
  · rintro y ⟨j, rfl⟩
    rw [inner_eq_zero_symm]
    exact inner_residual 𝕜 he x j
  · simp
  · intro a b _ _ pa pb
    rw [inner_add_right, pa, pb, add_zero]
  · intro c a _ pa
    rw [inner_smul_right, pa, mul_zero]

/-! ## Part I: The sum-of-rank-one-projectors identity (headline) -/

/-- **Main theorem.** For a finite orthonormal family `e`, the orthogonal projection onto
`S = span (range e)` equals the sum of the rank-one projectors:
`S.starProjection x = ∑ i, ⟪e i, x⟫ • e i`. This is the operator identity
`P_S = ∑ i, e_i e_i^*` (a finite-rank resolution of the identity). -/
theorem subProj_eq_starProjection {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) (x : E) :
    (Submodule.span 𝕜 (Set.range e)).starProjection x = subProj 𝕜 e x :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (subProj_mem_span 𝕜 e x) (residual_orthogonal_span 𝕜 he x)

/-- The same identity phrased with the subspace-valued `orthogonalProjection`. -/
theorem coe_orthogonalProjection_eq_subProj {k : ℕ} {e : Fin k → E}
    (he : Orthonormal 𝕜 e) (x : E) :
    (((Submodule.span 𝕜 (Set.range e)).orthogonalProjection x : Submodule.span 𝕜 (Set.range e)) : E)
      = subProj 𝕜 e x := by
  rw [Submodule.coe_orthogonalProjection_apply]
  exact subProj_eq_starProjection 𝕜 he x

/-! ## Part II: Parseval / Bessel equality on the subspace -/

/-- **Parseval equality on `S`.** The squared norm of the projection is the sum of the
squared coordinate moduli: `‖subProj e x‖² = ∑ i, ‖⟪e i, x⟫‖²`. This is the attained
(equality) form of Bessel's inequality, restricted to the subspace `S`. -/
theorem norm_subProj_sq {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) (x : E) :
    ‖subProj 𝕜 e x‖ ^ 2 = ∑ i, ‖⟪e i, x⟫_𝕜‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner 𝕜]
  unfold subProj
  rw [he.inner_sum (fun i => ⟪e i, x⟫_𝕜) (fun i => ⟪e i, x⟫_𝕜) Finset.univ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_mul]
  norm_cast

/-- **Bessel's inequality** as a corollary: `‖subProj e x‖² ≤ ‖x‖²`. -/
theorem norm_subProj_sq_le {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) (x : E) :
    ‖subProj 𝕜 e x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_subProj_sq 𝕜 he x]
  exact he.sum_inner_products_le x

/-! ## Part III: Idempotency and reconstruction (projector axioms) -/

/-- **Idempotency** `P² = P`: `subProj e (subProj e x) = subProj e x`. -/
theorem subProj_idempotent {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) (x : E) :
    subProj 𝕜 e (subProj 𝕜 e x) = subProj 𝕜 e x := by
  simp only [subProj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he.inner_right_fintype (fun j => ⟪e j, x⟫_𝕜) i]

/-- **Reconstruction** `P + (1 − P) = id`: the projection and residual sum to `x`. -/
theorem subProj_add_residual {k : ℕ} (e : Fin k → E) (x : E) :
    subProj 𝕜 e x + (x - subProj 𝕜 e x) = x := by
  abel

/-! ## Part IV: The `k = 1` case recovers the parent's rank-one projector -/

/-- For a single-vector family, `subProj` is the one-term sum `⟪e 0, x⟫ • e 0`, i.e. the
parent file's rank-one orthogonal projector onto the line `span{e 0}`. -/
theorem subProj_one (e : Fin 1 → E) (x : E) :
    subProj 𝕜 e x = ⟪e 0, x⟫_𝕜 • e 0 := by
  simp [subProj]

/-! ## Part V: Capstone -/

/-- **Summary.** For a finite orthonormal family `e` with span `S`, the map
`subProj e = ∑ i ⟪e i, ·⟫ • e i` is the orthogonal projection onto `S`: it agrees with
Mathlib's `starProjection`, its residual is orthogonal to `S`, it satisfies the Parseval
equality on `S`, and it is idempotent. -/
theorem subProj_is_orthogonal_projection {k : ℕ} {e : Fin k → E} (he : Orthonormal 𝕜 e) :
    (∀ x : E, (Submodule.span 𝕜 (Set.range e)).starProjection x = subProj 𝕜 e x) ∧
    (∀ x : E, ∀ w ∈ Submodule.span 𝕜 (Set.range e), ⟪x - subProj 𝕜 e x, w⟫_𝕜 = 0) ∧
    (∀ x : E, ‖subProj 𝕜 e x‖ ^ 2 = ∑ i, ‖⟪e i, x⟫_𝕜‖ ^ 2) ∧
    (∀ x : E, subProj 𝕜 e (subProj 𝕜 e x) = subProj 𝕜 e x) :=
  ⟨fun x => subProj_eq_starProjection 𝕜 he x,
   fun x => residual_orthogonal_span 𝕜 he x,
   fun x => norm_subProj_sq 𝕜 he x,
   fun x => subProj_idempotent 𝕜 he x⟩

end CauchySchwarzOQ01OQ02OQ01OQ03
