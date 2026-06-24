import Mathlib

/-
# The Gramian as a squared volume: `√(det gram v)` is the parallelepiped volume

For a finite family of vectors `v : ι → F` in a real inner product space, the parent entry
`GramLinearIndependenceOQ01` established the **Gramian criterion**: the Gram determinant
`det (gram ℝ v)` is nonnegative and is strictly positive exactly when `v` is linearly
independent.  The sibling entry `…OQ01OQ01` quantified it from above (Hadamard's inequality
`det (gram ℝ v) ≤ ∏ ‖v i‖²`).  This entry supplies the **geometric meaning** of the Gramian,
answering the parent's second open question:

> Identify `√(det gram v)` with the volume of the parallelepiped spanned by `v`, connecting
> the Gramian criterion to the volume / exterior-power picture of linear independence.

The headline result is

* `volume_parallelepiped_eq_sqrt_det_gram` :
  `volume (parallelepiped v) = ENNReal.ofReal (√(det (gram ℝ v)))`

for a top-dimensional family in a finite-dimensional inner product space (`b` ranges over an
orthonormal basis indexed by `ι`, equivalently `finrank ℝ F = card ι`), together with the
concrete instance `volume_parallelepiped_euclidean` on `EuclideanSpace ℝ ι`.

Mathlib has the two ends of the bridge — `Basis.det`, the coordinate machinery, and
`MeasureTheory.Measure.addHaar_parallelepiped` (`b.addHaar (parallelepiped v) = ofReal |b.det v|`),
together with `OrthonormalBasis.addHaar_eq_volume` — but **not** the identification of the
volume with the Gramian.  The link is the matrix factorisation in an orthonormal basis:

1. `gram_eq_transpose_mul` : in an orthonormal basis `b`, writing `B := b.toMatrix v` for the
   coordinate matrix `B k i = ⟪b k, v i⟫`, completeness gives `gram ℝ v = Bᵀ * B`.
2. `det_gram_eq_basis_det_sq` : hence `det (gram ℝ v) = (b.det v)²`, the **squared** signed
   volume.
3. `sqrt_det_gram_eq_abs_det` : so `√(det (gram ℝ v)) = |b.det v|`, the unsigned volume of the
   coordinate determinant — and `addHaar_parallelepiped` turns `|b.det v|` into the measure of
   the parallelepiped.

As a corollary, `volume_parallelepiped_pos_iff_linearIndependent` recovers the parent's
criterion in geometric form: the parallelepiped has positive volume iff `v` is independent.

Everything is fully machine-checked with no `sorry` and no extra axioms.
-/

namespace GramLinearIndependenceOQ01OQ02

open Matrix Finset MeasureTheory
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ## The Gram matrix as `Bᵀ B` in an orthonormal basis -/

omit [DecidableEq ι] in
/-- In an orthonormal basis `b`, the Gram matrix of `v` factors through the coordinate matrix
`B := b.toMatrix v` (with `B k i = ⟪b k, v i⟫`) as `gram ℝ v = Bᵀ * B`.  This is exactly
completeness of the orthonormal basis: `⟪v i, v j⟫ = ∑ k, ⟪b k, v i⟫ ⟪b k, v j⟫`. -/
theorem gram_eq_transpose_mul (b : OrthonormalBasis ι ℝ F) (v : ι → F) :
    gram ℝ v = (b.toBasis.toMatrix v)ᵀ * (b.toBasis.toMatrix v) := by
  ext i j
  simp only [gram_apply, Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  rw [← b.sum_inner_mul_inner (v i) (v j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm (v i) (b k)]

/-! ## The Gramian is the squared signed volume -/

/-- The Gram determinant equals the square of the basis determinant `b.det v` (the signed
volume of `v` read in the orthonormal basis `b`): `det (gram ℝ v) = (b.det v)²`. -/
theorem det_gram_eq_basis_det_sq (b : OrthonormalBasis ι ℝ F) (v : ι → F) :
    (gram ℝ v).det = (b.toBasis.det v) ^ 2 := by
  rw [gram_eq_transpose_mul b v, Matrix.det_mul, Matrix.det_transpose, Module.Basis.det_apply]
  ring

/-- The square root of the Gramian is the unsigned volume `|b.det v|`. -/
theorem sqrt_det_gram_eq_abs_det (b : OrthonormalBasis ι ℝ F) (v : ι → F) :
    Real.sqrt ((gram ℝ v).det) = |b.toBasis.det v| := by
  rw [det_gram_eq_basis_det_sq b v, Real.sqrt_sq_eq_abs]

/-! ## The volume identity -/

/-- **The Gramian is a squared volume.** For a top-dimensional family `v : ι → F` in a
finite-dimensional real inner product space (`b` an orthonormal basis indexed by `ι`), the
Lebesgue–Haar volume of the parallelepiped spanned by `v` is the square root of the Gram
determinant:
`volume (parallelepiped v) = ENNReal.ofReal (√(det (gram ℝ v)))`. -/
theorem volume_parallelepiped_eq_sqrt_det_gram
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (b : OrthonormalBasis ι ℝ F) (v : ι → F) :
    volume (parallelepiped v) = ENNReal.ofReal (Real.sqrt ((gram ℝ v).det)) := by
  have hvol := MeasureTheory.Measure.addHaar_parallelepiped b.toBasis v
  rw [b.addHaar_eq_volume] at hvol
  rw [hvol, sqrt_det_gram_eq_abs_det b v]

/-- Concrete form of the volume identity on `EuclideanSpace ℝ ι`, where the standard basis
`EuclideanSpace.basisFun` is orthonormal and all measure-theoretic instances are canonical. -/
theorem volume_parallelepiped_euclidean (v : ι → EuclideanSpace ℝ ι) :
    volume (parallelepiped v) = ENNReal.ofReal (Real.sqrt ((gram ℝ v).det)) :=
  volume_parallelepiped_eq_sqrt_det_gram (EuclideanSpace.basisFun ι ℝ) v

/-! ## Geometric form of the linear-independence criterion -/

/-- The parallelepiped spanned by `v` has positive volume iff `v` is linearly independent —
the parent's Gramian criterion (`det (gram ℝ v) > 0 ↔ LinearIndependent`) read geometrically.
The Gram matrix is positive **definite** exactly when `v` is independent (Mathlib's
`posDef_gram_iff_linearIndependent`), and a positive definite matrix has positive determinant,
which by the volume identity is the squared volume. -/
theorem volume_parallelepiped_pos_iff_linearIndependent
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (b : OrthonormalBasis ι ℝ F) (v : ι → F) :
    0 < volume (parallelepiped v) ↔ LinearIndependent ℝ v := by
  rw [volume_parallelepiped_eq_sqrt_det_gram b v, ENNReal.ofReal_pos, Real.sqrt_pos,
    ← Matrix.posDef_gram_iff_linearIndependent]
  constructor
  · intro hdpos
    rw [(Matrix.posSemidef_gram ℝ v).posDef_iff_isUnit]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdpos.ne')
  · exact fun hpd => hpd.det_pos

end GramLinearIndependenceOQ01OQ02
