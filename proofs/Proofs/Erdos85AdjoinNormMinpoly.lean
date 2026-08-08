import Proofs.Erdos85BoundaryOrbitMinpoly
import Mathlib.RingTheory.Norm.Basic

/-!
# Norm of a translated simple generator

For an integral element `μ`, multiplication by `μ` on `ℚ(μ)` has
characteristic polynomial `minpoly ℚ μ`.  Taking the determinant of
`cI - Mμ` therefore identifies the field norm of `c - μ` with evaluation
of that minimal polynomial at `c`.
-/

open IntermediateField

namespace Erdos85

noncomputable section

variable {L : Type*} [Field L] [CharZero L]

/-- **Translated-generator norm identity.**  The norm from `ℚ(μ)` of
`c - μ` is the value at `c` of the rational minimal polynomial of `μ`.
The sign convention is built into using `c - μ` (rather than `μ - c`). -/
theorem norm_rat_sub_generator_eq_minpoly_eval
    (μ : L) (c : ℚ) (hμ : IsIntegral ℚ μ) :
    Algebra.norm ℚ
        (⟨(c : L) - μ, rat_sub_mem_adjoin c μ⟩ :
          IntermediateField.adjoin ℚ {μ}) =
      (minpoly ℚ μ).eval c := by
  let E := IntermediateField.adjoin ℚ {μ}
  let pb : PowerBasis ℚ E := IntermediateField.adjoin.powerBasis hμ
  let g : E := IntermediateField.AdjoinSimple.gen ℚ μ
  have hg : (g : L) = μ := IntermediateField.AdjoinSimple.algebraMap_gen ℚ μ
  have hpbgen : pb.gen = g := by
    exact IntermediateField.adjoin.powerBasis_gen hμ
  have hx :
      (⟨(c : L) - μ, rat_sub_mem_adjoin c μ⟩ : E) =
        algebraMap ℚ E c - pb.gen := by
    apply Subtype.ext
    simp [E, hpbgen, g, hg]
  rw [hx, Algebra.norm_eq_matrix_det pb.basis]
  have hmatrix :
      Algebra.leftMulMatrix pb.basis (algebraMap ℚ E c - pb.gen) =
        Matrix.scalar _ c - Algebra.leftMulMatrix pb.basis pb.gen := by
    rw [map_sub, (Algebra.leftMulMatrix pb.basis).commutes c]
    rfl
  rw [hmatrix, ← Matrix.eval_charpoly,
    charpoly_leftMulMatrix pb, hpbgen]
  have hmp : minpoly ℚ g = minpoly ℚ μ := by
    rw [← hg]
    exact (minpoly.algebraMap_eq (A := ℚ)
      (algebraMap E L).injective g).symm
  exact congrArg (fun p : Polynomial ℚ ↦ p.eval c) hmp

/-- Square-certificate form of the norm identity. -/
theorem norm_rat_sub_generator_isSquare_iff_minpoly_eval_isSquare
    (μ : L) (c : ℚ) (hμ : IsIntegral ℚ μ) :
    IsSquare (Algebra.norm ℚ
        (⟨(c : L) - μ, rat_sub_mem_adjoin c μ⟩ :
          IntermediateField.adjoin ℚ {μ})) ↔
      IsSquare ((minpoly ℚ μ).eval c) := by
  rw [norm_rat_sub_generator_eq_minpoly_eval μ c hμ]

/-- A nonsquare minimal-polynomial evaluation rules out a square root in
the simple field, in the exact form consumed by the boundary orbit package. -/
theorem not_exists_sq_root_of_minpoly_eval_not_isSquare
    (μ : L) (c : ℚ) (hμ : IsIntegral ℚ μ)
    (hvalue : ¬ IsSquare ((minpoly ℚ μ).eval c)) :
    ¬ ∃ t ∈ IntermediateField.adjoin ℚ {μ},
      t * t = (c : L) - μ := by
  apply not_exists_sq_root_of_norm_not_isSquare μ c hμ
  rwa [norm_rat_sub_generator_eq_minpoly_eval μ c hμ]

end

end Erdos85
