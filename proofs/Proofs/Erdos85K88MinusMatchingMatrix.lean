import Proofs.Erdos85EightFiberTraceTerminal

/-! # The canonical `K_{8,8}` minus a perfect matching matrix

Vertices are an index in `Fin 8` and a Boolean side.  Opposite-side vertices
are adjacent except when their indices agree.  This explicit sixteen-vertex
model is convenient as the target of a component relabelling.
-/

namespace Erdos85

noncomputable section

abbrev K88Vertex := Fin 8 × Bool

/-- Same bipartition side in the canonical model. -/
def k88SameSide (x y : K88Vertex) : Prop := x.2 = y.2

instance : DecidableRel k88SameSide := by
  intro x y
  unfold k88SameSide
  infer_instance

/-- Rational adjacency matrix of `K_{8,8}` with the index-matching removed. -/
def k88MinusMatchingMatrix : Matrix K88Vertex K88Vertex ℚ := fun x y =>
  if x.2 ≠ y.2 ∧ x.1 ≠ y.1 then 1 else 0

/-- Every same-side class in the canonical model has eight vertices. -/
theorem k88SameSide_fiber_card (x : K88Vertex) :
    ((Finset.univ : Finset K88Vertex).filter fun y => k88SameSide x y).card = 8 := by
  rcases x with ⟨i, b⟩
  fin_cases b <;> native_decide +revert

/-- The complete square table of the canonical model.  This single matrix
identity simultaneously says degree seven on the diagonal, codegree six for
distinct vertices on one side, and codegree zero across the sides. -/
theorem k88MinusMatchingMatrix_sq :
    k88MinusMatchingMatrix * k88MinusMatchingMatrix =
      1 + (6 : ℚ) • relationClassMatrix k88SameSide := by
  native_decide

/-- The canonical same-side matrix is an eight-fiber projection. -/
theorem k88SameSideMatrix_sq :
    relationClassMatrix k88SameSide * relationClassMatrix k88SameSide =
      (8 : ℚ) • relationClassMatrix k88SameSide := by
  exact relationClassMatrix_mul_self_eq_eight k88SameSide
    (by simp [k88SameSide])
    (by simp [k88SameSide])
    k88SameSide_fiber_card

/-- The square table transports back along an arbitrary vertex relabelling.
This is the graph-classification interface: it suffices to exhibit an
equivalence under which the candidate matrix becomes the canonical one. -/
theorem matrix_sq_eq_one_add_six_of_reindex_eq_k88MinusMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : Matrix V V ℚ) (e : V ≃ K88Vertex)
    (hD : Matrix.reindex e e D = k88MinusMatchingMatrix) :
    D * D = 1 + (6 : ℚ) •
      relationClassMatrix (fun x y : V => k88SameSide (e x) (e y)) := by
  apply (Matrix.reindex e e).injective
  change (Matrix.reindexAlgEquiv ℚ ℚ e) (D * D) =
    (Matrix.reindexAlgEquiv ℚ ℚ e)
      (1 + (6 : ℚ) •
        relationClassMatrix (fun x y : V => k88SameSide (e x) (e y)))
  change (Matrix.reindexAlgEquiv ℚ ℚ e) D =
    k88MinusMatchingMatrix at hD
  rw [map_mul, hD, k88MinusMatchingMatrix_sq]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Matrix.reindex_apply, relationClassMatrix, k88SameSide]
  · have hesymm : e.symm x ≠ e.symm y := by
      intro h
      exact hxy (e.symm.injective h)
    simp [Matrix.reindex_apply, relationClassMatrix, k88SameSide,
      hxy, hesymm]

/-- The pulled-back same-side matrix remains an eight-fiber projection. -/
theorem reindexedK88SameSideMatrix_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (e : V ≃ K88Vertex) :
    let P : Matrix V V ℚ :=
      relationClassMatrix (fun x y : V => k88SameSide (e x) (e y))
    P * P = (8 : ℚ) • P := by
  dsimp only
  apply (Matrix.reindex e e).injective
  change (Matrix.reindexAlgEquiv ℚ ℚ e)
      (relationClassMatrix (fun x y : V => k88SameSide (e x) (e y)) *
       relationClassMatrix (fun x y : V => k88SameSide (e x) (e y))) =
    (Matrix.reindexAlgEquiv ℚ ℚ e)
      ((8 : ℚ) • relationClassMatrix
        (fun x y : V => k88SameSide (e x) (e y)))
  rw [map_mul, map_smul]
  have hP : (Matrix.reindexAlgEquiv ℚ ℚ e)
      (relationClassMatrix (fun x y : V => k88SameSide (e x) (e y))) =
      relationClassMatrix k88SameSide := by
    ext x y
    simp [Matrix.reindex_apply, relationClassMatrix, k88SameSide]
  rw [hP, k88SameSideMatrix_sq]

/-- The annihilator itself is invariant under a supplied canonical
relabeling, without requiring clients to reason about conjugate linear maps. -/
theorem aeval_bipartite_defect_polynomial_eq_zero_of_reindex_eq_k88
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : Matrix V V ℚ) (e : V ≃ K88Vertex)
    (hD : Matrix.reindex e e D = k88MinusMatchingMatrix) :
    Polynomial.aeval (Matrix.toLin' D)
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0 := by
  let P : Matrix V V ℚ :=
    relationClassMatrix (fun x y : V => k88SameSide (e x) (e y))
  have hDmatrix : D * D = 1 + (6 : ℚ) • P :=
    matrix_sq_eq_one_add_six_of_reindex_eq_k88MinusMatching D e hD
  have hPmatrix : P * P = (8 : ℚ) • P := reindexedK88SameSideMatrix_sq e
  have hDlin : Matrix.toLin' D * Matrix.toLin' D =
      1 + (6 : ℚ) • Matrix.toLin' P := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_add,
      map_smul, Matrix.toLin'_one, Module.End.one_eq_id] using
      congrArg Matrix.toLin' hDmatrix
  have hPlin : Matrix.toLin' P * Matrix.toLin' P =
      (8 : ℚ) • Matrix.toLin' P := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_smul] using
      congrArg Matrix.toLin' hPmatrix
  exact aeval_bipartite_defect_polynomial_eq_zero_of_fourth
    (Matrix.toLin' D)
    (bipartite_defect_fourth_eq_zero_of_square_projection
      (Matrix.toLin' D) (Matrix.toLin' P) hDlin hPlin)

/-- Consequently the canonical defect matrix has exactly the four expected
linear factors. -/
theorem k88MinusMatching_aeval_polynomial_eq_zero :
    Polynomial.aeval (Matrix.toLin' k88MinusMatchingMatrix)
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0 := by
  have hDlin :
      Matrix.toLin' k88MinusMatchingMatrix *
          Matrix.toLin' k88MinusMatchingMatrix =
        1 + (6 : ℚ) • Matrix.toLin' (relationClassMatrix k88SameSide) := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_add,
      map_smul, Matrix.toLin'_one, Module.End.one_eq_id] using
      congrArg Matrix.toLin' k88MinusMatchingMatrix_sq
  have hPlin :
      Matrix.toLin' (relationClassMatrix k88SameSide) *
          Matrix.toLin' (relationClassMatrix k88SameSide) =
        (8 : ℚ) • Matrix.toLin' (relationClassMatrix k88SameSide) := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_smul] using
      congrArg Matrix.toLin' k88SameSideMatrix_sq
  exact aeval_bipartite_defect_polynomial_eq_zero_of_fourth
    (Matrix.toLin' k88MinusMatchingMatrix)
    (bipartite_defect_fourth_eq_zero_of_square_projection
      (Matrix.toLin' k88MinusMatchingMatrix)
      (Matrix.toLin' (relationClassMatrix k88SameSide)) hDlin hPlin)

/-- Trace terminal specialized to the canonical relabelled component model. -/
theorem false_of_k88MinusMatching_trace_data
    (S : Matrix K88Vertex K88Vertex ℚ)
    (hcomm : Matrix.toLin' S * Matrix.toLin' k88MinusMatchingMatrix =
      Matrix.toLin' k88MinusMatchingMatrix * Matrix.toLin' S)
    (htotal : LinearMap.trace ℚ (K88Vertex → ℚ) (Matrix.toLin' S) = 0)
    (h7 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S)
        (Matrix.toLin' k88MinusMatchingMatrix) hcomm
        (Polynomial.X - Polynomial.C (7 : ℚ))) = 8)
    (h1 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S)
        (Matrix.toLin' k88MinusMatchingMatrix) hcomm
        (Polynomial.X - Polynomial.C (1 : ℚ))) = 0)
    (hm1 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S)
        (Matrix.toLin' k88MinusMatchingMatrix) hcomm
        (Polynomial.X - Polynomial.C (-1 : ℚ))) = 0)
    (hm7 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S)
        (Matrix.toLin' k88MinusMatchingMatrix) hcomm
        (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0) : False := by
  exact false_of_bipartite_defect_four_sector_traces
    (Matrix.toLin' S) (Matrix.toLin' k88MinusMatchingMatrix) hcomm
    k88MinusMatching_aeval_polynomial_eq_zero htotal h7 h1 hm1 hm7

end

end Erdos85
