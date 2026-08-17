import Proofs.Erdos85OrderSixtyFourSevenComponentPairPacking

/-! # The residual defect-Laplacian determinant is a square -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem card_filter_component'
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    ((Finset.univ : Finset (Fin 64)).filter
      (fun x => D.connectedComponentMk x = c)).card = c.supp.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- Averaging within defect components preserves the total coordinate sum. -/
theorem ratOnesMatrix_mul_defectComponentNormalizedProjection
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    ratOnesMatrix (Fin 64) * defectComponentNormalizedProjection D =
      ratOnesMatrix (Fin 64) := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [ratOnesMatrix, Matrix.of_apply, one_mul,
    defectComponentNormalizedProjection]
  calc
    (∑ z, if D.connectedComponentMk z = D.connectedComponentMk y then
        ((D.connectedComponentMk z).supp.ncard : ℚ)⁻¹ else 0) =
      ∑ _z ∈ (Finset.univ : Finset (Fin 64)).filter
        (fun z => D.connectedComponentMk z = D.connectedComponentMk y),
          ((D.connectedComponentMk y).supp.ncard : ℚ)⁻¹ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : D.connectedComponentMk z = D.connectedComponentMk y
      · rw [if_pos hz, hz]
        simp
      · rw [if_neg hz]
        simp [hz]
    _ = 1 := by
      rw [Finset.sum_const, card_filter_component', nsmul_eq_mul]
      have hp : (D.connectedComponentMk y).supp.ncard ≠ 0 :=
        Nat.ne_of_gt (D.connectedComponentMk y).nonempty_supp.ncard_pos
      field_simp

/-- On component-mean-zero vectors, the defect Laplacian is exactly the
square of adjacency.  Consequently its invariant determinant is a rational
square. -/
theorem orderSixtyFour_residual_laplacian_det_eq_adjacency_det_sq
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    ∃ (hW : ∀ x ∈ LinearMap.ker
          (defectComponentNormalizedProjection
            (secondOrderDefectGraph G)).toLin',
          (G.adjMatrix ℚ).toLin' x ∈ LinearMap.ker
            (defectComponentNormalizedProjection
              (secondOrderDefectGraph G)).toLin')
      (hL : ∀ x ∈ LinearMap.ker
          (defectComponentNormalizedProjection
            (secondOrderDefectGraph G)).toLin',
          ((secondOrderDefectGraph G).lapMatrix ℚ).toLin' x ∈
            LinearMap.ker (defectComponentNormalizedProjection
              (secondOrderDefectGraph G)).toLin'),
      LinearMap.det
          (((secondOrderDefectGraph G).lapMatrix ℚ).toLin'.restrict hL) =
        LinearMap.det ((G.adjMatrix ℚ).toLin'.restrict hW) ^ 2 := by
  classical
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let P := defectComponentNormalizedProjection D
  let L := D.lapMatrix ℚ
  let J := ratOnesMatrix (Fin 64)
  have hAP : A * P = Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by
    exact orderSixtyFour_adj_mul_defectComponentNormalizedProjection
      G hfree hmin hcover
  have hPA : P * A = Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by
    have ht := congrArg Matrix.transpose hAP
    have hconst : (Matrix.of (fun _ _ => (8 : ℚ)⁻¹) :
        Matrix (Fin 64) (Fin 64) ℚ).transpose =
        Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by ext x y; rfl
    rw [hconst] at ht
    simpa only [Matrix.transpose_mul, A, P,
      G.isSymm_adjMatrix.eq,
      (defectComponentNormalizedProjection_isSymm D).eq] using ht
  have hcommM : A * P = P * A := hAP.trans hPA.symm
  have hcomm : A.toLin' * P.toLin' = P.toLin' * A.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  let W := LinearMap.ker P.toLin'
  let hW := mapsTo_ker_of_commute A.toLin' P.toLin' hcomm
  have hJP : J * P = J :=
    ratOnesMatrix_mul_defectComponentNormalizedProjection D
  have hJzero : ∀ v : W, J.mulVec (v : Fin 64 → ℚ) = 0 := by
    intro v
    have hh := congrArg (fun M => M.mulVec (v : Fin 64 → ℚ)) hJP
    have hv0 : P.mulVec (v : Fin 64 → ℚ) = 0 := v.property
    rw [← Matrix.mulVec_mulVec, hv0, Matrix.mulVec_zero] at hh
    exact hh.symm
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hDreg : ∀ x : Fin 64, D.degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
  have hLmat : L = (7 : ℚ) • (1 : Matrix (Fin 64) (Fin 64) ℚ) -
      D.adjMatrix ℚ := by
    ext x y
    simp only [L, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst y
      simp [hDreg x, SimpleGraph.adjMatrix_apply]
    · simp [hxy, SimpleGraph.adjMatrix_apply]
  have hsq0 := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
    G hfree hreg
  have hsq : A * A = L + J := by
    rw [hLmat]
    dsimp only [A, D, J]
    rw [hsq0]
    module
  have hL : ∀ x ∈ W, L.toLin' x ∈ W := by
    intro v hv
    have hAv : A.toLin' v ∈ W := hW v hv
    have hAAv : A.toLin' (A.toLin' v) ∈ W := hW _ hAv
    have heq := congrArg (fun M => M.mulVec (v : Fin 64 → ℚ)) hsq
    rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, hJzero ⟨v, hv⟩,
      add_zero] at heq
    change A.mulVec (A.mulVec v) ∈ W at hAAv
    rw [heq] at hAAv
    exact hAAv
  refine ⟨hW, hL, ?_⟩
  have hrestr :
      (A.toLin'.restrict hW) * (A.toLin'.restrict hW) =
        L.toLin'.restrict hL := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have heq := congrArg (fun M => M.mulVec (v : Fin 64 → ℚ)) hsq
    rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, hJzero v, add_zero] at heq
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply,
      Module.End.mul_apply] using heq
  rw [← hrestr, map_mul, pow_two]

end

end Erdos85
