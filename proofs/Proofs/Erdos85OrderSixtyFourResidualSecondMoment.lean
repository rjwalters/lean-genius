import Proofs.Erdos85OrderSixtyFourResidualTrace
import Proofs.Erdos85SquareOrderAdjacencyMoments

/-! # The residual adjacency second moment at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The component-mean-zero sector carries adjacency second moment `448`.
The ambient second moment is `512`, while normalized component averaging
sees only the principal adjacency eigenvalue `8`, contributing `64`. -/
theorem orderSixtyFour_residual_defect_sector_secondMoment_eq_fourFortyEight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    ∃ hW : ∀ x ∈ LinearMap.ker
        (defectComponentNormalizedProjection
          (secondOrderDefectGraph G)).toLin',
        (G.adjMatrix ℚ).toLin' x ∈ LinearMap.ker
          (defectComponentNormalizedProjection
            (secondOrderDefectGraph G)).toLin',
      LinearMap.trace ℚ _
        ((G.adjMatrix ℚ).toLin'.restrict hW *
          (G.adjMatrix ℚ).toLin'.restrict hW) = 448 := by
  classical
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let P := defectComponentNormalizedProjection D
  let J8 : Matrix (Fin 64) (Fin 64) ℚ :=
    Matrix.of fun _ _ => (8 : ℚ)⁻¹
  let S := A.toLin' * A.toLin'
  have hPmatrix : P * P = P :=
    defectComponentNormalizedProjection_mul_self D
  have hPid : IsIdempotentElem P.toLin' := by
    simpa only [IsIdempotentElem, Module.End.mul_eq_comp,
      Matrix.toLin'_mul] using congrArg Matrix.toLin' hPmatrix
  have hAP : A * P = J8 :=
    orderSixtyFour_adj_mul_defectComponentNormalizedProjection
      G hfree hmin hcover
  have hPA : P * A = J8 := by
    have ht := congrArg Matrix.transpose hAP
    have hJ8 : J8.transpose = J8 := by ext x y; rfl
    rw [hJ8] at ht
    simpa only [Matrix.transpose_mul, A, P,
      G.isSymm_adjMatrix.eq,
      (defectComponentNormalizedProjection_isSymm D).eq] using ht
  have hcommA : A.toLin' * P.toLin' = P.toLin' * A.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' (hAP.trans hPA.symm)
  have hcommS : S * P.toLin' = P.toLin' * S := by
    dsimp only [S]
    calc
      (A.toLin' * A.toLin') * P.toLin' =
          A.toLin' * (A.toLin' * P.toLin') := mul_assoc _ _ _
      _ = A.toLin' * (P.toLin' * A.toLin') := by rw [hcommA]
      _ = (A.toLin' * P.toLin') * A.toLin' := (mul_assoc _ _ _).symm
      _ = (P.toLin' * A.toLin') * A.toLin' := by rw [hcommA]
      _ = P.toLin' * (A.toLin' * A.toLin') := mul_assoc _ _ _
  let U := LinearMap.range P.toLin'
  let W := LinearMap.ker P.toLin'
  let hU := mapsTo_range_of_commute S P.toLin' hcommS
  let hW := mapsTo_ker_of_commute A.toLin' P.toLin' hcommA
  let hWS := mapsTo_ker_of_commute S P.toLin' hcommS
  have htrace : LinearMap.trace ℚ (Fin 64 → ℚ) S = 512 := by
    rw [show S = (A * A).toLin' by
      simp only [S, Module.End.mul_eq_comp, Matrix.toLin'_mul],
      Matrix.trace_toLin'_eq]
    change Matrix.trace (G.adjMatrix ℚ * G.adjMatrix ℚ) = 512
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    have hentry (x : Fin 64) :
        (G.adjMatrix ℚ * G.adjMatrix ℚ) x x = 8 := by
      rw [G.adjMatrix_mul_self_apply_self]
      norm_num [orderSixtyFour_regular_of_tightCover
        G hfree hmin hcover x]
    simp_rw [hentry]
    norm_num
  have hUtrace : LinearMap.trace ℚ U (S.restrict hU) = 64 := by
    rw [trace_restrict_range_eq_trace_mul_of_idempotent
      S P.toLin' hPid hcommS]
    rw [show S * P.toLin' = (A * (A * P)).toLin' by
      have hm := congrArg Matrix.toLin' (Matrix.mul_assoc A A P)
      simpa only [S, Module.End.mul_eq_comp, Matrix.toLin'_mul] using hm,
      hAP, Matrix.trace_toLin'_eq]
    rw [Matrix.trace]
    have hdiag (x : Fin 64) : (A * J8).diag x = 1 := by
      rw [Matrix.diag_apply, Matrix.mul_apply]
      change (∑ y, G.adjMatrix ℚ x y * (8 : ℚ)⁻¹) = 1
      rw [← Finset.sum_mul]
      simp only [SimpleGraph.adjMatrix_apply]
      rw [Finset.sum_boole]
      have hfilt : (Finset.univ : Finset (Fin 64)).filter
          (fun y => G.Adj x y) = G.neighborFinset x := by
        ext y
        simp [SimpleGraph.mem_neighborFinset]
      rw [hfilt, G.card_neighborFinset_eq_degree]
      rw [orderSixtyFour_regular_of_tightCover G hfree hmin hcover x]
      norm_num
    simp_rw [hdiag]
    norm_num
  have hsplit := trace_eq_add_trace_restrict_of_isCompl
    S U W (LinearMap.IsIdempotentElem.isCompl hPid) hU hWS
  refine ⟨hW, ?_⟩
  have hsquare :
      A.toLin'.restrict hW * A.toLin'.restrict hW = S.restrict hWS := by
    ext x
    rfl
  rw [hsquare]
  rw [htrace, hUtrace] at hsplit
  linarith

end

end Erdos85
