import Proofs.Erdos85OrderSixtyFourSevenComponentLocal

/-! # Adjacency is injective off the principal defect sector at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem card_filter_component
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    ((Finset.univ : Finset (Fin 64)).filter
      (fun x => D.connectedComponentMk x = c)).card = c.supp.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- A vector in the kernel of normalized component averaging which is killed
by adjacency must vanish. -/
theorem orderSixtyFour_residual_adjacency_injective
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
      Function.Injective ((G.adjMatrix ℚ).toLin'.restrict hW) := by
  classical
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let P := defectComponentNormalizedProjection D
  let J : Matrix (Fin 64) (Fin 64) ℚ := ratOnesMatrix (Fin 64)
  let J8 : Matrix (Fin 64) (Fin 64) ℚ :=
    Matrix.of fun _ _ => (8 : ℚ)⁻¹
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
  have hcommM : A * P = P * A := hAP.trans hPA.symm
  have hcomm : A.toLin' * P.toLin' = P.toLin' * A.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  let W := LinearMap.ker P.toLin'
  let hW := mapsTo_ker_of_commute A.toLin' P.toLin' hcomm
  refine ⟨hW, ?_⟩
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    have hvA : A.toLin'.restrict hW v = 0 := LinearMap.mem_ker.mp hv
    apply Subtype.ext
    have hvA0 : A.mulVec (v : Fin 64 → ℚ) = 0 := by
      simpa [LinearMap.restrict_apply, A, Matrix.toLin'_apply] using
        congrArg Subtype.val hvA
    have hvP0 : P.mulVec (v : Fin 64 → ℚ) = 0 := v.property
    have hJ8v : J8.mulVec (v : Fin 64 → ℚ) = 0 := by
      have hh := congrArg (fun M => M.mulVec (v : Fin 64 → ℚ)) hPA
      rw [← Matrix.mulVec_mulVec, hvA0, Matrix.mulVec_zero] at hh
      exact hh.symm
    have hJv : J.mulVec (v : Fin 64 → ℚ) = 0 := by
      have hJJ8 : J = (8 : ℚ) • J8 := by
        ext x y
        norm_num [J, J8, ratOnesMatrix]
      rw [hJJ8, Matrix.smul_mulVec, hJ8v, smul_zero]
    have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
    have hDreg : ∀ x : Fin 64, D.degree x = 7 :=
      (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
    have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
      G hfree hreg
    have hvD : (D.adjMatrix ℚ).mulVec (v : Fin 64 → ℚ) =
        (7 : ℚ) • (v : Fin 64 → ℚ) := by
      have hh := congrArg (fun M => M.mulVec (v : Fin 64 → ℚ)) hsq
      rw [← Matrix.mulVec_mulVec, hvA0, Matrix.mulVec_zero] at hh
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec] at hh
      rw [hJv] at hh
      norm_num at hh
      exact (sub_eq_zero.mp hh.symm).symm
    have hconst (x y : Fin 64)
        (hxy : D.connectedComponentMk x = D.connectedComponentMk y) :
        (v : Fin 64 → ℚ) x = (v : Fin 64 → ℚ) y := by
      apply apply_eq_of_mulVec_eq_smul_of_reachable D hDreg hvD
      exact SimpleGraph.ConnectedComponent.eq.mp hxy
    funext x
    have hx := congrFun hvP0 x
    change (∑ y,
      (if D.connectedComponentMk x = D.connectedComponentMk y then
          ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ else 0) *
        (v : Fin 64 → ℚ) y) = 0 at hx
    let c := D.connectedComponentMk x
    have hsum :
        (∑ y,
          (if D.connectedComponentMk x = D.connectedComponentMk y then
              ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ else 0) *
            (v : Fin 64 → ℚ) y) = (v : Fin 64 → ℚ) x := by
      calc
        _ = ∑ _y ∈ (Finset.univ : Finset (Fin 64)).filter
            (fun y => D.connectedComponentMk y = c),
              ((c.supp.ncard : ℚ)⁻¹ * (v : Fin 64 → ℚ) x) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : D.connectedComponentMk y = c
          · rw [if_pos hy.symm, if_pos hy]
            exact congrArg (fun z => (c.supp.ncard : ℚ)⁻¹ * z)
              (hconst x y hy.symm).symm
          · rw [if_neg (fun h => hy h.symm), if_neg hy]
            simp
        _ = (v : Fin 64 → ℚ) x := by
          rw [Finset.sum_const, card_filter_component]
          have hp : c.supp.ncard ≠ 0 :=
            Nat.ne_of_gt c.nonempty_supp.ncard_pos
          rw [nsmul_eq_mul]
          field_simp
    rw [hsum] at hx
    simpa using hx
  · exact bot_le

end

end Erdos85
