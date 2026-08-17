import Proofs.Erdos85OrderSixtyFourDefectComponentEquitable
import Proofs.Erdos85QuadraticTrace
import Proofs.Erdos85PrincipalIndicatorTrace

/-! # Excluding eight defect components at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

def defectComponentAverageProjection
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    Matrix (Fin 64) (Fin 64) ℚ :=
  fun x y => if D.connectedComponentMk x = D.connectedComponentMk y
    then (8 : ℚ)⁻¹ else 0

private theorem card_filter_connectedComponentMk_eq
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    ((Finset.univ : Finset (Fin 64)).filter
      (fun x => D.connectedComponentMk x = c)).card = c.supp.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem defectComponentAverageProjection_mul_self
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (hsize : ∀ c : D.ConnectedComponent, c.supp.ncard = 8) :
    defectComponentAverageProjection D * defectComponentAverageProjection D =
      defectComponentAverageProjection D := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [defectComponentAverageProjection]
  by_cases hxy : D.connectedComponentMk x = D.connectedComponentMk y
  · rw [if_pos hxy]
    calc
      (∑ z,
          (if D.connectedComponentMk x = D.connectedComponentMk z
            then (8 : ℚ)⁻¹ else 0) *
          if D.connectedComponentMk z = D.connectedComponentMk y
            then (8 : ℚ)⁻¹ else 0) =
          ∑ _z ∈ (Finset.univ : Finset (Fin 64)).filter
            (fun z => D.connectedComponentMk z = D.connectedComponentMk y),
              (8 : ℚ)⁻¹ * (8 : ℚ)⁻¹ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : D.connectedComponentMk z = D.connectedComponentMk y
        · simp [hz, hxy.trans hz.symm]
        · simp [hz, fun hxz : D.connectedComponentMk x =
            D.connectedComponentMk z => hz (hxz.symm.trans hxy)]
      _ = (8 : ℚ)⁻¹ := by
        rw [Finset.sum_const, card_filter_connectedComponentMk_eq,
          hsize]
        norm_num
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hxz : D.connectedComponentMk x = D.connectedComponentMk z
    · rw [if_pos hxz]
      have hzy : D.connectedComponentMk z ≠ D.connectedComponentMk y := by
        intro h
        exact hxy (hxz.trans h)
      rw [if_neg hzy, mul_zero]
    · rw [if_neg hxz, zero_mul]

private theorem defect_neighborFinset_eq_component_erase
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (hreg : ∀ x : Fin 64, D.degree x = 7)
    (hsize : ∀ c : D.ConnectedComponent, c.supp.ncard = 8)
    (x : Fin 64) :
    D.neighborFinset x =
      ((Finset.univ : Finset (Fin 64)).filter
        (fun y => D.connectedComponentMk y = D.connectedComponentMk x)).erase x := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    have hxy : D.Adj x y := (D.mem_neighborFinset x y).mp hy
    have hcomp : D.connectedComponentMk y = D.connectedComponentMk x :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(D.ne_of_adj hxy).symm, hcomp⟩
  · rw [D.card_neighborFinset_eq_degree, hreg]
    have hxmem : x ∈ (Finset.univ : Finset (Fin 64)).filter
        (fun y => D.connectedComponentMk y = D.connectedComponentMk x) := by simp
    rw [Finset.card_erase_of_mem hxmem,
      card_filter_connectedComponentMk_eq, hsize]

theorem defect_adjMatrix_eq_eight_smul_projection_sub_one
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (hreg : ∀ x : Fin 64, D.degree x = 7)
    (hsize : ∀ c : D.ConnectedComponent, c.supp.ncard = 8) :
    D.adjMatrix ℚ =
      (8 : ℚ) • defectComponentAverageProjection D -
        (1 : Matrix (Fin 64) (Fin 64) ℚ) := by
  classical
  ext x y
  have hneighbors := defect_neighborFinset_eq_component_erase D hreg hsize x
  simp only [SimpleGraph.adjMatrix_apply, defectComponentAverageProjection,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    simp
  · have hadj : D.Adj x y ↔
        D.connectedComponentMk x = D.connectedComponentMk y := by
      rw [← D.mem_neighborFinset, hneighbors]
      simp [hxy, eq_comm]
    by_cases hc : D.connectedComponentMk x = D.connectedComponentMk y
    · rw [if_pos (hadj.mpr hc), if_pos hc]
      norm_num [hxy]
    · rw [if_neg (fun h => hc (hadj.mp h)), if_neg hc]
      norm_num [hxy]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem orderSixtyFour_adj_mul_defectComponentAverageProjection
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 8) :
    G.adjMatrix ℚ *
        defectComponentAverageProjection (secondOrderDefectGraph G) =
      Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by
  classical
  let D := secondOrderDefectGraph G
  have hsize (c : D.ConnectedComponent) : c.supp.ncard = 8 :=
    orderSixtyFour_defect_component_order_eq_eight_of_count_eight
      G hfree hmin hcover hcount c
  have hneighbor (c : D.ConnectedComponent) (x : Fin 64) :
      (componentNeighborFinset G D c x).card = 1 := by
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover c x
    change 8 * (componentNeighborFinset G D c x).card = c.supp.ncard at h
    rw [hsize c] at h
    omega
  ext x y
  rw [Matrix.mul_apply]
  simp only [SimpleGraph.adjMatrix_apply,
    defectComponentAverageProjection, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]
  let S := componentNeighborFinset G D (D.connectedComponentMk y) x
  have heq (z : Fin 64) :
      (if G.Adj x z then
          (if D.connectedComponentMk z = D.connectedComponentMk y
            then (8 : ℚ)⁻¹ else 0) else 0) =
        if z ∈ S then (8 : ℚ)⁻¹ else 0 := by
    by_cases ha : G.Adj x z <;>
      by_cases hc : D.connectedComponentMk z = D.connectedComponentMk y <;>
      simp only [S, componentNeighborFinset, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset, ha, hc, and_self, true_and,
        false_and, if_true, if_false]
  rw [Finset.sum_congr rfl fun z _ => heq z]
  rw [← Finset.sum_filter, Finset.sum_const]
  rw [Finset.filter_univ_mem]
  change S.card • (8 : ℚ)⁻¹ = (8 : ℚ)⁻¹
  rw [show S.card = 1 from hneighbor _ _]
  norm_num

theorem defectComponentAverageProjection_isSymm
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    (defectComponentAverageProjection D).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, defectComponentAverageProjection]
  by_cases h : D.connectedComponentMk x = D.connectedComponentMk y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hyx => h hyx.symm)]

theorem ones_mul_defectComponentAverageProjection
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (hsize : ∀ c : D.ConnectedComponent, c.supp.ncard = 8) :
    (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix (Fin 64) (Fin 64) ℚ) *
        defectComponentAverageProjection D =
      Matrix.of (fun _ _ => (1 : ℚ)) := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, one_mul, defectComponentAverageProjection]
  rw [← Finset.sum_filter, Finset.sum_const,
    card_filter_connectedComponentMk_eq, hsize]
  norm_num

theorem trace_adj_mul_defectComponentAverageProjection_eq_eight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 8) :
    Matrix.trace (G.adjMatrix ℚ *
      defectComponentAverageProjection (secondOrderDefectGraph G)) = 8 := by
  rw [orderSixtyFour_adj_mul_defectComponentAverageProjection
    G hfree hmin hcover hcount]
  simp [Matrix.trace, Matrix.diag]
  norm_num

/-- The defect graph cannot have eight connected components.  In that
branch the block-constant sector has adjacency trace eight, while the
complement squares to the nonsquare scalar eight and hence has trace zero,
contradicting the zero trace of a loopless adjacency matrix. -/
theorem orderSixtyFour_defect_component_count_ne_eight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent ≠ 8 := by
  classical
  intro hcount
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let P := defectComponentAverageProjection D
  let J : Matrix (Fin 64) (Fin 64) ℚ := Matrix.of fun _ _ => 1
  have hkernel := orderSixtyFour_regular_defect_kernel G hfree hmin hcover
  have hDreg : ∀ x : Fin 64, D.degree x = 7 := hkernel.2.2.1
  have hsize (c : D.ConnectedComponent) : c.supp.ncard = 8 :=
    orderSixtyFour_defect_component_order_eq_eight_of_count_eight
      G hfree hmin hcover hcount c
  have hPmatrix : P * P = P :=
    defectComponentAverageProjection_mul_self D hsize
  have hPid : IsIdempotentElem P.toLin' := by
    simpa only [IsIdempotentElem, Module.End.mul_eq_comp,
      Matrix.toLin'_mul] using congrArg Matrix.toLin' hPmatrix
  have hAP : A * P = Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by
    exact orderSixtyFour_adj_mul_defectComponentAverageProjection
      G hfree hmin hcover hcount
  have hPA : P * A = Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by
    have ht := congrArg Matrix.transpose hAP
    have hRt : (Matrix.of (fun _ _ => (8 : ℚ)⁻¹) :
        Matrix (Fin 64) (Fin 64) ℚ).transpose =
        Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by
      ext x y
      rfl
    rw [hRt] at ht
    simpa only [Matrix.transpose_mul, A, P,
      G.isSymm_adjMatrix.eq,
      (defectComponentAverageProjection_isSymm D).eq] using ht
  have hcommM : A * P = P * A := hAP.trans hPA.symm
  have hcomm : A.toLin' * P.toLin' = P.toLin' * A.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  let U := LinearMap.range P.toLin'
  let W := LinearMap.ker P.toLin'
  let hU := mapsTo_range_of_commute A.toLin' P.toLin' hcomm
  let hW := mapsTo_ker_of_commute A.toLin' P.toLin' hcomm
  have hJP : J * P = J := by
    exact ones_mul_defectComponentAverageProjection D hsize
  have hDmatrix : D.adjMatrix ℚ = (8 : ℚ) • P - 1 :=
    defect_adjMatrix_eq_eight_smul_projection_sub_one D hDreg hsize
  have hsq : A * A = (8 : ℚ) • 1 + J - (8 : ℚ) • P := by
    have hbase := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
      G hfree hkernel.1
    dsimp only [A, J]
    rw [hbase, hDmatrix]
    simp only [ratOnesMatrix]
    module
  have hWsq : (A.toLin'.restrict hW) * (A.toLin'.restrict hW) =
      (8 : ℚ) • LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hvP : P.mulVec (v : Fin 64 → ℚ) = 0 := v.property
    have hvJ : J.mulVec (v : Fin 64 → ℚ) = 0 := by
      have hj := congrArg (fun M => M.mulVec (v : Fin 64 → ℚ)) hJP
      rw [← Matrix.mulVec_mulVec, hvP, Matrix.mulVec_zero] at hj
      exact hj.symm
    have hv := congrArg (fun M => M.mulVec (v : Fin 64 → ℚ)) hsq
    simp only [Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hvJ, hvP, add_zero,
      smul_zero, sub_zero] at hv
    simpa [LinearMap.restrict_apply, Module.End.mul_apply] using hv
  have htrace : LinearMap.trace ℚ (Fin 64 → ℚ) A.toLin' = 0 := by
    rw [Matrix.trace_toLin'_eq]
    simp [A, Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_apply]
  have hUtrace : LinearMap.trace ℚ U (A.toLin'.restrict hU) = 8 := by
    rw [trace_restrict_range_eq_trace_mul_of_idempotent
      A.toLin' P.toLin' hPid hcomm]
    rw [show A.toLin' * P.toLin' = (A * P).toLin' by
      simp only [Module.End.mul_eq_comp, Matrix.toLin'_mul],
      Matrix.trace_toLin'_eq]
    exact trace_adj_mul_defectComponentAverageProjection_eq_eight
      G hfree hmin hcover hcount
  have hWnontrivial : Nontrivial W := by
    have hcardN : (D.neighborFinset 0).card = 7 := by
      rw [D.card_neighborFinset_eq_degree, hDreg]
    have hNnonempty : (D.neighborFinset 0).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      rw [he] at hcardN
      simp at hcardN
    obtain ⟨y, hy⟩ := hNnonempty
    have hxy : D.Adj 0 y := (D.mem_neighborFinset 0 y).mp hy
    have hcomp : D.connectedComponentMk 0 = D.connectedComponentMk y :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
    let v : Fin 64 → ℚ := Pi.single 0 1 - Pi.single y 1
    have hPv : P.mulVec v = 0 := by
      dsimp only [v]
      rw [Matrix.mulVec_sub, Matrix.mulVec_single_one,
        Matrix.mulVec_single_one]
      funext z
      change P z 0 - P z y = 0
      simp only [P, defectComponentAverageProjection, sub_eq_zero]
      by_cases hz : D.connectedComponentMk z = D.connectedComponentMk 0
      · rw [if_pos hz, if_pos (hz.trans hcomp)]
      · rw [if_neg hz, if_neg (fun hzy => hz (hzy.trans hcomp.symm))]
    have hv0 : v ≠ 0 := by
      intro hv
      have hz := congrFun hv 0
      simp [v, (D.ne_of_adj hxy)] at hz
    let w : W := ⟨v, hPv⟩
    exact ⟨⟨w, 0, fun hw => hv0 (congrArg Subtype.val hw)⟩⟩
  letI : Nontrivial W := hWnontrivial
  exact false_of_complementary_traces_sq_nonsquare_nat
    A.toLin' U W
    (LinearMap.IsIdempotentElem.isCompl hPid) hU hW htrace
    8 (by norm_num) hUtrace 8 (by norm_num) hWsq

end

end Erdos85
