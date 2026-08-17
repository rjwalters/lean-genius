import Proofs.Erdos85OrderSixtyFourSevenComponent
import Proofs.Erdos85InvariantDecomposition

/-! # The residual defect-sector trace at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Orthogonal averaging onto the vectors constant on every connected
component of `D`.  Unlike `defectComponentAverageProjection`, this version
allows components of different orders. -/
def defectComponentNormalizedProjection
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    Matrix (Fin 64) (Fin 64) ℚ :=
  fun x y => if D.connectedComponentMk x = D.connectedComponentMk y then
    ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ else 0

private theorem card_filter_component_eq
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    ((Finset.univ : Finset (Fin 64)).filter
      (fun x => D.connectedComponentMk x = c)).card = c.supp.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem defectComponentNormalizedProjection_mul_self
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    defectComponentNormalizedProjection D *
        defectComponentNormalizedProjection D =
      defectComponentNormalizedProjection D := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [defectComponentNormalizedProjection]
  by_cases hxy : D.connectedComponentMk x = D.connectedComponentMk y
  · rw [if_pos hxy]
    calc
      (∑ z,
          (if D.connectedComponentMk x = D.connectedComponentMk z then
              ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ else 0) *
            if D.connectedComponentMk z = D.connectedComponentMk y then
              ((D.connectedComponentMk z).supp.ncard : ℚ)⁻¹ else 0) =
          ∑ _z ∈ (Finset.univ : Finset (Fin 64)).filter
            (fun z => D.connectedComponentMk z = D.connectedComponentMk x),
              ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ *
                ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : D.connectedComponentMk z = D.connectedComponentMk x
        · rw [if_pos hz.symm, if_pos (hz.trans hxy), hz]
          simp
        · rw [if_neg (fun hxz => hz hxz.symm),
            if_neg (fun hzy => hz (hzy.trans hxy.symm)), zero_mul]
          simp [hz]
      _ = ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ := by
        rw [Finset.sum_const, card_filter_component_eq]
        have hp : (D.connectedComponentMk x).supp.ncard ≠ 0 :=
          Nat.ne_of_gt (D.connectedComponentMk x).nonempty_supp.ncard_pos
        rw [nsmul_eq_mul]
        norm_num [hp]
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hxz : D.connectedComponentMk x = D.connectedComponentMk z
    · rw [if_pos hxz]
      rw [if_neg (fun hzy => hxy (hxz.trans hzy))]
      exact mul_zero _
    · rw [if_neg hxz]
      exact zero_mul _

theorem defectComponentNormalizedProjection_isSymm
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    (defectComponentNormalizedProjection D).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, defectComponentNormalizedProjection]
  by_cases hxy : D.connectedComponentMk x = D.connectedComponentMk y
  · rw [if_pos hxy, if_pos hxy.symm, hxy]
  · rw [if_neg hxy, if_neg (fun hyx => hxy hyx.symm)]

/-- Normalized averaging makes the order-64 adjacency action completely
uniform: every matrix entry of `A P` is `1/8`. -/
theorem orderSixtyFour_adj_mul_defectComponentNormalizedProjection
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    G.adjMatrix ℚ *
        defectComponentNormalizedProjection (secondOrderDefectGraph G) =
      Matrix.of (fun _ _ => (8 : ℚ)⁻¹) := by
  classical
  let D := secondOrderDefectGraph G
  let P := defectComponentNormalizedProjection D
  ext x y
  rw [Matrix.mul_apply]
  let S := componentNeighborFinset G D (D.connectedComponentMk y) x
  have heq (z : Fin 64) :
      G.adjMatrix ℚ x z * P z y =
        if z ∈ S then
          ((D.connectedComponentMk y).supp.ncard : ℚ)⁻¹ else 0 := by
    simp only [SimpleGraph.adjMatrix_apply, P,
      defectComponentNormalizedProjection]
    by_cases ha : G.Adj x z
    · by_cases hc : D.connectedComponentMk z = D.connectedComponentMk y
      · have hr : D.Reachable z y :=
          SimpleGraph.ConnectedComponent.eq.mp hc
        simp [S, componentNeighborFinset, ha, hc, hr]
      · have hr : ¬ D.Reachable z y := fun h =>
          hc (SimpleGraph.ConnectedComponent.eq.mpr h)
        simp [S, componentNeighborFinset, ha, hc, hr]
    · simp [S, componentNeighborFinset, ha]
  rw [Finset.sum_congr rfl fun z _ => heq z]
  rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_univ_mem]
  have hn := orderSixtyFour_eight_mul_componentNeighborFinset_card
    G hfree hmin hcover (D.connectedComponentMk y) x
  change 8 * S.card = (D.connectedComponentMk y).supp.ncard at hn
  have hp : (D.connectedComponentMk y).supp.ncard ≠ 0 :=
    Nat.ne_of_gt (D.connectedComponentMk y).nonempty_supp.ncard_pos
  have hnQ : (8 : ℚ) * S.card =
      (D.connectedComponentMk y).supp.ncard := by exact_mod_cast hn
  change (S.card : ℚ) *
    ((D.connectedComponentMk y).supp.ncard : ℚ)⁻¹ = (8 : ℚ)⁻¹
  rw [inv_eq_one_div]
  field_simp
  linarith [hnQ]

/-- The trace of adjacency followed by normalized component averaging is
eight, for every allowed component partition. -/
theorem orderSixtyFour_trace_adj_mul_defectComponentNormalizedProjection
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    Matrix.trace (G.adjMatrix ℚ *
      defectComponentNormalizedProjection (secondOrderDefectGraph G)) = 8 := by
  rw [orderSixtyFour_adj_mul_defectComponentNormalizedProjection
    G hfree hmin hcover]
  simp [Matrix.trace, Matrix.diag]
  norm_num

/-- The complementary, component-mean-zero sector carries adjacency trace
`-8`.  This is the precise residual trace that must be supplied by the
nonprincipal defect sectors. -/
theorem orderSixtyFour_residual_defect_sector_trace_eq_neg_eight
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
      LinearMap.trace ℚ _ ((G.adjMatrix ℚ).toLin'.restrict hW) = -8 := by
  classical
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let P := defectComponentNormalizedProjection D
  let J8 : Matrix (Fin 64) (Fin 64) ℚ :=
    Matrix.of fun _ _ => (8 : ℚ)⁻¹
  have hPmatrix : P * P = P :=
    defectComponentNormalizedProjection_mul_self D
  have hPid : IsIdempotentElem P.toLin' := by
    simpa only [IsIdempotentElem, Module.End.mul_eq_comp,
      Matrix.toLin'_mul] using congrArg Matrix.toLin' hPmatrix
  have hAP : A * P = J8 := by
    exact orderSixtyFour_adj_mul_defectComponentNormalizedProjection
      G hfree hmin hcover
  have hPA : P * A = J8 := by
    have ht := congrArg Matrix.transpose hAP
    have hJ8 : J8.transpose = J8 := by
      ext x y
      rfl
    rw [hJ8] at ht
    simpa only [Matrix.transpose_mul, A, P,
      G.isSymm_adjMatrix.eq,
      (defectComponentNormalizedProjection_isSymm D).eq] using ht
  have hcommM : A * P = P * A := hAP.trans hPA.symm
  have hcomm : A.toLin' * P.toLin' = P.toLin' * A.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  let U := LinearMap.range P.toLin'
  let W := LinearMap.ker P.toLin'
  let hU := mapsTo_range_of_commute A.toLin' P.toLin' hcomm
  let hW := mapsTo_ker_of_commute A.toLin' P.toLin' hcomm
  have htrace : LinearMap.trace ℚ (Fin 64 → ℚ) A.toLin' = 0 := by
    rw [Matrix.trace_toLin'_eq]
    simp [A, Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_apply]
  have hUtrace : LinearMap.trace ℚ U (A.toLin'.restrict hU) = 8 := by
    rw [trace_restrict_range_eq_trace_mul_of_idempotent
      A.toLin' P.toLin' hPid hcomm]
    rw [show A.toLin' * P.toLin' = (A * P).toLin' by
      simp only [Module.End.mul_eq_comp, Matrix.toLin'_mul],
      Matrix.trace_toLin'_eq]
    exact orderSixtyFour_trace_adj_mul_defectComponentNormalizedProjection
      G hfree hmin hcover
  have hsplit := trace_eq_add_trace_restrict_of_isCompl
    A.toLin' U W (LinearMap.IsIdempotentElem.isCompl hPid) hU hW
  refine ⟨hW, ?_⟩
  change LinearMap.trace ℚ W (A.toLin'.restrict hW) = -8
  rw [htrace, hUtrace] at hsplit
  linarith

end

end Erdos85
