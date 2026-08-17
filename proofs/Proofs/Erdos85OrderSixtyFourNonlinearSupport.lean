import Proofs.Erdos85OrderSixtyFourSixteenBlockCycles
import Proofs.Erdos85OrderSixtyFourComponentMeanZero
import Proofs.Erdos85OrderSixtyFourSizeEightDefectClique

/-! # Support of non-`-1` defect eigenspaces at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On an order-eight component of a seven-regular graph, a componentwise
mean-zero vector is acted on by adjacency as negation. -/
theorem sevenRegular_orderEightComponent_mulVec_eq_neg_of_sum_zero
    {K : Type*} [Field K]
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (hreg : ∀ x : Fin 64, D.degree x = 7)
    (e : D.ConnectedComponent) (he8 : e.supp.ncard = 8)
    (v : Fin 64 → K) (hsum : ∑ z : e.supp, v z.1 = 0)
    {y : Fin 64} (hy : D.connectedComponentMk y = e) :
    (D.adjMatrix K).mulVec v y = -v y := by
  classical
  let F := (Finset.univ : Finset (Fin 64)).filter
    (fun z => D.connectedComponentMk z = e)
  have hyF : y ∈ F := by simp [F, hy]
  have hneighbors : D.neighborFinset y = F.erase y := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have hyz : D.Adj y z := (D.mem_neighborFinset y z).mp hz
      have hzcomp : D.connectedComponentMk z = e :=
        (ConnectedComponent.connectedComponentMk_eq_of_adj hyz).symm.trans hy
      exact Finset.mem_erase.mpr ⟨(D.ne_of_adj hyz).symm, by simp [F, hzcomp]⟩
    · rw [D.card_neighborFinset_eq_degree, hreg,
        Finset.card_erase_of_mem hyF]
      have hFcard : F.card = e.supp.ncard := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext z
        simp [F, ConnectedComponent.mem_supp_iff]
      rw [hFcard, he8]
  have hFsum : ∑ z ∈ F, v z = 0 := by
    calc
      (∑ z ∈ F, v z) = ∑ z : e.supp, v z.1 := by
        simpa [F, ConnectedComponent.mem_supp_iff] using
          (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset (Fin 64)))
            (p := fun z => z ∈ e.supp) v).symm
      _ = 0 := hsum
  have hmul : (D.adjMatrix K).mulVec v y =
      ∑ z ∈ D.neighborFinset y, v z := by
    rw [Matrix.mulVec, dotProduct]
    simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext z
    simp [SimpleGraph.mem_neighborFinset]
  rw [hmul, hneighbors]
  have herase := Finset.sum_erase_add _ v hyF
  rw [hFsum] at herase
  exact eq_neg_of_add_eq_zero_left herase

/-- Field-generic localization.  This is the form needed after extending
scalars to an algebraic closure in the nonlinear primary argument. -/
theorem orderSixtyFour_seven_defect_components_nonMinusOne_eigenvector_support_field
    {K : Type*} [Field K]
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7)
    (v : Fin 64 → K)
    (hsumAll : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      ∑ z : e.supp, v z.1 = 0)
    (μ : K) (hμ : μ ≠ -1)
    (heigen : ((secondOrderDefectGraph G).adjMatrix K).mulVec v = μ • v) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧ ∀ y, y ∉ c.supp → v y = 0 := by
  let instG := ‹DecidableRel G.Adj›
  let instAnti := ‹DecidableRel (antipodalGraph G).Adj›
  let instT := ‹DecidableRel (triangleFreeEdgeGraph G).Adj›
  let instComp := ‹DecidableEq (secondOrderDefectGraph G).ConnectedComponent›
  classical
  letI := instG
  letI := instAnti
  letI := instT
  letI := instComp
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hothers⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro y hyc
  let e := D.connectedComponentMk y
  have hec : e ≠ c := by
    intro heq
    apply hyc
    rw [ConnectedComponent.mem_supp_iff]
    exact heq
  have he8 := hothers e hec
  have hneg := sevenRegular_orderEightComponent_mulVec_eq_neg_of_sum_zero
    D (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
    e he8 v (hsumAll e) (y := y) rfl
  have hey := congrFun heigen y
  change (D.adjMatrix K).mulVec v y = μ * v y at hey
  rw [hneg] at hey
  have hfactor : (μ + 1) * v y = 0 := by
    calc
      (μ + 1) * v y = μ * v y + v y := by ring
      _ = -v y + v y := by rw [← hey]
      _ = 0 := neg_add_cancel _
  have hμone : μ + 1 ≠ 0 := by
    intro hz
    apply hμ
    exact eq_neg_of_add_eq_zero_left hz
  exact (mul_eq_zero.mp hfactor).resolve_left hμone

/-- Every residual defect eigenvector with eigenvalue different from `-1`
is supported on the unique order-16 component.  The six order-eight blocks
are complete, so their mean-zero adjacency eigenvalue is exactly `-1`. -/
theorem orderSixtyFour_seven_defect_components_nonMinusOne_eigenvector_support
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7)
    (v : Fin 64 → ℚ)
    (hv : v ∈ LinearMap.ker
      (defectComponentNormalizedProjection
        (secondOrderDefectGraph G)).toLin')
    (μ : ℚ) (hμ : μ ≠ -1)
    (heigen : ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec v = μ • v) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧ ∀ y, y ∉ c.supp → v y = 0 := by
  let instG := ‹DecidableRel G.Adj›
  let instAnti := ‹DecidableRel (antipodalGraph G).Adj›
  let instT := ‹DecidableRel (triangleFreeEdgeGraph G).Adj›
  let instComp := ‹DecidableEq (secondOrderDefectGraph G).ConnectedComponent›
  classical
  letI := instG
  letI := instAnti
  letI := instT
  letI := instComp
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hothers⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro y hyc
  let e := D.connectedComponentMk y
  have hec : e ≠ c := by
    intro heq
    apply hyc
    rw [ConnectedComponent.mem_supp_iff]
    exact heq
  have he8 := hothers e hec
  have hsum : ∑ z : e.supp, v z.1 = 0 :=
    (mem_ker_defectComponentNormalizedProjection_iff_component_sum_zero
      D v).mp hv e
  have hneg := sevenRegular_orderEightComponent_mulVec_eq_neg_of_sum_zero
    D (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
    e he8 v hsum (y := y) rfl
  have hey := congrFun heigen y
  change (D.adjMatrix ℚ).mulVec v y = μ * v y at hey
  rw [hneg] at hey
  have hfactor : (μ + 1) * v y = 0 := by linarith
  have hμone : μ + 1 ≠ 0 := by
    intro hz
    apply hμ
    linarith
  exact (mul_eq_zero.mp hfactor).resolve_left hμone

end

end Erdos85
