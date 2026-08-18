import Proofs.Erdos85CycleDefectPrimaryClassification
import Proofs.Erdos85OrderSixteenTwoFactorCensus
import Proofs.Erdos85TwoRegularEigenvalueCycleLocator

/-! # Component orders from the order-sixteen two-factor census -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Every component of a C4-free 2-regular graph on sixteen vertices has
one of the ten cycle orders consumed by the defect-primary classifier. -/
theorem orderSixteenCycleOrder_of_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hdeg : ∀ x, G.degree x = 2) (hfree : ¬ containsC4 V G)
    (c : G.ConnectedComponent) :
    OrderSixteenCycleOrder c.supp.ncard := by
  classical
  obtain ⟨rs, hcensus, hsizes⟩ :=
    exists_orderSixteenCyclePartition_of_twoRegular_of_not_containsC4
      G hcard hdeg hfree
  have hmemMapped :
      c.supp.ncard ∈
        (Finset.univ : Finset G.ConnectedComponent).val.map
          (fun e ↦ e.supp.ncard) := by
    exact Multiset.mem_map.mpr ⟨c, by simp, rfl⟩
  have hmem : c.supp.ncard ∈ rs := by
    change c.supp.ncard ∈ (↑rs : Multiset ℕ)
    rw [hsizes]
    exact hmemMapped
  rcases hcensus with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals simp_all [OrderSixteenCycleOrder] <;> aesop

/-- Capstone consumer for the internal two-factor: every actual adjacency
eigenvalue of a C4-free 2-regular graph on sixteen vertices maps under
`μ = 7 - α²` to one of the ten fully registered defect primaries. -/
theorem orderSixteen_twoRegular_eigenvalue_defect_primary_class
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hdeg : ∀ x, G.degree x = 2) (hfree : ¬ containsC4 V G)
    (α : AlgebraicClosure ℚ) (v : V → AlgebraicClosure ℚ)
    (hv0 : v ≠ 0)
    (heigen : (G.adjMatrix (AlgebraicClosure ℚ)).mulVec v = α • v) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  obtain ⟨c, r, _hrthree, hrsize, hroot⟩ :=
    exists_twoRegular_component_chebyshev_root_of_eigenvector
      G hdeg α v hv0 heigen
  have hr : OrderSixteenCycleOrder r := by
    rw [hrsize]
    exact orderSixteenCycleOrder_of_component G hcard hdeg hfree c
  exact orderSixteenCycle_defect_primary_class hr α hroot

end

end Erdos85
