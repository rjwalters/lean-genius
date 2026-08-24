import Proofs.Erdos85FinalDyadicEndpointResidualBranchPartition

/-!
# The endpoint residual/nonexceptional equitable cut

Every nonexceptional vertex has exactly `r` graph neighbors in the residual
cell, while every exceptional vertex has none.  This is the pointwise form
of the operator identity sending the residual-cell indicator to `r` times
the nonexceptional indicator.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Graph degree into the residual cell is exactly `r` off exceptional
support and zero on exceptional support. -/
theorem finalDyadic_endpoint_neighbor_inter_residual_card_eq_ite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (v : V) :
    (G.neighborFinset v ∩
      ((Finset.univ : Finset V) \ (S ∪
        finalDyadicNegativeHighCutCenters G S j r))).card =
      if v ∈ exceptionalSignedSupport G S q then 0 else r := by
  let M := finalDyadicNegativeHighCutCenters G S j r
  let W := (Finset.univ : Finset V) \ (S ∪ M)
  by_cases hv : v ∈ exceptionalSignedSupport G S q
  · rw [if_pos hv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro w hw
    have hwData := Finset.mem_inter.mp hw
    have hvNw : v ∈ G.neighborFinset w :=
      (G.mem_neighborFinset w v).mpr
        ((G.mem_neighborFinset v w).mp hwData.1).symm
    have hdisj :=
      finalDyadic_endpoint_residual_neighborFinset_disjoint_exceptional
        G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
          hsupport hemptyClique hwData.2
    exact Finset.disjoint_left.mp hdisj hvNw hv
  · rw [if_neg hv]
    have hres :=
      (finalDyadic_endpoint_nonexceptional_residual_degree_profile
        G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
          hsupport hemptyClique hv).2.2
    have hset : G.neighborFinset v ∩ W =
        G.neighborFinset v \ (S ∪ M) := by
      ext x
      simp [W]
    change (G.neighborFinset v ∩ W).card = r
    rw [hset]
    exact hres

end

end Erdos85

#print axioms Erdos85.finalDyadic_endpoint_neighbor_inter_residual_card_eq_ite
