import Proofs.Erdos85OwnerLedgerDiagonalResidual
import Proofs.Erdos85StarActivityTriangleEdgeCutGraph

/-!
# The owner-ledger diagonal residual as a literal triangle-edge cut

Once the false-owner center discrepancy is identified with residual-center
activity, the last diagonal coefficient is exactly the parity of a located
part of the support cut in `A \ T`.
-/

open SimpleGraph

namespace Erdos85

open OwnerSourceTransportLedger

/-- **Ledger-to-literal-cut reduction.**  Under the exact centerwise
discrepancy/activity identification, the corrected owner terminal is `(1,1)`
if and only if the total residual `(A \ T)` support-cut incidence has even
parity. -/
theorem psiHatOwner_eq_one_iff_triangleEdgeCutResidual_eq_zero
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (L : OwnerSourceTransportLedger C)
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    [DecidableRel (A \ T).Adj]
    (R X : Finset V) (t : V → ZMod 2)
    (delta : Bool → V → ZMod 2)
    (hdecomp : ∀ owner,
      L.psiHatOwner owner = 1 + ∑ g ∈ R, delta owner g)
    (hzero : ∀ g ∈ R, delta false g + delta true g = 0)
    (hdeltaActivity : ∀ g ∈ R,
      delta false g = ∑ u ∈ A.neighborFinset g ∩ X, t u)
    (heven : ∀ g ∈ R, Even (A.neighborFinset g ∩ X).card)
    (hTconst : ∀ g ∈ R, ∀ u, u ∈ A.neighborFinset g ∩ X →
      T.Adj g u → t u = t g) :
    L.psiHatOwner = (fun _ : Bool => 1) ↔
      (((∑ g ∈ R,
        ((binaryVertexCutGraph (A \ T)
          (f2PotentialSupport t)).neighborFinset g ∩ X).card : ℕ) :
            ZMod 2) = 0) := by
  rw [psiHatOwner_eq_one_iff_diagonalResidual_eq_zero
    L R delta hdecomp hzero]
  have hDeltaActivity :
      (∑ g ∈ R, delta false g) =
        ∑ g ∈ R, ∑ u ∈ A.neighborFinset g ∩ X, t u := by
    apply Finset.sum_congr rfl
    intro g hg
    exact hdeltaActivity g hg
  rw [hDeltaActivity,
    sum_f2_neighbor_inter_eq_sum_starTriangleEdgeCut_card
      A T R X t heven hTconst]
  have hcounts :
      (∑ y ∈ R, (starTriangleEdgeCutNeighbors A T X t y).card) =
        ∑ g ∈ R,
          ((binaryVertexCutGraph (A \ T) (f2PotentialSupport t)).neighborFinset g ∩ X).card := by
    apply Finset.sum_congr rfl
    intro g _
    rw [starTriangleEdgeCutNeighbors_eq_cutGraph_neighborFinset_inter]
  rw [hcounts]

end Erdos85

#print axioms Erdos85.psiHatOwner_eq_one_iff_triangleEdgeCutResidual_eq_zero
