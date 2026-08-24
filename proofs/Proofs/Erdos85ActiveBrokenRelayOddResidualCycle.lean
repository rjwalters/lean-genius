import Proofs.Erdos85DisconnectedEulerianOddResidualHolonomy
import Proofs.Erdos85OddWeightCycleExtraction

/-!
# An actual odd-price cycle in the active broken relay

Compose connectivity-free Eulerian holonomy with weighted cycle extraction.
The result matches the audit's cycle-space terminal literally: odd residual
price produces a `Walk.IsCycle`, not merely a closed walk.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Odd residual price in the active-broken Eulerization produces an actual
Q_s cycle of odd K-weight, without a connectivity hypothesis. -/
theorem activeBrokenRelay_exists_odd_residual_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (x : V → ZMod 2)
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (hodd : Odd (((graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))) ⊓
      binaryTransportResidualGraph A hq hreg).edgeFinset.card)) :
    ∃ (u : V) (c : (graphF2SymmetricDifference
        (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed)
        (binaryVertexCutGraph (triangleFreeEdgeGraph A)
          (f2PotentialSupport x))).Walk u u),
      c.IsCycle ∧
      f2WalkWeight (graphEdgeIndicator
        (binaryTransportResidualGraph A hq hreg)) c = 1 := by
  obtain ⟨u, p, hp⟩ :=
    activeBrokenRelay_exists_closedWalk_odd_residual_global
      A hfree hq hreg x mate hclosed hinvol hfixed hodd
  obtain ⟨v, c, hcycle, hweight, _⟩ :=
    exists_odd_graphEdgeIndicator_cycle_of_closedWalk
      (graphF2SymmetricDifference
        (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed)
        (binaryVertexCutGraph (triangleFreeEdgeGraph A)
          (f2PotentialSupport x)))
      (binaryTransportResidualGraph A hq hreg) p hp
  exact ⟨v, c, hcycle, hweight⟩

end

end Erdos85

#print axioms Erdos85.activeBrokenRelay_exists_odd_residual_cycle
