import Proofs.Erdos85EulerianEdgeCycle
import Proofs.Erdos85ActiveBrokenRelayEulerizationEvenRegular

/-!
# Every active broken-relay Eulerization edge lies on a cycle

This is the direct transport consumer of the parity-free Eulerization and
the specified-edge cycle theorem.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the intended C4-free even-regular hypotheses, every chosen edge
of the active broken-relay/cut symmetric difference lies on a cycle of that
same Eulerian graph. -/
theorem activeBrokenRelay_cut_symmDiff_edge_exists_cycle_of_evenRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ v, A.degree v = q) (hq : Even q)
    (x : V → ZMod 2) (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) {a b : V}
    (hab : (graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))).Adj a b) :
    ∃ (u : V), ∃ p : (graphF2SymmetricDifference
        (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed)
        (binaryVertexCutGraph (triangleFreeEdgeGraph A)
          (f2PotentialSupport x))).Walk u u,
      p.IsCycle ∧ s(a, b) ∈ p.edges := by
  apply exists_isCycle_mem_edge_of_even_degrees _ _ hab
  exact activeBrokenRelay_cut_symmDiff_even_degree_of_evenRegular
    A hfree q hreg hq x mate hclosed hinvol hfixed

end

end Erdos85

#print axioms Erdos85.activeBrokenRelay_cut_symmDiff_edge_exists_cycle_of_evenRegular
