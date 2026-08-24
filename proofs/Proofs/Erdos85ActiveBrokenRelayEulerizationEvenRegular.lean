import Proofs.Erdos85ActiveBrokenRelayEulerization
import Proofs.Erdos85BrokenFiberParity

/-!
# Active broken-relay Eulerization from even regularity

Broken-fiber parity removes the final `T`-evenness hypothesis from the exact
active-relay Eulerization.  The intended C4-free even-regular `A` assumptions
now suffice directly.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a finite C4-free even-regular graph, the active broken relay and its
triangle-free cut have an Eulerian symmetric difference. -/
theorem activeBrokenRelay_cut_symmDiff_even_degree_of_evenRegular
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
      mate w v ≠ v) (v : V) :
    Even ((graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))).degree v) := by
  apply activeBrokenRelay_cut_symmDiff_even_degree
    A hfree x mate hclosed hinvol hfixed
  intro u
  have hevenFiber := even_triangleFreeEdge_fiber_of_even_degree A hfree u
    (by simpa [hreg u] using hq)
  have hfiber :
      (Finset.univ.filter fun z =>
        (triangleFreeEdgeGraph A).Adj u z) =
        (triangleFreeEdgeGraph A).neighborFinset u := by
    ext z
    simp [SimpleGraph.mem_neighborFinset]
  rw [hfiber, (triangleFreeEdgeGraph A).card_neighborFinset_eq_degree u]
    at hevenFiber
  exact hevenFiber

#print axioms activeBrokenRelay_cut_symmDiff_even_degree_of_evenRegular

end

end Erdos85
