import Proofs.Erdos85BinarySquareMixedOwnerRootedCensus

/-!
# Rooted ordered triangles versus local triangle edges

The two orientations of every edge in the neighbourhood graph of `x` are
exactly the ordered ambient triangles rooted at `x`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered ambient triangles rooted at `x` are counted twice by the local
unoriented triangle-edge count. -/
theorem card_rootedCyclicColoredPairs_self_eq_two_mul_localTriangleEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (rootedCyclicColoredPairs G G G x).card =
      2 * (G.induce (G.neighborSet x)).edgeFinset.card := by
  classical
  let H := G.induce (G.neighborSet x)
  let e : {p // p ∈ rootedCyclicColoredPairs G G G x} ≃ H.Dart :=
    { toFun := fun p => by
        have hp := p.2
        simp only [rootedCyclicColoredPairs, Finset.mem_filter,
          Finset.mem_univ, true_and] at hp
        exact
          { toProd :=
              (⟨p.1.2, (G.mem_neighborSet x p.1.2).mpr hp.1⟩,
                ⟨p.1.1, (G.mem_neighborSet x p.1.1).mpr hp.2.2.symm⟩)
            adj := hp.2.1 }
      invFun := fun d => by
        refine ⟨(d.snd.1, d.fst.1), ?_⟩
        simp only [rootedCyclicColoredPairs, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨(G.mem_neighborSet x d.fst.1).mp d.fst.2,
          d.adj, ((G.mem_neighborSet x d.snd.1).mp d.snd.2).symm⟩
      left_inv := by
        intro p
        apply Subtype.ext
        simp
      right_inv := by
        intro d
        apply SimpleGraph.Dart.ext
        simp }
  have hcard := Fintype.card_congr e
  simpa [H] using hcard.trans H.dart_card_eq_twice_card_edges

end

end Erdos85

#print axioms
  Erdos85.card_rootedCyclicColoredPairs_self_eq_two_mul_localTriangleEdges
