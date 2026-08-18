import Proofs.Erdos85BinarySquareMixedOwnerRootedCensus

/-!
# Rooted ordered triangles versus local triangle edges

The two orientations of every edge in the neighbourhood graph of `x` are
exactly the ordered ambient triangles rooted at `x`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered cyclic triples whose first root lies in `S`. -/
def cyclicColoredTriplesFirstRootIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] : Finset (V × V × V) :=
  (cyclicColoredTriples A B C).filter fun p => p.1 ∈ S

/-- First-root fiber decomposition over a vertex set. -/
theorem card_cyclicColoredTriplesFirstRootIn_eq_sum_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] :
    (cyclicColoredTriplesFirstRootIn A B C S).card =
      ∑ x : S, (rootedCyclicColoredPairs A B C x.1).card := by
  classical
  let e : {p // p ∈ cyclicColoredTriplesFirstRootIn A B C S} ≃
      Σ x : S, {q // q ∈ rootedCyclicColoredPairs A B C x.1} :=
    { toFun := fun p => by
        have hp := p.2
        simp only [cyclicColoredTriplesFirstRootIn, Finset.mem_filter,
          cyclicColoredTriples, Finset.mem_univ, true_and] at hp
        exact ⟨⟨p.1.1, hp.2⟩, ⟨(p.1.2.1, p.1.2.2), by
          simp only [rootedCyclicColoredPairs, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact hp.1⟩⟩
      invFun := fun q => by
        refine ⟨(q.1.1, q.2.1.1, q.2.1.2), ?_⟩
        have hq := q.2.2
        simp only [rootedCyclicColoredPairs, Finset.mem_filter,
          Finset.mem_univ, true_and] at hq
        simp only [cyclicColoredTriplesFirstRootIn, Finset.mem_filter,
          cyclicColoredTriples, Finset.mem_univ, true_and]
        exact ⟨hq, q.1.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        rcases p with ⟨⟨x, z, y⟩, hp⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨⟨x, hx⟩, ⟨⟨z, y⟩, hzy⟩⟩
        rfl }
  have hcard := Fintype.card_congr e
  simpa [Fintype.card_sigma] using hcard

/-- The global ordered cyclic census is the sum of its first-root fibers. -/
theorem card_cyclicColoredTriples_eq_sum_rootedCyclicColoredPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    (cyclicColoredTriples A B C).card =
      ∑ x : V, (rootedCyclicColoredPairs A B C x).card := by
  have htrace := trace_three_adjMatrices_eq_card_cyclicColoredTriples A B C
  change (∑ x : V,
      (A.adjMatrix ℤ * B.adjMatrix ℤ * C.adjMatrix ℤ) x x) =
        ((cyclicColoredTriples A B C).card : ℤ) at htrace
  simp_rw [mul_three_adjMatrices_apply_eq_card_rootedCyclicColoredPairs]
    at htrace
  exact_mod_cast htrace.symm

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
  Erdos85.card_cyclicColoredTriplesFirstRootIn_eq_sum_rooted
#print axioms
  Erdos85.card_cyclicColoredTriples_eq_sum_rootedCyclicColoredPairs
#print axioms
  Erdos85.card_rootedCyclicColoredPairs_self_eq_two_mul_localTriangleEdges
