import Proofs.Erdos85ActiveWitnessRelayBoundary
import Proofs.Erdos85F2MatrixSupportGraph

/-!
# Exact Eulerization of the active broken relay

The active broken relay and the cut of the triangle-free-edge graph have the
same F2 boundary.  Their symmetric difference is therefore represented by a
zero-boundary binary adjacency matrix, hence is an honest Eulerian graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem zmod_two_eq_of_eq_one_iff (a b : ZMod 2)
    (h : a = 1 ↔ b = 1) : a = b := by
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbinary a with rfl | rfl <;> rcases hbinary b with rfl | rfl
  · rfl
  · exact (zero_ne_one (h.mpr rfl)).elim
  · exact (zero_ne_one (h.mp rfl)).elim
  · rfl

/-- In an even-valent graph, the degree parity across the cut supported by
`x` is exactly the adjacency syndrome `G x`. -/
theorem binaryVertexCutGraph_degree_cast_eq_adjMatrix_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ZMod 2) (heven : ∀ v, Even (G.degree v)) (v : V) :
    ((binaryVertexCutGraph G (f2PotentialSupport x)).degree v : ZMod 2) =
      (G.adjMatrix (ZMod 2)).mulVec x v := by
  rw [← f2Potential_neighborSupport_card_cast G x v]
  apply zmod_two_eq_of_eq_one_iff
  rw [ZMod.natCast_eq_one_iff_odd, ZMod.natCast_eq_one_iff_odd]
  exact binaryVertexCutGraph_degree_odd_iff G (f2PotentialSupport x) v
    (heven v)

/-- Multiplying a binary adjacency matrix by the all-ones vector returns the
degree parity at each vertex. -/
theorem adjMatrix_mulVec_one_eq_degree_cast
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.adjMatrix (ZMod 2)).mulVec (fun _ => 1) v =
      (G.degree v : ZMod 2) := by
  have hsupp : f2PotentialSupport (fun _ : V => (1 : ZMod 2)) = Finset.univ := by
    ext u
    simp [f2PotentialSupport]
  rw [← f2Potential_neighborSupport_card_cast G (fun _ => 1) v,
    hsupp, Finset.inter_univ, G.card_neighborFinset_eq_degree]

/-- The graph supported on the F2 sum of two adjacency matrices: equivalently,
their edge symmetric difference. -/
def graphF2SymmetricDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (R C : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel C.Adj] :
    SimpleGraph V :=
  f2MatrixSupportGraph
    (R.adjMatrix (ZMod 2) + C.adjMatrix (ZMod 2))
    (by
      intro u v
      simp only [Matrix.add_apply, SimpleGraph.adjMatrix_apply]
      by_cases hr : R.Adj u v <;> by_cases hc : C.Adj u v <;>
        simp_all [R.adj_comm, C.adj_comm])
    (by intro v; simp [SimpleGraph.adjMatrix_apply])

instance graphF2SymmetricDifference_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (R C : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel C.Adj] :
    DecidableRel (graphF2SymmetricDifference R C).Adj := by
  dsimp only [graphF2SymmetricDifference]
  infer_instance

/-- Equal degree syndromes cancel in the symmetric difference, making it
Eulerian. -/
theorem graphF2SymmetricDifference_even_degree_of_degree_cast_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (R C : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel C.Adj]
    (hdegree : ∀ v, (R.degree v : ZMod 2) = (C.degree v : ZMod 2))
    (v : V) : Even ((graphF2SymmetricDifference R C).degree v) := by
  apply f2MatrixSupportGraph_even_degree_of_mulVec_one_eq_zero
  funext u
  rw [Matrix.add_mulVec, Pi.add_apply,
    adjMatrix_mulVec_one_eq_degree_cast,
    adjMatrix_mulVec_one_eq_degree_cast, hdegree]
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rfl

/-- Exact `(73rnz_cjibi-j)` Eulerization.  The active broken relay `R_s` and
the triangle-free cut have the same boundary `T x`; their F2 symmetric
difference has even degree everywhere. -/
theorem activeBrokenRelay_cut_symmDiff_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (x : V → ZMod 2)
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (hevenT : ∀ v, Even ((triangleFreeEdgeGraph A).degree v)) (v : V) :
    Even ((graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))).degree v) := by
  apply graphF2SymmetricDifference_even_degree_of_degree_cast_eq
  intro u
  rw [activeBrokenWitnessRelayGraph_degree_cast_eq_adjMatrix_mulVec
    A hfree x mate hclosed hinvol hfixed u]
  exact (binaryVertexCutGraph_degree_cast_eq_adjMatrix_mulVec
    (triangleFreeEdgeGraph A) x hevenT u).symm

end

end Erdos85

#print axioms Erdos85.binaryVertexCutGraph_degree_cast_eq_adjMatrix_mulVec
#print axioms Erdos85.graphF2SymmetricDifference_even_degree_of_degree_cast_eq
#print axioms Erdos85.activeBrokenRelay_cut_symmDiff_even_degree
