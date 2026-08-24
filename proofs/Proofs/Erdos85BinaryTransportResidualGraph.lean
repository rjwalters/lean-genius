import Proofs.Erdos85BinaryTransportTriangleInterface
import Proofs.Erdos85ActiveBrokenRelayEulerization

/-!
# The residual binary transport graph

Set `H = supp(A²(A+I))` and let `T` be the triangle-free-edge graph.  This
file realizes `K = H △ T` as a simple graph, proves it Eulerian, and proves
it edge-disjoint from the ambient graph.  These are audit identities
(17)--(18) in graph form.
-/

open SimpleGraph

namespace Erdos85

instance triangleFreeEdgeGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (triangleFreeEdgeGraph G).Adj := by
  intro x y
  change Decidable (y ∈ triangleFreeNeighbors G x)
  infer_instance

/-- Adjacency in the F₂ graph sum is exclusive-or adjacency. -/
theorem graphF2SymmetricDifference_adj_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (R C : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel C.Adj]
    (x y : V) :
    (graphF2SymmetricDifference R C).Adj x y ↔
      (R.Adj x y ∧ ¬ C.Adj x y) ∨ (¬ R.Adj x y ∧ C.Adj x y) := by
  change R.adjMatrix (ZMod 2) x y + C.adjMatrix (ZMod 2) x y = 1 ↔ _
  simp only [SimpleGraph.adjMatrix_apply]
  by_cases hr : R.Adj x y <;> by_cases hc : C.Adj x y <;> simp [hr, hc]

/-- The residual transport graph `K = H △ T`. -/
def binaryTransportResidualGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, G.degree v = q) : SimpleGraph V :=
  graphF2SymmetricDifference
    (binaryTransportSupportGraph G hq hreg) (triangleFreeEdgeGraph G)

instance binaryTransportResidualGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, G.degree v = q) :
    DecidableRel (binaryTransportResidualGraph G hq hreg).Adj := by
  unfold binaryTransportResidualGraph
  infer_instance

/-- At even ambient degree, the triangle-free-edge graph is even-valent:
all remaining incident edges occur in triangle pairs. -/
theorem triangleFreeEdgeGraph_even_degree_of_evenRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) (x : V) :
    Even ((triangleFreeEdgeGraph G).degree x) := by
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have htfcard : (triangleFreeNeighbors G x).card =
      (triangleFreeEdgeGraph G).degree x := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
  rw [hreg x, htfcard] at hlocal
  obtain ⟨a, ha⟩ := hq
  refine ⟨a - (G.induce (G.neighborSet x)).edgeFinset.card, ?_⟩
  omega

/-- The residual transport graph is Eulerian. -/
theorem binaryTransportResidualGraph_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) (x : V) :
    Even ((binaryTransportResidualGraph G hq hreg).degree x) := by
  change Even ((graphF2SymmetricDifference
    (binaryTransportSupportGraph G hq hreg)
    (triangleFreeEdgeGraph G)).degree x)
  apply graphF2SymmetricDifference_even_degree_of_degree_cast_eq
  intro v
  rw [ZMod.natCast_eq_zero_iff_even.mpr
      (binaryTransportSupportGraph_even_degree G hq hreg v),
    ZMod.natCast_eq_zero_iff_even.mpr
      (triangleFreeEdgeGraph_even_degree_of_evenRegular G hfree hq hreg v)]

/-- The residual transport graph has no ambient edges: `K ∩ A = ⊥`. -/
theorem binaryTransportResidualGraph_inf_eq_bot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) :
    binaryTransportResidualGraph G hq hreg ⊓ G = ⊥ := by
  ext x y
  simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false]
  rintro ⟨hK, hG⟩
  change (graphF2SymmetricDifference
    (binaryTransportSupportGraph G hq hreg)
    (triangleFreeEdgeGraph G)).Adj x y at hK
  have hiff := binaryTransportSupportGraph_adj_iff_triangleFreeEdgeGraph_adj_of_adj
    G hfree hq hreg hG
  have hxor := (graphF2SymmetricDifference_adj_iff
    (binaryTransportSupportGraph G hq hreg) (triangleFreeEdgeGraph G) x y).mp hK
  rcases hxor with ⟨hH, hnT⟩ | ⟨hnH, hT⟩
  · exact hnT (hiff.mp hH)
  · exact hnH (hiff.mpr hT)

end Erdos85

#print axioms Erdos85.graphF2SymmetricDifference_adj_iff
#print axioms Erdos85.triangleFreeEdgeGraph_even_degree_of_evenRegular
#print axioms Erdos85.binaryTransportResidualGraph_even_degree
#print axioms Erdos85.binaryTransportResidualGraph_inf_eq_bot
