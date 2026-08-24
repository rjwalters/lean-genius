import Proofs.Erdos85OneHighOddKeyCycleExtraction
import Proofs.Erdos85BinaryTransportResidualGraph

/-!
# A specified edge of an even graph lies on a cycle

The earlier cycle-extraction API only produced some cycle from a nonempty
even-valent graph.  The transport argument needs the sharper fact that a
chosen edge lies on a cycle.  Deleting that edge makes one endpoint odd; the
handshaking lemma in its connected component forces the other endpoint into
the same component, giving the required return path.
-/

open SimpleGraph

namespace Erdos85

/-- Every specified edge of a finite even-valent simple graph lies on a
cycle. -/
theorem exists_isCycle_mem_edge_of_even_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) {a b : V} (hab : G.Adj a b) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(a, b) ∈ p.edges := by
  classical
  let K := G.deleteEdges {s(a, b)}
  letI : DecidableRel K.Adj := by
    dsimp [K]
    infer_instance
  have hKa : K.neighborFinset a = (G.neighborFinset a).erase b := by
    ext x
    simp [K, SimpleGraph.mem_neighborFinset, hab.ne, and_comm]
  have hoddA : Odd (K.degree a) := by
    rw [← K.card_neighborFinset_eq_degree, hKa, Finset.card_erase_of_mem]
    · rw [← Nat.not_even_iff_odd]
      intro hsub
      have hpos : 1 ≤ (G.neighborFinset a).card :=
        Finset.card_pos.mpr
          ⟨b, by simpa [SimpleGraph.mem_neighborFinset] using hab⟩
      have heq := (Nat.even_sub hpos).mp hsub
      have hone := heq.mp (by
        rw [G.card_neighborFinset_eq_degree]
        exact heven a)
      exact Nat.not_even_one hone
    · simpa [SimpleGraph.mem_neighborFinset] using hab
  let C : K.ConnectedComponent := K.connectedComponentMk a
  let T : SimpleGraph C.supp := C.toSimpleGraph
  letI : DecidableRel T.Adj := by
    dsimp [T, ConnectedComponent.toSimpleGraph]
    infer_instance
  have haC : a ∈ C.supp := by simp [C]
  let aC : C.supp := ⟨a, haC⟩
  have hdegA : T.degree aC = K.degree aC.1 := by
    have hs : K.neighborSet a ⊆ C.supp := by
      intro y hay
      exact C.mem_supp_of_adj_mem_supp haC hay
    convert K.degree_induce_of_neighborSet_subset (v := aC) hs using 1
    dsimp [T, ConnectedComponent.toSimpleGraph]
    unfold degree
    congr 1
  have hoddAC : Odd (T.degree aC) := by rwa [hdegA]
  obtain ⟨w, hwa, hoddw⟩ :=
    T.exists_ne_odd_degree_of_exists_odd_degree aC hoddAC
  have hdegw : T.degree w = K.degree w.1 := by
    have hs : K.neighborSet w.1 ⊆ C.supp := by
      intro y hwy
      exact C.mem_supp_of_adj_mem_supp w.2 hwy
    convert K.degree_induce_of_neighborSet_subset (v := w) hs using 1
    dsimp [T, ConnectedComponent.toSimpleGraph]
    unfold degree
    congr 1
  have hoddKw : Odd (K.degree w.1) := by rwa [← hdegw]
  have hwab : w.1 = a ∨ w.1 = b := by
    by_contra hn
    simp only [not_or] at hn
    have hKsame : K.neighborFinset w.1 = G.neighborFinset w.1 := by
      ext y
      simp only [K, SimpleGraph.mem_neighborFinset, deleteEdges_adj,
        Set.mem_singleton_iff, and_iff_left_iff_imp]
      intro _ he
      rw [Sym2.eq_iff] at he
      rcases he with h | h
      · exact hn.1 h.1
      · exact hn.2 h.1
    have hevenK : Even (K.degree w.1) := by
      rw [← K.card_neighborFinset_eq_degree, hKsame,
        G.card_neighborFinset_eq_degree]
      exact heven w.1
    exact Nat.not_even_iff_odd.mpr hoddKw hevenK
  have hwb : w.1 = b := hwab.resolve_left (by
    intro hwa'
    apply hwa
    apply Subtype.ext
    exact hwa')
  have hbC : b ∈ C.supp := hwb ▸ w.2
  apply adj_and_reachable_delete_edges_iff_exists_cycle.mp
  refine ⟨hab, ?_⟩
  simpa [K, C] using C.reachable_of_mem_supp haC hbC

/-- Every triangle-free ambient edge lies on a triangle-free-edge cycle in a
C4-free even-regular graph. -/
theorem triangleFreeEdgeGraph_edge_exists_cycle_of_evenRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) {a b : V}
    (hab : (triangleFreeEdgeGraph G).Adj a b) :
    ∃ (u : V) (p : (triangleFreeEdgeGraph G).Walk u u),
      p.IsCycle ∧ s(a, b) ∈ p.edges := by
  apply exists_isCycle_mem_edge_of_even_degrees
    (triangleFreeEdgeGraph G) _ hab
  exact triangleFreeEdgeGraph_even_degree_of_evenRegular G hfree hq hreg

/-- Every residual binary-transport edge lies on a residual transport cycle
under the intended even-regular C4-free hypotheses. -/
theorem binaryTransportResidualGraph_edge_exists_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) {a b : V}
    (hab : (binaryTransportResidualGraph G hq hreg).Adj a b) :
    ∃ (u : V) (p : (binaryTransportResidualGraph G hq hreg).Walk u u),
      p.IsCycle ∧ s(a, b) ∈ p.edges := by
  apply exists_isCycle_mem_edge_of_even_degrees
    (binaryTransportResidualGraph G hq hreg) _ hab
  exact binaryTransportResidualGraph_even_degree G hfree hq hreg

end Erdos85

#print axioms Erdos85.exists_isCycle_mem_edge_of_even_degrees
#print axioms Erdos85.triangleFreeEdgeGraph_edge_exists_cycle_of_evenRegular
#print axioms Erdos85.binaryTransportResidualGraph_edge_exists_cycle
