import Proofs.Erdos85SixteenVertexC4EdgeBound

/-!
# Cut incidences from a sixteen-vertex C4-free sector

For a vertex set `s`, count ordered incidences from `s` to its complement.
The degree sum on `s` is twice the number of induced edges plus this cut
count.  Consequently, a six-regular ambient graph sends at least 26
incidences out of any sixteen-vertex sector whose induced graph is C4-free.
-/

open SimpleGraph

namespace Erdos85

/-- Ordered edge incidences whose first endpoint lies in `s` and whose second
endpoint lies outside `s`. -/
def graphCutIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] : ℕ :=
  ∑ v : s, (G.neighborFinset v.1 \ s.toFinset).card

/-- At one vertex, induced degree plus outward cut degree is ambient degree. -/
theorem degree_induce_add_cutDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] (v : s) :
    (G.induce s).degree v +
        (G.neighborFinset v.1 \ s.toFinset).card = G.degree v.1 := by
  have hind : (G.induce s).degree v =
      (G.neighborFinset v.1 ∩ s.toFinset).card := by
    have hmap := G.map_neighborFinset_induce v
    have hcard := congrArg Finset.card hmap
    simpa only [Finset.card_map, G.card_neighborFinset_eq_degree,
      (G.induce s).card_neighborFinset_eq_degree] using hcard
  rw [hind, ← G.card_neighborFinset_eq_degree]
  exact Finset.card_inter_add_card_sdiff _ _

/-- The degree sum on `s` splits into twice the induced-edge count and the
ordered cut-incidence count. -/
theorem graphCutIncidenceCount_add_twice_card_induced_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] :
    graphCutIncidenceCount G s + 2 * (G.induce s).edgeFinset.card =
      ∑ v : s, G.degree v.1 := by
  have hsum :
      (∑ v : s, (G.induce s).degree v) + graphCutIncidenceCount G s =
        ∑ v : s, G.degree v.1 := by
    rw [graphCutIncidenceCount, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact degree_induce_add_cutDegree G s v
  rw [(G.induce s).sum_degrees_eq_twice_card_edges] at hsum
  omega

/-- **Sixteen-sector cut bound.**  In a six-regular ambient graph, a
sixteen-vertex sector inducing a C4-free graph has at least 26 outward edge
incidences. -/
theorem twentySix_le_graphCutIncidenceCount_of_sixRegular_card_sixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (hcard : Fintype.card s = 16)
    (hreg : ∀ v : V, G.degree v = 6)
    (hfree : ¬ containsC4 s (G.induce s)) :
    26 ≤ graphCutIncidenceCount G s := by
  have hedge := card_edges_le_thirtyFive_of_card_sixteen_of_not_containsC4
    (G.induce s) hcard hfree
  have hsplit := graphCutIncidenceCount_add_twice_card_induced_edges G s
  have hsum : (∑ v : s, G.degree v.1) = 96 := by
    simp_rw [hreg]
    simp [hcard]
  rw [hsum] at hsplit
  omega

end Erdos85

#print axioms Erdos85.degree_induce_add_cutDegree
#print axioms Erdos85.graphCutIncidenceCount_add_twice_card_induced_edges
#print axioms
  Erdos85.twentySix_le_graphCutIncidenceCount_of_sixRegular_card_sixteen
