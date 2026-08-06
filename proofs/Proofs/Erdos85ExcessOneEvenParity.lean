import Proofs.Erdos85ExcessDefectRegular

/-!
# Even-degree parity kill at excess one

At excess one (`n = d(d-1) + 4`) the combined second-order defect graph
is three-regular.  If the antipodal relation is moreover two-regular,
the disjointness of the two defect neighbourhoods leaves exactly one
triangle-free incident edge at every vertex.  The remaining `d - 1`
neighbours are paired off by the local matching of the `C₄`-free link,
so `d = 2·(matched pairs) + 1` is odd.

Contrapositively, an even-degree excess-one graph cannot carry a
two-regular antipodal relation.  This is the parity half of the
excess-one classification; the odd degrees are handled by the `K₄`
spectral terminal.
-/

open SimpleGraph

namespace Erdos85

/-- At excess one, a two-regular antipodal relation forces exactly one
triangle-free incident edge at every vertex.  No degree parity is
assumed: the count is read off from the three-regular defect
neighbourhood, which splits disjointly into two antipodal neighbours
and the triangle-free ones. -/
theorem excessOne_triangleFreeNeighbors_card_eq_one_of_antipodal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2) (x : V) :
    (triangleFreeNeighbors G x).card = 1 := by
  have hdeg := secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree hreg (e := 1) (by omega) x
  rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    secondOrderDefectGraph_neighborFinset G x,
    Finset.card_union_of_disjoint
      (disjoint_antipodal_triangleFreeNeighbors G x), hanti x] at hdeg
  omega

/-- **Even-degree parity kill at excess one.**  A `C₄`-free `d`-regular
graph on `d(d-1) + 4` vertices with a two-regular antipodal relation has
odd degree: the unique triangle-free incident edge plus the perfect
local matching of the remaining neighbours give `d = 2k + 1`. -/
theorem excessOne_degree_odd_of_antipodal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2) :
    Odd d := by
  have hpos : 0 < Fintype.card V := by
    rw [hcard]
    omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
  have hone := excessOne_triangleFreeNeighbors_card_eq_one_of_antipodal_two
    G hfree hreg hcard hanti x
  have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
    G hfree hreg x
  have hhand :
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) =
        2 * (G.induce (G.neighborSet x)).edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges (G.induce (G.neighborSet x))
  rw [hone, hhand] at hsum
  exact ⟨(G.induce (G.neighborSet x)).edgeFinset.card, by omega⟩

/-- Contradiction form of the parity kill: even degree is impossible at
excess one once the antipodal relation is two-regular. -/
theorem excessOne_even_degree_kill
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2)
    (heven : Even d) : False := by
  obtain ⟨k, hk⟩ := excessOne_degree_odd_of_antipodal_two
    G hfree hreg hcard hanti
  obtain ⟨m, hm⟩ := heven
  omega

end Erdos85
