import Proofs.Erdos85OrderFortyNineSevenHighZeroFiber
import Proofs.Erdos85OrderFortyNineSupportPartitions

/-!
# Structural quotient laws for the seven-high empty-triple case

The finite empty-layer checker uses two graph-side facts.  Every low vertex
has a unique common neighbor with each high vertex, and the total high-support
weight across its neighborhood is seven.  These are independent of the later
finite enumeration and are packaged here at the exact `h = 7`, `t = 0`
interface.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- For a low vertex and a labeled high point, exactly one graph neighbor of
the low vertex carries that high label.  Equivalently, the eight-neighbor
partition clauses used by the `t = 0` checker are exactly-one constraints. -/
theorem sevenHigh_t0_existsUnique_neighbor_carrying_label
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    {y : Fin 49} (hy : G.degree y = 7) (w : Fin 7) :
    ∃! x : Fin 49,
      x ∈ G.neighborFinset y ∧ w ∈ sevenHighLabeledSupport G e x := by
  have hw : (e.symm w).1 ∈ orderFortyNineHighVertices G := (e.symm w).2
  simpa [mem_sevenHighLabeledSupport_iff] using
    (orderFortyNine_low_neighborhood_partitions_highs
      G hfree hmin (Fintype.card_fin 49) hy hw)

/-- In the seven-high stratum the support sizes on the seven neighbors of a
low vertex sum to seven.  This is the pointwise equation behind the
`#P - #E = |support|` empty/singleton/pair quotient law. -/
theorem sevenHigh_t0_sum_support_card_over_lowNeighborhood_eq_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    {y : Fin 49} (hy : G.degree y = 7) :
    (∑ x ∈ G.neighborFinset y,
      (orderFortyNineHighSupport G x).card) = 7 := by
  simpa [orderFortyNineHighSupport, hHigh] using
    (orderFortyNine_sum_highIncidence_over_lowNeighborhood
      G hfree hmin (Fintype.card_fin 49) hy)

/-- Arithmetic core of the local quotient.  Here `p`, `s`, and `e` count
pair-, singleton-, and empty-support low neighbors, while `k` is the support
size of the root.  The degree partition and the support-weight identity force
`p - e = k` without truncated subtraction. -/
theorem sevenHigh_t0_local_quotient_arithmetic
    {p s e k : Nat}
    (hdegree : p + s + e + k = 7)
    (hweight : 2 * p + s = 7) :
    p = e + k := by
  omega

/-- A pair-support low vertex has at most one empty-support low neighbor. -/
theorem sevenHigh_t0_pair_empty_neighbor_bound
    {p s e : Nat}
    (hdegree : p + s + e + 2 = 7)
    (hweight : 2 * p + s = 7) :
    e ≤ 1 := by
  omega

/-- A singleton-support low vertex has at most two empty-support low
neighbors. -/
theorem sevenHigh_t0_singleton_empty_neighbor_bound
    {p s e : Nat}
    (hdegree : p + s + e + 1 = 7)
    (hweight : 2 * p + s = 7) :
    e ≤ 2 := by
  omega

/-- An empty-support low vertex has at most three empty-support low
neighbors. -/
theorem sevenHigh_t0_empty_empty_neighbor_bound
    {p s e : Nat}
    (hdegree : p + s + e = 7)
    (hweight : 2 * p + s = 7) :
    e ≤ 3 := by
  omega

end

end Erdos85

#print axioms Erdos85.sevenHigh_t0_existsUnique_neighbor_carrying_label
#print axioms Erdos85.sevenHigh_t0_sum_support_card_over_lowNeighborhood_eq_seven
#print axioms Erdos85.sevenHigh_t0_local_quotient_arithmetic
