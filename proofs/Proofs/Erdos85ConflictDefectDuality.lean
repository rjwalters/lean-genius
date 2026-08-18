import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85ConflictRegular

/-!
# Conflict--defect duality in the positive-excess band

For a `C₄`-free graph, two distinct vertices fail to conflict exactly when
they form one of the two second-order defect relations.  Thus the combined
defect graph is literally the complement of the common-neighbour conflict
graph.  This identifies safe one-vertex attachment sets with defect cliques.

At positive excess `e`, defect regularity then gives the sharp elementary cap
`e + 3` on every safe selector.  In the plateau range `e ≤ d - 4`, this is
strictly below the `d` vertices required for a degree-`d` attachment.  Hence
failure of the direct one-vertex attachment is automatic throughout that
range; any plateau-to-boundary argument must use structure beyond the bare
selector obstruction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The combined second-order defect graph is the complement of the
common-neighbour conflict graph. -/
theorem commonNeighborConflict_compl_eq_secondOrderDefectGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    (commonNeighborConflict G)ᶜ = secondOrderDefectGraph G := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  · have hcard := card_common_eq_if_secondOrderDefect G hfree x y hxy
    rw [SimpleGraph.compl_adj, commonNeighborConflict_adj_iff]
    by_cases hD : (secondOrderDefectGraph G).Adj x y
    · have hmem : y ∈ (secondOrderDefectGraph G).neighborFinset x :=
        (SimpleGraph.mem_neighborFinset (secondOrderDefectGraph G) x y).2 hD
      rw [if_pos hmem] at hcard
      constructor
      · exact fun _ => hD
      · intro _
        refine ⟨hxy, ?_⟩
        rintro ⟨_, hnonempty⟩
        have hnezero :
            (G.neighborFinset x ∩ G.neighborFinset y).card ≠ 0 :=
          Finset.card_ne_zero.mpr hnonempty
        exact hnezero hcard
    · have hmem : y ∉ (secondOrderDefectGraph G).neighborFinset x := by
        simpa [SimpleGraph.mem_neighborFinset] using hD
      rw [if_neg hmem] at hcard
      constructor
      · rintro ⟨_, hnoConflict⟩
        have hempty : ¬(G.neighborFinset x ∩ G.neighborFinset y).Nonempty :=
          fun hnonempty => hnoConflict ⟨hxy, hnonempty⟩
        have hz : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 :=
          Finset.card_eq_zero.mpr
            (Finset.not_nonempty_iff_eq_empty.mp hempty)
        omega
      · exact fun h => (hD h).elim

/-- At order `d(d-1)+3+e`, every safe attachment set has at most `e+3`
vertices. -/
theorem commonNeighborIndependent_card_le_excess_add_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (S : Finset V) (hS : CommonNeighborIndependent G S) :
    S.card ≤ e + 3 := by
  have hind : (commonNeighborConflict G).IsIndepSet S :=
    (commonNeighborIndependent_iff_isIndepSet G S).1 hS
  have hle := hind.card_le_indepNum
  have hcap := indepNum_commonNeighborConflict_le_excess G hfree hreg
  rw [hcard] at hcap
  have hsimp : d * (d - 1) + 3 + e - d * (d - 1) = e + 3 := by
    omega
  rw [hsimp] at hcap
  exact hle.trans hcap

/-- In the positive-excess plateau band, a safe selector is strictly too
small to attach a new vertex of degree `d`. -/
theorem commonNeighborIndependent_card_lt_degree_of_excess_band
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hd : 4 ≤ d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (he : e ≤ d - 4)
    (S : Finset V) (hS : CommonNeighborIndependent G S) :
    S.card < d := by
  have hcap := commonNeighborIndependent_card_le_excess_add_three
    G hfree hreg hcard S hS
  omega

end

end Erdos85
