import Proofs.Erdos85OneHighStructuralTerminalInterface

/-! # A pinned normal form for the one-high mate-miss terminal

The mate-miss hexagon is not, by itself, contradictory.  This file records
the exact common-neighbor information forced by its three specified
nonedges and packages the remaining terminal as a strictly normalized
configuration.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A mate-miss hexagon with the two common neighborhoods across its
distinguished missing chords pinned to their visible rim vertices. -/
structure OneHighPinnedMateMissHexagon
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    extends OneHighMateMissHexagon G v where
  xa_common : G.neighborFinset x ∩ G.neighborFinset a = {y}
  yb_common : G.neighborFinset y ∩ G.neighborFinset b = {x}

private theorem common_eq_singleton_of_common_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y z : V}
    (hxy : x ≠ y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    G.neighborFinset x ∩ G.neighborFinset y = {z} := by
  have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x z).mpr hxz,
        (G.mem_neighborFinset y z).mpr hyz⟩
  have hsub : ({z} : Finset V) ⊆
      G.neighborFinset x ∩ G.neighborFinset y := by
    simpa using hzmem
  have hcard : (G.neighborFinset x ∩ G.neighborFinset y).card ≤
      ({z} : Finset V).card := by
    rw [Finset.card_singleton]
    exact common_le_one_of_not_containsC4 hfree x y hxy
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- Every mate-miss hexagon in a `C₄`-free graph has the pinned normal form.
In particular, `y` is the unique common neighbor of `x,a`, and `x` is the
unique common neighbor of `y,b`. -/
noncomputable def OneHighMateMissHexagon.pin
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (H : OneHighMateMissHexagon G v) :
    OneHighPinnedMateMissHexagon G v := by
  have hbranch := secondLayerBranch_pairwiseDisjoint G hfree v
  have hxa : H.x ≠ H.a := by
    intro heq
    exact (Finset.disjoint_left.mp
      (hbranch (by simp) (by simp) H.source_ne_u))
      H.x_mem (heq ▸ H.a_mem)
  have hyb : H.y ≠ H.b := by
    intro heq
    exact (Finset.disjoint_left.mp
      (hbranch (by simp) (by simp) H.source_ne_w))
      H.y_mem (heq ▸ H.b_mem)
  refine ⟨H, ?_, ?_⟩
  · exact common_eq_singleton_of_common_neighbor G hfree hxa
      H.xy_edge H.ya_edge.symm
  · exact common_eq_singleton_of_common_neighbor G hfree hyb
      H.xy_edge.symm H.bx_edge

/-- The genuinely residual terminal obligation after all mate-miss witnesses
have been normalized by their forced common-neighbor equalities. -/
def OneHighPinnedMateMissHexagonSectorExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (_p : OneHighRawV2Presentation G hfree v),
      Nonempty (OneHighPinnedMateMissHexagon G v) → False

/-- It suffices to exclude pinned mate-miss hexagons: `C₄`-freeness upgrades
every witness in the original terminal sector to the pinned normal form. -/
theorem oneHighMateMissHexagonSectorExcluded_of_pinned
    (h : OneHighPinnedMateMissHexagonSectorExcluded) :
    OneHighMateMissHexagonSectorExcluded := by
  intro G _ _ _ hfree hmin hHigh v hv p H
  exact h G inferInstance inferInstance inferInstance hfree hmin hHigh hv p
    ⟨H.some.pin G hfree⟩

end

end Erdos85
