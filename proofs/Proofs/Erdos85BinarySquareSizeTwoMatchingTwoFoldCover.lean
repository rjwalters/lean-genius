import Proofs.Erdos85BinarySquareSizeTwoMatchingOverlap

/-! # Selector-star matchings form a two-fold cover -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Two-fold cover law.**  Fix two normalized size-two coordinates `c,d`.
For every ambient vertex `x`, its target selector edge in `d` belongs to
exactly the two matching pages indexed by the endpoints of its source
selector in `c`. -/
theorem binarySquare_regular_twoSizeTwoParts_targetEdge_mem_exactly_sourceEndpointPages
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (x : V) :
    ∃ u v : c.supp, u ≠ v ∧
      componentNeighborFinset G (secondOrderDefectGraph G) c x = {u.1, v.1} ∧
      ∀ w : c.supp,
        componentNeighborFinset G (secondOrderDefectGraph G) d x ∈
            sizeTwoSelectorStarMatchingEdgeSet G c d w ↔
          w = u ∨ w = v := by
  let D := secondOrderDefectGraph G
  have htwo : (componentNeighborFinset G D c x).card = 2 :=
    binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard c hc x
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp htwo
  have haMem : a ∈ componentNeighborFinset G D c x := by
    rw [hpair]
    simp [hab]
  have hbMem : b ∈ componentNeighborFinset G D c x := by
    rw [hpair]
    simp
  have haSupp : a ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c a).mpr
      (Finset.mem_filter.mp haMem).2
  have hbSupp : b ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c b).mpr
      (Finset.mem_filter.mp hbMem).2
  let u : c.supp := ⟨a, haSupp⟩
  let v : c.supp := ⟨b, hbSupp⟩
  have huv : u ≠ v := by
    intro huv
    exact hab (congrArg Subtype.val huv)
  refine ⟨u, v, huv, hpair, ?_⟩
  intro w
  constructor
  · intro hw
    obtain ⟨y, hy⟩ := hw
    change componentNeighborFinset G D d y.1 =
      componentNeighborFinset G D d x at hy
    have hyx : y.1 = x :=
      binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
        G hfree hq hreg hcard d hd hy
    have hwMem : w.1 ∈ componentNeighborFinset G D c x := by
      simpa [hyx] using y.2
    rw [hpair] at hwMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwMem
    rcases hwMem with hwu | hwv
    · exact Or.inl (Subtype.ext hwu)
    · exact Or.inr (Subtype.ext hwv)
  · intro hw
    rcases hw with rfl | rfl
    · let xs : sizeTwoSelectorStarIndex G c u := ⟨x, haMem⟩
      exact ⟨xs, rfl⟩
    · let xs : sizeTwoSelectorStarIndex G c v := ⟨x, hbMem⟩
      exact ⟨xs, rfl⟩

end

end Erdos85
