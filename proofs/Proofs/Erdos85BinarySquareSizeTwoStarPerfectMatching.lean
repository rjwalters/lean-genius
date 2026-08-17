import Proofs.Erdos85BinarySquareCrossSelectorUnique
import Proofs.Erdos85BinarySquareSizeTwoOwnerLineGraph

/-! # Selector stars become perfect matchings in other coordinates -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ambient vertices whose selector in coordinate `c` contains the point
`u`.  Under the selector-edge bijection, this is the star at `u`. -/
def sizeTwoSelectorStarIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (u : c.supp) :=
  {x : V // u.1 ∈
    componentNeighborFinset G (secondOrderDefectGraph G) c x}

/-- Every selector into a normalized size-two component has exactly two
points. -/
theorem binarySquare_regular_sizeTwoPart_selector_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (hd : d.supp.ncard = q * 2) (x : V) :
    (componentNeighborFinset G (secondOrderDefectGraph G) d x).card = 2 := by
  have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk x) d (x := x) rfl
  rw [hd] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

/-- **Star-perfect-matching theorem.**  Fix a point `u` in a normalized
size-two coordinate `c`.  The selectors in a distinct normalized size-two
coordinate `d`, indexed by the ambient vertices in the selector star at `u`,
are pairwise disjoint two-element sets and contain every point of `d` exactly
once. -/
theorem binarySquare_regular_sizeTwoTarget_selectorStar_isPerfectMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (hd : d.supp.ncard = q * 2)
    (u : c.supp) :
    (∀ x : sizeTwoSelectorStarIndex G c u,
      (componentNeighborFinset G (secondOrderDefectGraph G) d x.1).card = 2) ∧
    (∀ x y : sizeTwoSelectorStarIndex G c u, x ≠ y →
      Disjoint
        (componentNeighborFinset G (secondOrderDefectGraph G) d x.1)
        (componentNeighborFinset G (secondOrderDefectGraph G) d y.1)) ∧
    (∀ v : d.supp, ∃! x : sizeTwoSelectorStarIndex G c u,
      v.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) d x.1) := by
  constructor
  · intro x
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard d hd x.1
  constructor
  · intro x y hxy
    have hval : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    have hcOwner :
        (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 y.1 := by
      rw [componentOwnerGraph_adj]
      exact ⟨hval, ⟨u.1, Finset.mem_inter.mpr ⟨x.2, y.2⟩⟩⟩
    exact componentOwnerGraph_adj_implies_other_selector_disjoint
      G hfree hcd hcOwner
  · intro v
    obtain ⟨x, hx, hxUnique⟩ :=
      existsUnique_mem_cross_componentNeighborFinsets G hfree c d hcd u v
    let xs : sizeTwoSelectorStarIndex G c u := ⟨x, hx.1⟩
    refine ⟨xs, hx.2, ?_⟩
    intro ys hys
    apply Subtype.ext
    exact hxUnique ys.1 ⟨ys.2, hys⟩

end

end Erdos85
