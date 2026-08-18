import Proofs.Erdos85BinarySquareSizeTwoCrossOwnerReachability

/-! # Components of a cross block and its owner factor are equivalent -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Send an owner-factor component to the cross-block component containing
its source-side vertices. -/
def restrictedOwnerComponentToCross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent) :
    (restrictedComponentOwnerGraph G source target).ConnectedComponent →
      (componentCrossBipartiteGraph G source target).ConnectedComponent :=
  ConnectedComponent.lift
    (fun x => (componentCrossBipartiteGraph G source target).connectedComponentMk
      (Sum.inl x))
    (fun x y p _hp => ConnectedComponent.eq.mpr
      ((restrictedOwner_reachable_iff_cross_inl_reachable
        G hfree source target x y).mp p.reachable))

@[simp] theorem restrictedOwnerComponentToCross_mk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x : source.supp) :
    restrictedOwnerComponentToCross G hfree source target
        ((restrictedComponentOwnerGraph G source target).connectedComponentMk x) =
      (componentCrossBipartiteGraph G source target).connectedComponentMk
        (Sum.inl x) := by
  rfl

/-- The component map reflects equality. -/
theorem restrictedOwnerComponentToCross_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent) :
    Function.Injective
      (restrictedOwnerComponentToCross G hfree source target) := by
  intro a b
  refine ConnectedComponent.ind₂ ?_ a b
  intro x y hxy
  simp only [restrictedOwnerComponentToCross_mk] at hxy ⊢
  apply ConnectedComponent.eq.mpr
  apply (restrictedOwner_reachable_iff_cross_inl_reachable
    G hfree source target x y).mpr
  exact ConnectedComponent.eq.mp hxy

/-- In the size-two setting every cross-block component meets the source
side, so the owner-to-cross component map is surjective. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentToCross_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2) :
    Function.Surjective
      (restrictedOwnerComponentToCross G hfree source target) := by
  intro e
  refine ConnectedComponent.ind ?_ e
  intro v
  cases v with
  | inl x =>
    exact ⟨(restrictedComponentOwnerGraph G source target).connectedComponentMk x,
      rfl⟩
  | inr z =>
    have hcardCross : (componentCrossNeighborFinset G source z).card = 2 := by
      rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
      exact binarySquare_regular_sizeTwoPart_selector_card
        G hfree hq hreg hcard source hsource z.1
    obtain ⟨x, hx⟩ : (componentCrossNeighborFinset G source z).Nonempty := by
      exact Finset.card_pos.mp (by omega)
    refine ⟨(restrictedComponentOwnerGraph G source target).connectedComponentMk x,
      ?_⟩
    rw [restrictedOwnerComponentToCross_mk]
    apply ConnectedComponent.eq.mpr
    have hxz : G.Adj x.1 z.1 := (Finset.mem_filter.mp hx).2.symm
    exact (show (componentCrossBipartiteGraph G source target).Adj
      (Sum.inl x) (Sum.inr z) from hxz).reachable

/-- Canonical equivalence between the components of a paired restricted owner
factor and the cycles of its size-two cross block. -/
def binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2) :
    (restrictedComponentOwnerGraph G source target).ConnectedComponent ≃
      (componentCrossBipartiteGraph G source target).ConnectedComponent :=
  Equiv.ofBijective (restrictedOwnerComponentToCross G hfree source target)
    ⟨restrictedOwnerComponentToCross_injective G hfree source target,
      binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentToCross_surjective
        G hfree hq hreg hcard source target hsource⟩

/-- At order 64, each restricted owner factor between two distinct size-two
coordinates has at most five cycle components. -/
theorem orderSixtyFour_regular_twoSizeTwoParts_restrictedOwnerComponent_card_le_five
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hst : source ≠ target)
    (hsource : source.supp.ncard = 16)
    (htarget : target.supp.ncard = 16) :
    Fintype.card
        (restrictedComponentOwnerGraph G source target).ConnectedComponent ≤ 5 := by
  let e := binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
    G hfree (by omega) hreg (by decide) source target (by omega)
  rw [Fintype.card_congr e]
  exact orderSixtyFour_regular_twoSizeTwoParts_crossComponent_card_le_five
    G hfree hreg source target hst hsource htarget

end

end Erdos85
