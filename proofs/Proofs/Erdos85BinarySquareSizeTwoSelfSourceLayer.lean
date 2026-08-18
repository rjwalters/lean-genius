import Proofs.Erdos85BinarySquareSizeTwoSourceLineGraph
import Proofs.Erdos85BinarySquareSizeTwoSelfIndexedBlock

/-! # Self-source geometry of a normalized size-two component -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The loopless common-neighbor graph of a simple graph. -/
def distinctCommonNeighborGraph {W : Type*} (H : SimpleGraph W) : SimpleGraph W where
  Adj u v := u ≠ v ∧ ∃ x, H.Adj x u ∧ H.Adj x v
  symm := ⟨by
    rintro u v ⟨huv, x, hxu, hxv⟩
    exact ⟨huv.symm, x, hxv, hxu⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

private theorem finset_eq_pair_of_card_two_of_mem
    {α : Type*} [DecidableEq α] {s : Finset α} {u v : α}
    (hcard : s.card = 2) (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) :
    s = {u, v} := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hcard
  rw [hs] at hu hv ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  aesop

/-- **Self-source distance-two identity.**  The selector edges contributed by
a size-two component to its own selector graph are exactly the distinct pairs
having a common neighbor in the ambient graph induced on that component. -/
theorem binarySquare_regular_sizeTwoPart_selfSourceSelectorGraph_eq_commonNeighborGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    sourceIndexedSizeTwoSelectorGraph G c c =
      distinctCommonNeighborGraph (G.induce c.supp) := by
  ext u v
  constructor
  · rintro ⟨huv, x, hx⟩
    have hu : u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x.1 := by
      rw [hx]
      simp
    have hv : v.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x.1 := by
      rw [hx]
      simp
    exact ⟨huv, x,
      (mem_componentNeighborFinset_internal_iff_induced_adj G c x u).mp hu,
      (mem_componentNeighborFinset_internal_iff_induced_adj G c x v).mp hv⟩
  · rintro ⟨huv, x, hxu, hxv⟩
    have hu :=
      (mem_componentNeighborFinset_internal_iff_induced_adj G c x u).mpr hxu
    have hv :=
      (mem_componentNeighborFinset_internal_iff_induced_adj G c x v).mpr hxv
    have htwo :
        (componentNeighborFinset G (secondOrderDefectGraph G) c x.1).card = 2 :=
      binarySquare_regular_sizeTwoPart_selector_card
        G hfree hq hreg hcard c hc x.1
    exact ⟨huv, x,
      finset_eq_pair_of_card_two_of_mem htwo hu hv
        (fun h => huv (Subtype.ext h))⟩

/-- The self-restricted owner line graph is the distance-two graph of the
internal ambient 2-factor: two labels are owner-adjacent exactly when their
internal neighborhoods meet. -/
theorem binarySquare_regular_sizeTwoPart_selfRestrictedOwner_adj_iff_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (x y : c.supp) :
    (restrictedComponentOwnerGraph G c c).Adj x y ↔
      x ≠ y ∧ ∃ z : c.supp,
        (G.induce c.supp).Adj x z ∧ (G.induce c.supp).Adj y z := by
  change
    (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 y.1 ↔ _
  rw [binarySquare_regular_sizeTwoPart_ownerAdj_iff_selector_intersects]
  constructor
  · rintro ⟨hxy, hinter⟩
    obtain ⟨z, hz⟩ := hinter
    have hzData := Finset.mem_inter.mp hz
    have hzSupp : z ∈ c.supp :=
      (ConnectedComponent.mem_supp_iff c z).mpr
        (Finset.mem_filter.mp hzData.1).2
    let zc : c.supp := ⟨z, hzSupp⟩
    exact ⟨fun h => hxy (congrArg Subtype.val h), zc,
      (mem_componentNeighborFinset_internal_iff_induced_adj G c x zc).mp hzData.1,
      (mem_componentNeighborFinset_internal_iff_induced_adj G c y zc).mp hzData.2⟩
  · rintro ⟨hxy, z, hxz, hyz⟩
    refine ⟨fun h => hxy (Subtype.ext h), ?_⟩
    exact ⟨z.1, Finset.mem_inter.mpr
      ⟨(mem_componentNeighborFinset_internal_iff_induced_adj G c x z).mpr hxz,
        (mem_componentNeighborFinset_internal_iff_induced_adj G c y z).mpr hyz⟩⟩

end

end Erdos85
