import Proofs.Erdos85OrderSixtyFourFiveCrossComponentsOwnerProfile

/-! # Opposite twins in four-vertex two-regular components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every four-vertex connected component of a finite two-regular graph is a
four-cycle. In particular it contains an opposite pair: distinct nonadjacent
vertices having exactly the same two neighbors. -/
theorem twoRegular_component_order_four_exists_oppositeTwins
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (hdeg : ∀ v, F.degree v = 2)
    (a : F.ConnectedComponent) (ha : a.supp.ncard = 4) :
    ∃ x y : W, x ≠ y ∧ x ∈ a.supp ∧ y ∈ a.supp ∧
      ¬ F.Adj x y ∧ F.neighborFinset x = F.neighborFinset y := by
  classical
  let S := a.supp.toFinite.toFinset
  have hScard : S.card = 4 := by
    simpa [S] using
      (Set.ncard_eq_toFinset_card a.supp a.supp.toFinite).symm.trans ha
  have hSpos : 0 < S.card := by omega
  obtain ⟨x, hxS⟩ := Finset.card_pos.mp hSpos
  have hx : x ∈ a.supp := by simpa [S] using hxS
  have hNsub : F.neighborFinset x ⊆ S.erase x := by
    intro z hz
    have hxz : F.Adj x z := (F.mem_neighborFinset x z).mp hz
    have hzSupp : z ∈ a.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      calc
        F.connectedComponentMk z = F.connectedComponentMk x :=
          (ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm
        _ = a := (ConnectedComponent.mem_supp_iff a x).mp hx
    exact Finset.mem_erase.mpr
      ⟨(F.ne_of_adj hxz).symm, by simpa [S] using hzSupp⟩
  have hNcard : (F.neighborFinset x).card = 2 := by
    rw [F.card_neighborFinset_eq_degree, hdeg]
  have hEraseCard : (S.erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hxS, hScard]
  have hNne : F.neighborFinset x ≠ S.erase x := by
    intro heq
    rw [heq, hEraseCard] at hNcard
    omega
  have hNssub : F.neighborFinset x ⊂ S.erase x :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hNsub, hNne⟩
  obtain ⟨y, hyErase, hyN⟩ := Finset.exists_of_ssubset hNssub
  have hyS : y ∈ S := (Finset.mem_erase.mp hyErase).2
  have hy : y ∈ a.supp := by simpa [S] using hyS
  have hxy : x ≠ y := (Finset.mem_erase.mp hyErase).1.symm
  have hnxy : ¬ F.Adj x y := by
    intro hxyAdj
    exact hyN ((F.mem_neighborFinset x y).mpr hxyAdj)
  have hNxSub : F.neighborFinset x ⊆ (S.erase x).erase y := by
    intro z hz
    exact Finset.mem_erase.mpr
      ⟨fun hzy => hyN (hzy ▸ hz), hNsub hz⟩
  have hDoubleEraseCard : ((S.erase x).erase y).card = 2 := by
    rw [Finset.card_erase_of_mem hyErase, hEraseCard]
  have hNxEq : F.neighborFinset x = (S.erase x).erase y := by
    apply Finset.eq_of_subset_of_card_le hNxSub
    rw [hNcard, hDoubleEraseCard]
  have hNySub : F.neighborFinset y ⊆ F.neighborFinset x := by
    intro z hz
    have hyz : F.Adj y z := (F.mem_neighborFinset y z).mp hz
    have hzSupp : z ∈ a.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      calc
        F.connectedComponentMk z = F.connectedComponentMk y :=
          (ConnectedComponent.connectedComponentMk_eq_of_adj hyz).symm
        _ = a := (ConnectedComponent.mem_supp_iff a y).mp hy
    rw [hNxEq]
    exact Finset.mem_erase.mpr
      ⟨(F.ne_of_adj hyz).symm,
        Finset.mem_erase.mpr
          ⟨fun hzx => hnxy (hzx ▸ hyz.symm), by simpa [S] using hzSupp⟩⟩
  have hNycard : (F.neighborFinset y).card = 2 := by
    rw [F.card_neighborFinset_eq_degree, hdeg]
  have hNeighbors : F.neighborFinset x = F.neighborFinset y := by
    symm
    apply Finset.eq_of_subset_of_card_le hNySub
    rw [hNycard, hNcard]
  exact ⟨x, y, hxy, hx, hy, hnxy, hNeighbors⟩

/-- Consequently, the unique order-four owner component in a five-component
order-64 cross profile supplies an opposite-twin pair in the owner factor. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_exists_ownerOppositeTwins
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hst : source ≠ target)
    (hsource : source.supp.ncard = 16)
    (htarget : target.supp.ncard = 16)
    (hfive : Fintype.card
      (componentCrossBipartiteGraph G source target).ConnectedComponent = 5) :
    ∃ x y : source.supp, x ≠ y ∧
      ¬ (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).neighborFinset x =
        (restrictedComponentOwnerGraph G source target).neighborFinset y := by
  let F := restrictedComponentOwnerGraph G source target
  obtain ⟨⟨a, ha4, _⟩, _⟩ :=
    orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerProfile
      G hfree hreg hcard source target hst hsource htarget hfive
  have hdeg : ∀ x, F.degree x = 2 :=
    binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by omega) hreg (by omega) source target
        (by omega) (by omega)
  obtain ⟨x, y, hxy, _hx, _hy, hnxy, hN⟩ :=
    twoRegular_component_order_four_exists_oppositeTwins F hdeg a ha4
  exact ⟨x, y, hxy, hnxy, hN⟩

end

end Erdos85
