import Proofs.Erdos85OrderSixtyFourFiveCrossComponentsOwnerProfile

/-! # Exact triangle-component count in a five-component owner factor -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the five-cross-component hypothesis, exactly four restricted-owner
components have order three. Since the factor is two-regular, these are its
four triangle components. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerTriangleComponent_count
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
    (Finset.univ.filter fun a :
      (restrictedComponentOwnerGraph G source target).ConnectedComponent =>
        a.supp.ncard = 3).card = 4 := by
  classical
  obtain ⟨⟨a, ha4, hunique⟩, hshape⟩ :=
    orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerProfile
      G hfree hreg hcard source target hst hsource htarget hfive
  have hfourFilter :
      Finset.univ.filter (fun b :
        (restrictedComponentOwnerGraph G source target).ConnectedComponent =>
          b.supp.ncard = 4) = {a} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · exact hunique b
    · rintro rfl
      exact ha4
  have hnotThreeFilter :
      Finset.univ.filter (fun b :
        (restrictedComponentOwnerGraph G source target).ConnectedComponent =>
          ¬ b.supp.ncard = 3) =
      Finset.univ.filter (fun b :
        (restrictedComponentOwnerGraph G source target).ConnectedComponent =>
          b.supp.ncard = 4) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hb3
      exact (hshape b).resolve_left hb3
    · intro hb4 hb3
      omega
  have hownerCard : Fintype.card
      (restrictedComponentOwnerGraph G source target).ConnectedComponent = 5 := by
    rw [← hfive]
    exact Fintype.card_congr
      (binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
        G hfree (q := 8) (by omega) hreg (by omega) source target (by omega))
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset
      (restrictedComponentOwnerGraph G source target).ConnectedComponent))
    (p := fun b => b.supp.ncard = 3)
  rw [hnotThreeFilter, hfourFilter] at hpartition
  simp only [Finset.card_singleton, Finset.card_univ, hownerCard] at hpartition
  omega

end

end Erdos85
