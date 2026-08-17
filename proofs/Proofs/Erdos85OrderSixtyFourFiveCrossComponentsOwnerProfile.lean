import Proofs.Erdos85OrderSixtyFourCrossBipartiteFiveProfile
import Proofs.Erdos85BinarySquareSizeTwoCrossOwnerComponentSize

/-! # Owner-factor profile under five cross components at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The cross profile `8+6+6+6+6` pulls back to the exact restricted-owner
profile `4+3+3+3+3`: there is a unique order-four component and every
component has order three or four. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerProfile
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
    (∃! a : (restrictedComponentOwnerGraph G source target).ConnectedComponent,
      a.supp.ncard = 4) ∧
    ∀ a : (restrictedComponentOwnerGraph G source target).ConnectedComponent,
      a.supp.ncard = 3 ∨ a.supp.ncard = 4 := by
  classical
  let E := binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
    G hfree (q := 8) (by omega) hreg (by omega) source target (by omega)
  obtain ⟨hone, hcrossShape⟩ :=
    orderSixtyFour_twoSizeTwoParts_crossBipartite_fiveComponent_profile
      G hfree hreg hcard source target hst hsource htarget hfive
  obtain ⟨e, hefilter⟩ := Finset.card_eq_one.mp hone
  have he8 : e.supp.ncard = 8 := by
    have : e ∈ Finset.univ.filter (fun f :
        (componentCrossBipartiteGraph G source target).ConnectedComponent =>
          f.supp.ncard = 8) := by
      rw [hefilter]
      simp
    exact (Finset.mem_filter.mp this).2
  let a := E.symm e
  have hEa : E a = e := E.apply_symm_apply e
  have hdouble (b :
      (restrictedComponentOwnerGraph G source target).ConnectedComponent) :
      (E b).supp.ncard = 2 * b.supp.ncard := by
    simpa [E, binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross]
      using
        binarySquare_regular_twoSizeTwoParts_crossComponent_ncard_eq_two_mul_owner
          G hfree (q := 8) (by omega) hreg (by omega) source target
            (by omega) (by omega) b
  have ha4 : a.supp.ncard = 4 := by
    have := hdouble a
    rw [hEa, he8] at this
    omega
  have hunique : ∀ b :
      (restrictedComponentOwnerGraph G source target).ConnectedComponent,
      b.supp.ncard = 4 → b = a := by
    intro b hb4
    have hEb8 : (E b).supp.ncard = 8 := by
      rw [hdouble b, hb4]
    have hmem : E b ∈ Finset.univ.filter (fun f :
        (componentCrossBipartiteGraph G source target).ConnectedComponent =>
          f.supp.ncard = 8) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEb8⟩
    rw [hefilter] at hmem
    have hEba : E b = E a := by
      simpa [hEa] using hmem
    exact E.injective hEba
  refine ⟨⟨a, ha4, hunique⟩, ?_⟩
  intro b
  have hbdouble := hdouble b
  rcases hcrossShape (E b) with h6 | h8
  · left
    rw [h6] at hbdouble
    omega
  · right
    rw [h8] at hbdouble
    omega

end

end Erdos85
