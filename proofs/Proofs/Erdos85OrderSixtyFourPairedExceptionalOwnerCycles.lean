import Proofs.Erdos85OrderSixtyFourFiveCrossComponentsOwnerProfile
import Proofs.Erdos85BinarySquareSizeTwoPairedOwnerComponentEquiv

/-! # Canonically paired exceptional owner cycles at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the five-cross-component profile, the unique order-four owner
components on the two sides form a unique pair, and the canonical paired
component equivalence maps the source member exactly to the target member. -/
theorem orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_existsUnique_pairedOwnerFourCycles
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
    ∃! p :
      (restrictedComponentOwnerGraph G source target).ConnectedComponent ×
        (restrictedComponentOwnerGraph G target source).ConnectedComponent,
      p.1.supp.ncard = 4 ∧ p.2.supp.ncard = 4 ∧
        binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv
          G hfree (q := 8) (by omega) hreg (by omega) source target
            (by omega) (by omega) p.1 = p.2 := by
  let P := binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv
    G hfree (q := 8) (by omega) hreg (by omega) source target
      (by omega) (by omega)
  obtain ⟨⟨a, ha4, haUnique⟩, _⟩ :=
    orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerProfile
      G hfree hreg hcard source target hst hsource htarget hfive
  let b := P a
  have hb4 : b.supp.ncard = 4 := by
    rw [binarySquare_regular_twoSizeTwoParts_pairedOwnerComponentEquiv_supp_ncard
      G hfree (q := 8) (by omega) hreg (by omega) source target
        (by omega) (by omega) a]
    exact ha4
  refine ⟨(a, b), ⟨ha4, hb4, rfl⟩, ?_⟩
  rintro ⟨a', b'⟩ ⟨ha'4, _hb'4, hab'⟩
  have haa : a' = a := haUnique a' ha'4
  subst a'
  have hbb : b' = b := by
    simpa [b, P] using hab'.symm
  subst b'
  rfl

end

end Erdos85
