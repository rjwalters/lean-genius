import Proofs.Erdos85MuNegFiveCanonicalOwnerCrossBridge
import Proofs.Erdos85MuNegFiveZeroThreeOwnerServiceBridge

/-!
# Clean relation terminals for h504 and h512

The owner universe and all non-degree clause families are identical to h503.
Consequently the same clean service/C4 semantics closes h504 and h512 after
substituting their exact cross-fiber profiles.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

theorem muNegFiveZeroFourOwnerRelations_false_of_serviceSemantics
    (sigma : Bool)
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveZeroThreeOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f →
      muNegFiveZeroThreeOwnerCompatible e f = true)
    (hends : ∀ e f, X e f → active e ∧ active f)
    (hfiber : ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 4 3 sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveZeroThreeOwnerValOfRelations active X) left z) = true)
    (hbalance : ∀ x y a b c d,
      muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = some a →
      muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = some b →
      muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = some c →
      muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = some d →
      (muNegFiveZeroThreeOwnerValOfRelations active X a).toNat +
          (muNegFiveZeroThreeOwnerValOfRelations active X b).toNat =
        (muNegFiveZeroThreeOwnerValOfRelations active X c).toNat +
          (muNegFiveZeroThreeOwnerValOfRelations active X d).toNat) : False := by
  apply muNegFiveZeroFourOwnerConstraintSemantics_false
  exact
    { cross_degree := muNegFiveZeroFourCrossDegreeClauses_satisfied sigma
        (muNegFiveZeroThreeOwnerValOfRelations active X) hfiber
      intertwining := muNegFiveZeroThreeIntertwiningClauses_satisfied
        (muNegFiveZeroThreeOwnerValOfRelations active X) hbalance
      hit_activity := muNegFiveZeroThreeHitActivityClauses_satisfied
        active X hsymm hends
      service := muNegFiveZeroThreeServiceClauses_satisfied
        active X hsem hsymm hirr hcompat
      exterior_c4 := muNegFiveZeroThreeC4Clauses_satisfied
        active X hsem hsymm }

theorem muNegFiveOneTwoOwnerRelations_false_of_serviceSemantics
    (sigma : Bool)
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveZeroThreeOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f →
      muNegFiveZeroThreeOwnerCompatible e f = true)
    (hends : ∀ e f, X e f → active e ∧ active f)
    (hfiber : ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 6 4 sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveZeroThreeOwnerValOfRelations active X) left z) = true)
    (hbalance : ∀ x y a b c d,
      muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = some a →
      muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = some b →
      muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = some c →
      muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = some d →
      (muNegFiveZeroThreeOwnerValOfRelations active X a).toNat +
          (muNegFiveZeroThreeOwnerValOfRelations active X b).toNat =
        (muNegFiveZeroThreeOwnerValOfRelations active X c).toNat +
          (muNegFiveZeroThreeOwnerValOfRelations active X d).toNat) : False := by
  apply muNegFiveOneTwoOwnerConstraintSemantics_false
  exact
    { cross_degree := muNegFiveOneTwoCrossDegreeClauses_satisfied sigma
        (muNegFiveZeroThreeOwnerValOfRelations active X) hfiber
      intertwining := muNegFiveZeroThreeIntertwiningClauses_satisfied
        (muNegFiveZeroThreeOwnerValOfRelations active X) hbalance
      hit_activity := muNegFiveZeroThreeHitActivityClauses_satisfied
        active X hsymm hends
      service := muNegFiveZeroThreeServiceClauses_satisfied
        active X hsem hsymm hirr hcompat
      exterior_c4 := muNegFiveZeroThreeC4Clauses_satisfied
        active X hsem hsymm }

end Erdos85

#print axioms Erdos85.muNegFiveZeroFourOwnerRelations_false_of_serviceSemantics
#print axioms Erdos85.muNegFiveOneTwoOwnerRelations_false_of_serviceSemantics
