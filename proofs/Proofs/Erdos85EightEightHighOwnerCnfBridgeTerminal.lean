import Proofs.Erdos85EightEightHighOwnerCrossClauseBridge
import Proofs.Erdos85EightEightHighOwnerCnfBridgeService

/-!
# Clean finite-semantics terminal for the high eight-plus-eight owner CNF

This is the final certificate-facing socket.  A graph adapter supplies the
actual active-owner predicate and owner adjacency relation, together with
the two cross-block counting identities and the clean service/C4 laws; all
DIMACS bookkeeping is discharged here.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

theorem eightEightHighOwnerRelations_false
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : EightEightHighOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f →
      eightEightHighOwnerCompatible e f = true)
    (hends : ∀ e f, X e f → active e ∧ active f)
    (htwo : ∀ left z, z < 8 →
      ((eightEightHighCrossFiberIds left z).filter fun id =>
        eightEightHighOwnerValOfRelations active X id = true).card = 2)
    (hbalance : ∀ x y a b c d,
      eightEightHighCrossIndex? ((x + 7) % 8) y = some a →
      eightEightHighCrossIndex? ((x + 1) % 8) y = some b →
      eightEightHighCrossIndex? x ((y + 1) % 8) = some c →
      eightEightHighCrossIndex? x ((y + 7) % 8) = some d →
      (eightEightHighOwnerValOfRelations active X a).toNat +
          (eightEightHighOwnerValOfRelations active X b).toNat =
        (eightEightHighOwnerValOfRelations active X c).toNat +
          (eightEightHighOwnerValOfRelations active X d).toNat) :
    False := by
  let val := eightEightHighOwnerValOfRelations active X
  have hcross : ∀ clause, clause ∈ eightEightHighCrossDegreeClauses →
      dimacsClauseSatisfied val clause :=
    eightEightHighCrossDegreeClauses_satisfied val htwo
  have hinter : ∀ clause, clause ∈ eightEightHighIntertwiningClauses →
      dimacsClauseSatisfied val clause :=
    eightEightHighIntertwiningClauses_satisfied val hbalance
  have hhit : ∀ clause, clause ∈ eightEightHighHitActivityClauses →
      dimacsClauseSatisfied val clause :=
    eightEightHighHitActivityClauses_satisfied active X hsymm hends
  exact eightEightHighOwnerConstraintSemantics_false
    (hsem.to_constraintSemantics active X hsymm hirr hcompat
      hcross hinter hhit)

end Erdos85

#print axioms Erdos85.eightEightHighOwnerRelations_false
