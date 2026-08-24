import Proofs.Erdos85OwnerSourceTransportCells
import Proofs.Erdos85OwnerComplementSpecialContribution

/-!
# A direct cross-star through is diagonal, not a special owner correction

An active cross-star through is inserted once with each Boolean owner label.
Its source, relay, and corrected contributions are therefore identical in the
two coordinates.  Such a diagonal vector cannot equal the complementary
one-hot special contribution forced by odd ordinary owner mass.
-/

namespace Erdos85

noncomputable section

/-- The two owner-labelled copies of one active cross-star through. -/
def activeCrossStarThroughPairLedger
    (sourceCell kRelay muRelay : ZMod 2)
    (hsource : sourceCell = 1)
    (hrelay : kRelay = 1 + muRelay) :
    OwnerSourceTransportLedger Bool :=
  ownerSourceTransportLedgerOfCells Finset.univ fun owner =>
    activeCrossStarThroughTransportCell owner sourceCell kRelay muRelay
      hsource hrelay

/-- A through contributes the same source unit to both owners. -/
theorem activeCrossStarThroughPairLedger_ownerSourceMass
    (sourceCell kRelay muRelay : ZMod 2)
    (hsource : sourceCell = 1)
    (hrelay : kRelay = 1 + muRelay) (i : Bool) :
    (activeCrossStarThroughPairLedger sourceCell kRelay muRelay
      hsource hrelay).ownerSourceMass i = 1 := by
  cases i <;> simp [activeCrossStarThroughPairLedger,
    OwnerSourceTransportLedger.ownerSourceMass,
    OwnerSourceTransportLedger.ownerCells,
    ownerSourceTransportLedgerOfCells,
    activeCrossStarThroughTransportCell, hsource] <;>
    change (1 : ZMod 2) = 1 <;> rfl

/-- Its relay contribution is likewise diagonal. -/
theorem activeCrossStarThroughPairLedger_ownerRelayMass
    (sourceCell kRelay muRelay : ZMod 2)
    (hsource : sourceCell = 1)
    (hrelay : kRelay = 1 + muRelay) (i : Bool) :
    (activeCrossStarThroughPairLedger sourceCell kRelay muRelay
      hsource hrelay).ownerRelayMass i = kRelay := by
  cases i <;> simp [activeCrossStarThroughPairLedger,
    OwnerSourceTransportLedger.ownerRelayMass,
    OwnerSourceTransportLedger.ownerCells,
    ownerSourceTransportLedgerOfCells,
    activeCrossStarThroughTransportCell] <;>
    change (1 : ZMod 2) * kRelay = kRelay <;> simp

/-- Its corrected owner vector is the constant diagonal vector `muRelay`. -/
theorem activeCrossStarThroughPairLedger_psiHatOwner
    (sourceCell kRelay muRelay : ZMod 2)
    (hsource : sourceCell = 1)
    (hrelay : kRelay = 1 + muRelay) :
    (activeCrossStarThroughPairLedger sourceCell kRelay muRelay
      hsource hrelay).psiHatOwner = fun _ : Bool => muRelay := by
  funext i
  cases i <;> simp [activeCrossStarThroughPairLedger,
    OwnerSourceTransportLedger.psiHatOwner,
    OwnerSourceTransportLedger.ownerCorrectedMass,
    OwnerSourceTransportLedger.ownerCells,
    ownerSourceTransportLedgerOfCells,
    activeCrossStarThroughTransportCell] <;>
    change (1 : ZMod 2) * muRelay = muRelay <;> simp

/-- No constant diagonal owner vector is a complementary one-hot unit. -/
theorem constantOwnerVector_ne_complementOwnerUnit
    (charged : Bool) (t : ZMod 2) :
    (fun _ : Bool => t) ≠ boolOwnerUnit (!charged) := by
  intro h
  have hc := congrFun h charged
  have hnc := congrFun h (!charged)
  cases charged <;> simp [boolOwnerUnit] at hc hnc
  · exact zero_ne_one (hc.symm.trans hnc)
  · exact zero_ne_one (hc.symm.trans hnc)

/-- **Direct-through no-go (`73rnz_cjibkzr`).**  The corrected contribution
of a direct cross-star through cannot be the unique complementary special
correction required by an odd ordinary owner vector. -/
theorem activeCrossStarThroughPairLedger_ne_complementSpecial
    (charged : Bool)
    (sourceCell kRelay muRelay : ZMod 2)
    (hsource : sourceCell = 1)
    (hrelay : kRelay = 1 + muRelay) :
    (activeCrossStarThroughPairLedger sourceCell kRelay muRelay
      hsource hrelay).psiHatOwner ≠ boolOwnerUnit (!charged) := by
  rw [activeCrossStarThroughPairLedger_psiHatOwner]
  exact constantOwnerVector_ne_complementOwnerUnit charged muRelay

end


end Erdos85

#print axioms Erdos85.activeCrossStarThroughPairLedger_ownerSourceMass
#print axioms Erdos85.activeCrossStarThroughPairLedger_psiHatOwner
#print axioms Erdos85.activeCrossStarThroughPairLedger_ne_complementSpecial
