import Proofs.Erdos85SizeTwoEigenlineCyclicThreeFiberSubsystem

/-!
# Agreement budget in the q=8 three-fiber core

The same-difference hypothesis bounds every ordered pair of distinct
translated bases by one common route.  Summing it gives 56 events per fiber
at q=8 and 168 across the exact `{0,2,4}` core.  These bounds use no agreement
hypothesis on the other three fibers.
-/

namespace Erdos85

noncomputable section

/-- Total ordered shifted-agreement mass in one difference fiber. -/
def sizeTwoCyclicRoutingDataAgreementMass
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a) : ℕ :=
  ∑ x : ZMod q, ∑ d ∈ (Finset.univ.erase (0 : ZMod q)),
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a data.perm x d t t)

/-- A fiber satisfying the reduced same-difference law has aggregate ordered
agreement mass at most `q(q-1)`. -/
theorem sizeTwoCyclicRoutingDataAgreementMass_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a)
    (hagreement : data.AgreementAt t) :
    sizeTwoCyclicRoutingDataAgreementMass data t ≤ q * (q - 1) := by
  classical
  unfold sizeTwoCyclicRoutingDataAgreementMass
  calc
    (∑ x : ZMod q, ∑ d ∈ (Finset.univ.erase (0 : ZMod q)),
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a data.perm x d t t)) ≤
        ∑ _x : ZMod q, ∑ _d ∈ (Finset.univ.erase (0 : ZMod q)), 1 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro d hd
      exact hagreement x d (Finset.mem_erase.mp hd).1
    _ = q * (q - 1) := by
      simp [ZMod.card]

/-- The three constrained q=8 fibers have total agreement budget at most
`3 * 56 = 168`. -/
theorem sizeTwoCyclicEightThreeFiber_agreementMass_le_168
    (code : SizeTwoCyclicThreeFiberCode 8 (1 : ZMod 8)
      sizeTwoCyclicEightFiberZero sizeTwoCyclicEightFiberTwo
        sizeTwoCyclicEightFiberFour) :
    sizeTwoCyclicRoutingDataAgreementMass code.data
          sizeTwoCyclicEightFiberZero +
        sizeTwoCyclicRoutingDataAgreementMass code.data
          sizeTwoCyclicEightFiberTwo +
        sizeTwoCyclicRoutingDataAgreementMass code.data
          sizeTwoCyclicEightFiberFour ≤ 168 := by
  have h0 := sizeTwoCyclicRoutingDataAgreementMass_le code.data
    sizeTwoCyclicEightFiberZero code.agreement_t
  have h2 := sizeTwoCyclicRoutingDataAgreementMass_le code.data
    sizeTwoCyclicEightFiberTwo code.agreement_u
  have h4 := sizeTwoCyclicRoutingDataAgreementMass_le code.data
    sizeTwoCyclicEightFiberFour code.agreement_v
  norm_num at h0 h2 h4
  omega

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRoutingDataAgreementMass_le
#print axioms Erdos85.sizeTwoCyclicEightThreeFiber_agreementMass_le_168
