import Proofs.Erdos85SharpSymmetricFiberProfileParityBalance
import Proofs.Erdos85SizeTwoEigenlineCyclicBaseResolvedReciprocity

/-!
# Global parity balance for cyclic sharp defects

Node: BinarySizeTwoCyclicPackingBound beneath outline A.5.3.

Base-resolved reciprocity supplies the symmetric tensor, and summing a tensor
row over the target base recovers the local target-difference multiplicity.
The generic fiber-profile double count therefore gives an exact global
orientation census for every balanced partition of the difference fibers.
-/

namespace Erdos85

noncomputable section

/-- For a balanced fiber predicate, a reciprocal cyclic code with sharp
one-duplicate/one-missing local profiles has exactly q*n source cells whose
duplicated target fiber satisfies the predicate. -/
theorem sizeTwoCyclicSharpProfile_duplicateParity_card
    {q : ℕ} [NeZero q] {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (parity : sizeTwoAllowedDifference q a → Prop)
    [DecidablePred parity]
    (duplicate missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (n : ℕ)
    (hparity :
      ((Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
        parity).card = n)
    (hnotParity :
      ((Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
        fun u => ¬parity u).card = n)
    (hne : ∀ x t, duplicate x t ≠ missing x t)
    (hopposite : ∀ x t,
      parity (duplicate x t) ↔ ¬parity (missing x t))
    (hprofile : ∀ x t u,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
        if u = duplicate x t then 2
        else if u = missing x t then 0 else 1) :
    ((Finset.univ : Finset
      (ZMod q × sizeTwoAllowedDifference q a)).filter
        fun v => parity (duplicate v.1 v.2)).card = q * n := by
  let W :
      (ZMod q × sizeTwoAllowedDifference q a) →
      (ZMod q × sizeTwoAllowedDifference q a) → ℕ :=
    fun v w => Fintype.card
      (SizeTwoCyclicBaseResolvedRoute code v.1 v.2 w.1 w.2)
  have hWsymm : ∀ v w, W v w = W w v := by
    intro v w
    exact sizeTwoCyclicBaseResolvedRoute_card_symm
      code v.1 v.2 w.1 w.2
  have hWprofile : ∀ v u,
      (∑ y : ZMod q, W v (y, u)) =
        if u = duplicate v.1 v.2 then 2
        else if u = missing v.1 v.2 then 0 else 1 := by
    intro v u
    rw [show (∑ y : ZMod q, W v (y, u)) =
        sizeTwoCyclicTargetDifferenceMultiplicity code v.1 v.2 u by
      exact sizeTwoCyclicBaseResolvedRoute_card_sum code v.1 v.2 u]
    exact hprofile v.1 v.2 u
  simpa [ZMod.card] using
    (sharpSymmetricFiberProfile_duplicateParity_card
      parity W
      (fun v => duplicate v.1 v.2)
      (fun v => missing v.1 v.2)
      hWsymm n hparity hnotParity
      (fun v => hne v.1 v.2)
      (fun v => hopposite v.1 v.2)
      hWprofile)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSharpProfile_duplicateParity_card
