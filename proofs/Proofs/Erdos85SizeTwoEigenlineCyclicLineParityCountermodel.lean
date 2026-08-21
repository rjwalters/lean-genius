import Proofs.Erdos85SizeTwoEigenlineCyclicRouteLineParity

/-!
# Countermodel to line parity plus sharp aggregate laws

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

The line-resolved reversal theorem forces a new per-fibre parity law in the
sharp one-duplicate/one-missing regime.  This file checks that this parity,
the displacement equation, aggregate reciprocity symmetry, and the exact
binary orientation census are still jointly satisfiable at `q=8`.

Consequently the missing packing contradiction must use base-resolved
correlations (or the shifted agreement bound) rather than only these
aggregate defect statistics.
-/

namespace Erdos85

noncomputable section

private abbrev AllowedEightOne := Fin 6

/-- The six allowed residues, in the order `0,2,3,4,5,7`. -/
private def allowedEightOneResidue (t : AllowedEightOne) : ZMod 8 :=
  ![0, 2, 3, 4, 5, 7] t

private def sharpLinePairEight
    (x : ZMod 8) (t : AllowedEightOne) :
    AllowedEightOne × AllowedEightOne :=
  if t = 0 then
    if x = 0 then ⟨1, 4⟩ else ⟨3, 5⟩
  else if t = 1 then
    if x = 0 then ⟨0, 5⟩
    else if x = 1 ∨ x = 2 then ⟨2, 1⟩
    else if x = 3 ∨ x = 4 ∨ x = 5 then
      ⟨3, 2⟩
    else ⟨4, 3⟩
  else if t = 2 then
    if x = 0 then ⟨4, 1⟩ else ⟨5, 3⟩
  else if t = 3 then
    if x = 7 then ⟨1, 4⟩ else ⟨0, 2⟩
  else if t = 4 then
    if x = 0 ∨ x = 1 then ⟨1, 2⟩
    else if x = 2 ∨ x = 3 ∨ x = 4 then
      ⟨2, 3⟩
    else if x = 5 ∨ x = 6 then ⟨3, 4⟩
    else ⟨5, 0⟩
  else
    if x = 7 then ⟨4, 1⟩ else ⟨2, 0⟩

private def sharpLineDuplicateEight
    (x : ZMod 8) (t : AllowedEightOne) : AllowedEightOne :=
  (sharpLinePairEight x t).1

private def sharpLineMissingEight
    (x : ZMod 8) (t : AllowedEightOne) : AllowedEightOne :=
  (sharpLinePairEight x t).2

private def sharpLineAggregateEight
    (duplicate missing : ZMod 8 → AllowedEightOne → AllowedEightOne)
    (t u : AllowedEightOne) : ℕ := by
  classical
  exact 8 + ((Finset.univ : Finset (ZMod 8)).filter
      fun x => duplicate x t = u).card -
    ((Finset.univ : Finset (ZMod 8)).filter
      fun x => missing x t = u).card

/-- Exact finite failure certificate for the aggregate line-parity route. -/
theorem exists_sharpProfileLineParityCountermodelEight :
    ∃ (duplicate missing : ZMod 8 → AllowedEightOne → AllowedEightOne),
      (∀ x t, duplicate x t ≠ missing x t) ∧
      (∀ x t, allowedEightOneResidue (duplicate x t) -
          allowedEightOneResidue (missing x t) =
        2 * (allowedEightOneResidue t + 1) -
          (8 * (8 - 1) / 2 + 1 : ℕ)) ∧
      (∀ t u,
        sharpLineAggregateEight duplicate missing t u =
          sharpLineAggregateEight duplicate missing u t) ∧
      (∀ t,
        ((Finset.univ : Finset (ZMod 8)).filter
            fun x => duplicate x t = t).card ≡
          ((Finset.univ : Finset (ZMod 8)).filter
            fun x => missing x t = t).card [MOD 2]) ∧
      ((Finset.univ : Finset (ZMod 8 × AllowedEightOne)).filter
        fun v => Even (allowedEightOneResidue (duplicate v.1 v.2)).val).card = 24 := by
  refine ⟨sharpLineDuplicateEight, sharpLineMissingEight, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end

end Erdos85

#print axioms Erdos85.exists_sharpProfileLineParityCountermodelEight
