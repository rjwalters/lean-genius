import Proofs.Erdos85SizeTwoEigenlineCyclicDefectCirculation

/-!
# Countermodel to the sharp-flow cocycle as a packing contradiction

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The reciprocity argument produces a symmetric discrete derivative for the
missing-defect counts.  That count-level system is not itself contradictory:
at `q = 8` the explicit flow below has the correct row mass, respects both
deleted fibers and their translates, and satisfies the full cocycle.  Thus a
proof of the packing bound must retain information beyond aggregate sharp
defect counts (for example, correlations between the base points realizing
different target fibers).
-/

namespace Erdos85

noncomputable section

private abbrev AllowedEight := sizeTwoAllowedDifference 8 (0 : ZMod 8)

/-- The displacement forced by the first moment when `q = 8`. -/
private def sharpFlowDeltaEight (t : AllowedEight) : ZMod 8 :=
  2 * (t.1 + 1) - (8 * (8 - 1) / 2 + 1 : ℕ)

/-- An explicit count flow.  Each source row has two entries of mass four.
The twelve supported ordered pairs form the obstruction to extracting a
contradiction from the symmetric derivative alone. -/
private def sharpFlowCountermodelEight (t : AllowedEight) (u : ZMod 8) : ℕ :=
  if (t.1 = 1 ∧ u = 2) ∨ (t.1 = 1 ∧ u = 4) ∨
      (t.1 = 2 ∧ u = 1) ∨ (t.1 = 2 ∧ u = 3) ∨
      (t.1 = 3 ∧ u = 2) ∨ (t.1 = 3 ∧ u = 6) ∨
      (t.1 = 4 ∧ u = 1) ∨ (t.1 = 4 ∧ u = 5) ∨
      (t.1 = 5 ∧ u = 4) ∨ (t.1 = 5 ∧ u = 6) ∨
      (t.1 = 6 ∧ u = 3) ∨ (t.1 = 6 ∧ u = 5) then 4 else 0

/-- The sharp-flow consequences currently available from mass, deleted-fiber
support, displacement, and reciprocity are jointly satisfiable at `q = 8`.

The first conjunct is row mass.  The second says every positive missing count
starts and ends in the allowed set.  The third is exactly the symmetric
discrete-derivative cocycle, with the flow extended by zero across the two
deleted residues. -/
theorem exists_sharpFlowCountermodelEight :
    ∃ (f : AllowedEight → ZMod 8 → ℕ) (delta : AllowedEight → ZMod 8),
      (∀ t, delta t =
        2 * (t.1 + 1) - (8 * (8 - 1) / 2 + 1 : ℕ)) ∧
      (∀ t, (∑ u : AllowedEight, f t u.1) = 8) ∧
      (∀ t z, f t z ≠ 0 →
        z ≠ (0 : ZMod 8) ∧ z ≠ (-1 : ZMod 8) ∧
        z + delta t ≠ (0 : ZMod 8) ∧
          z + delta t ≠ (-1 : ZMod 8)) ∧
      (∀ t u,
        f t (u.1 - delta t) + f u t.1 =
          f u (t.1 - delta u) + f t u.1) := by
  refine ⟨sharpFlowCountermodelEight, sharpFlowDeltaEight, ?_, ?_, ?_, ?_⟩
  · intro t
    rfl
  · decide
  · decide
  · decide

end

end Erdos85

#print axioms Erdos85.exists_sharpFlowCountermodelEight
