import Proofs.Erdos85SizeTwoEigenlineCyclicDoubleShiftFixedPoints
import Mathlib.GroupTheory.Perm.Fin

/-!
# Cycle-type countermodel to the double-shift sign endpoint

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

At the first binary parameter `q=8`, the completed comparison acts on six
rows.  The currently proved information—canonical sign and at most five
fixed points—does not restrict that sign: a 5-cycle has sign `+1` and one
fixed point, while a 6-cycle has sign `-1` and no fixed points.  Thus a
successful packing contradiction must control more of the comparison cycle
type than its sign and fixed-point count.
-/

namespace Erdos85

noncomputable section

private def doubleShiftEvenCycleType : Equiv.Perm (Fin 6) :=
  Fin.cycleRange ⟨4, by decide⟩

private def doubleShiftOddCycleType : Equiv.Perm (Fin 6) :=
  Fin.cycleRange (Fin.last 5)

/-- Both possible signs satisfy the six-point fixed-point bound. -/
theorem exists_doubleShiftCycleTypeSignCountermodelSix :
    ∃ even odd : Equiv.Perm (Fin 6),
      Equiv.Perm.sign even = 1 ∧
      Fintype.card (Function.fixedPoints even) ≤ 5 ∧
      Equiv.Perm.sign odd = -1 ∧
      Fintype.card (Function.fixedPoints odd) ≤ 5 := by
  refine ⟨doubleShiftEvenCycleType, doubleShiftOddCycleType, ?_, ?_, ?_, ?_⟩
  · norm_num [doubleShiftEvenCycleType, Fin.sign_cycleRange]
  · decide
  · norm_num [doubleShiftOddCycleType, Fin.sign_cycleRange]
  · decide

end

end Erdos85

#print axioms Erdos85.exists_doubleShiftCycleTypeSignCountermodelSix
