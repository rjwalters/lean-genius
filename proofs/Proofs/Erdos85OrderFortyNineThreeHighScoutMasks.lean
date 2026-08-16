import Proofs.Erdos85OrderFortyNineFiveHighCanonicalMasks

/-!
# Recovered masks for the two surviving three-high scout geometries

These are decoded from the fixed high-edge units after recovering each
historical lazy `IDPool` allocation from its universal C4 block.  The first
array is the unique-common-neighbor (`dist2`) representative; the second is
the surviving distinct-common-neighbor, non-partner, sibling-coincidence
(`dist1_c2`) representative.
-/

namespace Erdos85

def orderFortyNineThreeHighDistTwoMasks : Array Nat :=
  #[0, 0, 0, 7,
    1, 1, 1, 1, 1, 1, 1,
    2, 4, 0,
    2, 2, 2, 2, 2, 2,
    4, 4, 4, 4, 4, 4,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def orderFortyNineThreeHighDistOneC2Masks : Array Nat :=
  #[0, 0, 0, 3, 1, 5,
    1, 1, 1, 1, 1, 0,
    2, 2, 2, 2, 2, 2,
    4, 4, 4, 4, 4, 4,
    0, 6,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem orderFortyNineThreeHighDistTwoMasks_size :
    orderFortyNineThreeHighDistTwoMasks.size = 49 := by decide

theorem orderFortyNineThreeHighDistOneC2Masks_size :
    orderFortyNineThreeHighDistOneC2Masks.size = 49 := by decide

theorem orderFortyNineThreeHighDistTwoMasks_high_zero :
    OrderFortyNineVariableHighMasksZero (3 : Fin 50)
      orderFortyNineThreeHighDistTwoMasks := by
  intro a w
  fin_cases a <;> fin_cases w <;> decide

theorem orderFortyNineThreeHighDistOneC2Masks_high_zero :
    OrderFortyNineVariableHighMasksZero (3 : Fin 50)
      orderFortyNineThreeHighDistOneC2Masks := by
  intro a w
  fin_cases a <;> fin_cases w <;> decide

theorem orderFortyNineThreeHighDistTwoMasks_partitionExcluded :
    OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50)
      orderFortyNineThreeHighDistTwoMasks :=
  orderFortyNineVariableHighPartitionExcluded_of_high_zero
    orderFortyNineThreeHighDistTwoMasks_high_zero

theorem orderFortyNineThreeHighDistOneC2Masks_partitionExcluded :
    OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50)
      orderFortyNineThreeHighDistOneC2Masks :=
  orderFortyNineVariableHighPartitionExcluded_of_high_zero
    orderFortyNineThreeHighDistOneC2Masks_high_zero

end Erdos85
