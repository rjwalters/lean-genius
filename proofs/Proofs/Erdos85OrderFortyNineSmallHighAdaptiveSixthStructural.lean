import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFifthStructural

/-!
# Sixth structural split of the adaptive `b1` residue

The fifth split leaves sixty-four cells.  Splitting the high-`2` partitions
of the two parent-pinned vertices `24` and `25` leaves exactly twelve ordered
selector pairs in every cell, hence 768 children total instead of 4096.
-/

namespace Erdos85

/-- The eight vertices in the fixed high-`2` support fiber. -/
def orderFortyNineThreeHighB1AdaptiveHighTwoCandidates : Fin 8 → Fin 49
  | 0 => 4
  | 1 => 5
  | 2 => 18
  | 3 => 19
  | 4 => 20
  | 5 => 21
  | 6 => 22
  | 7 => 23

def orderFortyNineThreeHighB1AdaptiveSixthCubeLeftVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (21 : Fin 46) (2 : Fin 3)

def orderFortyNineThreeHighB1AdaptiveSixthCubeRightVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (22 : Fin 46) (2 : Fin 3)

theorem orderFortyNineThreeHighB1AdaptiveSixthCube_selector_values :
    (orderFortyNineThreeHighB1AdaptiveSixthCubeLeftVariables.map (· + 1),
      orderFortyNineThreeHighB1AdaptiveSixthCubeRightVariables.map (· + 1)) =
      (#[206, 249, 717, 746, 774, 801, 827, 852],
       #[207, 250, 718, 747, 775, 802, 828, 853]) := by
  native_decide

def orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
    (li ri ai bi ci di ei : Fin 8) (i j : Fin 49) : Bool :=
  orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci i j ||
    ((i = 24 && j = orderFortyNineThreeHighB1AdaptiveHighTwoCandidates di) ||
      (j = 24 && i = orderFortyNineThreeHighB1AdaptiveHighTwoCandidates di)) ||
    ((i = 25 && j = orderFortyNineThreeHighB1AdaptiveHighTwoCandidates ei) ||
      (j = 25 && i = orderFortyNineThreeHighB1AdaptiveHighTwoCandidates ei))

private def orderFortyNineAdaptiveSixthWitnessVertices : List (Fin 49) :=
  (List.finRange 26).map fun i => ⟨i.val, by omega⟩

private def orderFortyNineAdaptiveSixthEndpointPairs :
    List (Fin 49 × Fin 49) :=
  orderFortyNineAdaptiveSixthWitnessVertices.flatMap fun i =>
    (orderFortyNineAdaptiveSixthWitnessVertices.filter fun j => i.val < j.val).map
      fun j => (i, j)

private def orderFortyNineAdaptiveSixthCommon
    (li ri ai bi ci di ei : Fin 8) (i j : Fin 49) : List (Fin 49) :=
  orderFortyNineAdaptiveSixthWitnessVertices.filter fun w =>
    orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
      li ri ai bi ci di ei i w &&
    orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
      li ri ai bi ci di ei j w

def orderFortyNineThreeHighB1AdaptiveSixthWitness
    (li ri ai bi ci di ei : Fin 8) : Option OrderFortyNineAdaptiveC4Witness :=
  match orderFortyNineAdaptiveSixthEndpointPairs.find? fun ij =>
      2 ≤ (orderFortyNineAdaptiveSixthCommon
        li ri ai bi ci di ei ij.1 ij.2).length with
  | none => none
  | some (i, j) =>
      match orderFortyNineAdaptiveSixthCommon li ri ai bi ci di ei i j with
      | w :: w' :: _ => some (i, j, w, w')
      | _ => none

/-- The one high-`2` selector excluded by the position of index `2` in a
live fifth parent.  Exactly one of `ri`, `ai`, `bi`, and `ci` is `2`. -/
def orderFortyNineThreeHighB1AdaptiveSixthForbiddenIndex
    (ri ai bi _ci : Fin 8) : Fin 8 :=
  if ri = 2 then 4 else if ai = 2 then 5 else if bi = 2 then 6 else 7

/-- The state-dependent four-element high-`2` selector set that avoids a
forced C4 at vertices `24` and `25`. -/
def orderFortyNineThreeHighB1AdaptiveSixthLiveIndex
    (ri ai bi ci i : Fin 8) : Bool :=
  (i = 3 || i = 4 || i = 5 || i = 6 || i = 7) &&
    i != orderFortyNineThreeHighB1AdaptiveSixthForbiddenIndex ri ai bi ci

def orderFortyNineThreeHighB1AdaptiveSixthResidual
    (li ri ai bi ci di ei : Fin 8) : Bool :=
  orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci &&
    orderFortyNineThreeHighB1AdaptiveSixthLiveIndex ri ai bi ci di &&
    orderFortyNineThreeHighB1AdaptiveSixthLiveIndex ri ai bi ci ei && di != ei

/-- Every fifth residual cell has exactly twelve sixth children. -/
theorem orderFortyNineThreeHighB1AdaptiveSixthResidual_card_twelve
    (li ri ai bi ci : Fin 8)
    (hfifth : orderFortyNineThreeHighB1AdaptiveFifthResidual
      li ri ai bi ci = true) :
    (((Finset.univ : Finset (Fin 8)).product Finset.univ).filter fun p =>
      orderFortyNineThreeHighB1AdaptiveSixthResidual
        li ri ai bi ci p.1 p.2).card = 12 := by
  simp only [orderFortyNineThreeHighB1AdaptiveSixthResidual, hfifth]
  native_decide +revert

theorem orderFortyNineThreeHighB1AdaptiveSixthStructurallyDead_count :
    64 * 64 - 768 = 3328 := by
  norm_num

end Erdos85
