import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFourthGraphConsumer

/-!
# Fifth structural split of the adaptive `b1` residue

The fourth split leaves eighty cells.  Vertex `23` is the last vertex of its
fixed high-`2` block whose unique neighbor in the high-`1` fiber is not yet
selected.  Adding that exact eight-way partition eliminates 576 of 640
children by a forced C4.  Sixteen fourth parents have no live child, while
each of the other sixty-four has exactly one.
-/

namespace Erdos85

/-- Fifth partition selector: low vertex `23`, high vertex `1`. -/
def orderFortyNineThreeHighB1AdaptiveFifthCubeVariables : Array Nat :=
  orderFortyNineSmallHighPartitionCubeVariables
    (3 : Fin 50) orderFortyNineThreeHighDistOneNoCoincidenceMasks
      (20 : Fin 46) (1 : Fin 3)

theorem orderFortyNineThreeHighB1AdaptiveFifthCube_selector_values :
    orderFortyNineThreeHighB1AdaptiveFifthCubeVariables.map (· + 1) =
      #[161, 248, 521, 556, 590, 623, 655, 686] := by
  native_decide

theorem orderFortyNineThreeHighB1AdaptiveFifthCube_selector_size :
    orderFortyNineThreeHighB1AdaptiveFifthCubeVariables.size = 8 := by
  native_decide

/-- Forced edges in a fourth residual cell and one positive fifth child. -/
def orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge
    (li ri ai bi ci : Fin 8) (i j : Fin 49) : Bool :=
  orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi i j ||
    ((i = 23 && j = orderFortyNineThreeHighB1AdaptiveCandidates ci) ||
      (j = 23 && i = orderFortyNineThreeHighB1AdaptiveCandidates ci))

private def orderFortyNineAdaptiveFifthWitnessVertices : List (Fin 49) :=
  (List.finRange 26).map fun i => ⟨i.val, by omega⟩

private def orderFortyNineAdaptiveFifthEndpointPairs :
    List (Fin 49 × Fin 49) :=
  orderFortyNineAdaptiveFifthWitnessVertices.flatMap fun i =>
    (orderFortyNineAdaptiveFifthWitnessVertices.filter fun j => i.val < j.val).map
      fun j => (i, j)

private def orderFortyNineAdaptiveFifthCommon
    (li ri ai bi ci : Fin 8) (i j : Fin 49) : List (Fin 49) :=
  orderFortyNineAdaptiveFifthWitnessVertices.filter fun w =>
    orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci i w &&
      orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci j w

/-- Computed C4 witness for a structurally dead fifth child. -/
def orderFortyNineThreeHighB1AdaptiveFifthWitness
    (li ri ai bi ci : Fin 8) : Option OrderFortyNineAdaptiveC4Witness :=
  match orderFortyNineAdaptiveFifthEndpointPairs.find? fun ij =>
      2 ≤ (orderFortyNineAdaptiveFifthCommon li ri ai bi ci ij.1 ij.2).length with
  | none => none
  | some (i, j) =>
      match orderFortyNineAdaptiveFifthCommon li ri ai bi ci i j with
      | w :: w' :: _ => some (i, j, w, w')
      | _ => none

/-- Exactly the fifth children with no forced C4 witness. -/
def orderFortyNineThreeHighB1AdaptiveFifthResidual
    (li ri ai bi ci : Fin 8) : Bool :=
  orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi &&
    (orderFortyNineThreeHighB1AdaptiveFifthWitness li ri ai bi ci).isNone

/-- A fourth residual parent has either no live fifth child or exactly one. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthResidual_card_zero_or_one
    (li ri ai bi : Fin 8)
    (hfourth : orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi = true) :
    ((Finset.univ : Finset (Fin 8)).filter fun ci =>
      orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci).card = 0 ∨
    ((Finset.univ : Finset (Fin 8)).filter fun ci =>
      orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci).card = 1 := by
  native_decide +revert

/-- Exactly sixty-four fifth children survive the forced-C4 search. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthResidual_count :
    (((((Finset.univ : Finset (Fin 8)).product Finset.univ).product
      ((Finset.univ : Finset (Fin 8)).product Finset.univ)).product
        Finset.univ).filter fun p =>
          orderFortyNineThreeHighB1AdaptiveFifthResidual
            p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2).card = 64 := by
  native_decide

/-- Of the eighty fourth parents, sixteen have no live fifth child. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthDeadParent_count :
    (((Finset.univ : Finset (Fin 8)).product Finset.univ).product
      ((Finset.univ : Finset (Fin 8)).product Finset.univ) |>.filter fun p =>
        orderFortyNineThreeHighB1AdaptiveFourthResidual
          p.1.1 p.1.2 p.2.1 p.2.2 &&
        decide (((Finset.univ : Finset (Fin 8)).filter fun ci =>
          orderFortyNineThreeHighB1AdaptiveFifthResidual
            p.1.1 p.1.2 p.2.1 p.2.2 ci).card = 0)).card = 16 := by
  native_decide

/-- The fifth split structurally rejects 576 of its 640 positive children. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthStructurallyDead_count :
    80 * 8 - 64 = 576 := by
  norm_num

end Erdos85
