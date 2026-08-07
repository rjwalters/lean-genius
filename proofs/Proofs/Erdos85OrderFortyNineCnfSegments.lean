import Proofs.Erdos85OrderFortyNinePartitionClauses

/-!
# Segmented semantics for the full order-49 CNF

The certified CNFs contain more than a million C4 clauses.  Keeping their
five production groups segmented avoids materializing one enormous kernel
`Array (List Int)` while retaining the exact semantics and ordering needed by
a streaming DIMACS/LRAT checker.
-/

namespace Erdos85

structure OrderFortyNineCnfSegmentsSatisfied
    (masks : Array Nat) (val : DimacsValuation) : Prop where
  fixed : dimacsFormulaSatisfied val (orderFortyNineFixedClauses masks)
  c4 : dimacsFormulaSatisfied val orderFortyNineC4Clauses
  degree : dimacsFormulaSatisfied val (orderFortyNineDegreeBlocks 9).clauses
  partition : dimacsFormulaSatisfied val (orderFortyNinePartitionClauses masks)

theorem orderFortyNineCnfSegments_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks) :
    ∃ val : DimacsValuation,
      OrderFortyNineCnfSegmentsSatisfied masks val ∧
      ∀ id, id ≤ 1176 → val id = orderFortyNineDimacsEdgeVal edges id := by
  obtain ⟨val, hdegreeSat, hdegreeBounded, htop, hagree⟩ :=
    orderFortyNineDegreeBlocks_invariant hc
  refine ⟨val, ?_, hagree⟩
  constructor
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineFixedClauses_satisfied_of_zero_masks hc hzero)
      (orderFortyNineFixedClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineC4Clauses_satisfied hc)
      orderFortyNineC4Clauses_bounded
      (fun id hid => (hagree id hid).symm)
  · exact hdegreeSat
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNinePartitionClauses_satisfied hc hzero)
      (orderFortyNinePartitionClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)

end Erdos85
