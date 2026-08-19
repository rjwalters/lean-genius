import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingDesign
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReconstruction
import Proofs.Erdos85GadgetExtension

/-!
# Reconstructed full cyclic codes remain C4-free

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

The full cross-agreement law is precisely the common-neighbour condition
needed for the graph reconstructed from a reciprocal permutation code to be
`C4`-free.  This closes the abstraction loop: after retaining looplessness,
the graph-free code has not forgotten simplicity or `C4`-freeness.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A full cross-agreement code with the no-fixed-route law retained. -/
structure SizeTwoCyclicFullLooplessPermutationCode
    (q : ℕ) [NeZero q] (a : ZMod q) where
  fullCode : SizeTwoCyclicFullPermutationCode q a
  loopless : fullCode.toReciprocalCode.Loopless

/-- Every normalized exterior grid produces the full loopless code needed
for reconstruction. -/
def sizeTwoCyclicFullLooplessPermutationCode_of_grid
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    SizeTwoCyclicFullLooplessPermutationCode q a := by
  let full := sizeTwoCyclicFullPermutationCode_of_grid
    q a C hfree hrow_hit hcol_hit
  refine ⟨full, ?_⟩
  simpa [full, sizeTwoCyclicFullPermutationCode_of_grid] using
    (sizeTwoCyclicReciprocalPermutationCode_of_grid_loopless
      q a C hfree hrow_hit hcol_hit)

/-- The target cell of a route has underlying absolute grid coordinates
equal to the corresponding matching edge. -/
theorem sizeTwoCyclicMatchingEdge_eq_targetCell
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source : SizeTwoCyclicMatchingSource q a)
    (r : SizeTwoAdmissibleTargetRow q source.2.1) :
    sizeTwoCyclicMatchingEdge code source r =
      (sizeTwoCyclicCellAt q a (source.1 + r.1)
        (code.toReciprocalCode.targetDifference source.1 source.2 r)).1 := by
  apply Prod.ext
  · rfl
  · change source.1 +
      (code.toReciprocalCode.toPermutationCode.perm source.1 source.2 r).1 =
        source.1 + r.1 +
          (code.toReciprocalCode.targetDifference source.1 source.2 r).1
    rw [← code.toReciprocalCode.target_column_eq]
    simp [add_assoc]

/-- A common neighbour of two reconstructed-code vertices determines an
absolute edge lying in both corresponding source matchings. -/
def sizeTwoCyclicCodeCommonNeighborToMatchingIntersection
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullLooplessPermutationCode q a)
    [DecidableEq (sizeTwoCyclicExteriorCell q a)]
    [DecidableRel (sizeTwoCyclicCodeGraph q a
      code.fullCode.toReciprocalCode).Adj]
    (u w : sizeTwoCyclicExteriorCell q a)
    (v : {v : sizeTwoCyclicExteriorCell q a // v ∈
      (sizeTwoCyclicCodeGraph q a
        code.fullCode.toReciprocalCode).neighborFinset u ∩
      (sizeTwoCyclicCodeGraph q a
        code.fullCode.toReciprocalCode).neighborFinset w}) :
    {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicSourceMatching code.fullCode
          (sizeTwoCyclicExteriorCellEquiv q a u) ∩
        sizeTwoCyclicSourceMatching code.fullCode
          (sizeTwoCyclicExteriorCellEquiv q a w)} := by
  let C := sizeTwoCyclicCodeGraph q a
    code.fullCode.toReciprocalCode
  have hv := Finset.mem_inter.mp v.2
  have huv : C.Adj u v.1 := (C.mem_neighborFinset u v.1).mp hv.1
  have hwv : C.Adj w v.1 := (C.mem_neighborFinset w v.1).mp hv.2
  have huroute := (sizeTwoCyclicCodeGraph_adj_iff q a
    code.fullCode.toReciprocalCode code.loopless u v.1).mp huv
  have hwroute := (sizeTwoCyclicCodeGraph_adj_iff q a
    code.fullCode.toReciprocalCode code.loopless w v.1).mp hwv
  let zu := sizeTwoCyclicExteriorCellEquiv q a u
  let zw := sizeTwoCyclicExteriorCellEquiv q a w
  change ∃ r : SizeTwoAdmissibleTargetRow q zu.2.1,
    v.1 = sizeTwoCyclicCellAt q a (zu.1 + r.1)
      (code.fullCode.toReciprocalCode.targetDifference
        zu.1 zu.2 r) at huroute
  change ∃ r : SizeTwoAdmissibleTargetRow q zw.2.1,
    v.1 = sizeTwoCyclicCellAt q a (zw.1 + r.1)
      (code.fullCode.toReciprocalCode.targetDifference
        zw.1 zw.2 r) at hwroute
  let ru := Classical.choose huroute
  let rw := Classical.choose hwroute
  have hru := Classical.choose_spec huroute
  have hrw := Classical.choose_spec hwroute
  refine ⟨v.1.1, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · apply (sizeTwoCyclicSourceMatching_mem_iff
      code.fullCode zu v.1.1).mpr
    refine ⟨ru, ?_⟩
    rw [sizeTwoCyclicMatchingEdge_eq_targetCell]
    exact congrArg Subtype.val hru.symm
  · apply (sizeTwoCyclicSourceMatching_mem_iff
      code.fullCode zw v.1.1).mpr
    refine ⟨rw, ?_⟩
    rw [sizeTwoCyclicMatchingEdge_eq_targetCell]
    exact congrArg Subtype.val hrw.symm

theorem sizeTwoCyclicCodeCommonNeighborToMatchingIntersection_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullLooplessPermutationCode q a)
    [DecidableEq (sizeTwoCyclicExteriorCell q a)]
    [DecidableRel (sizeTwoCyclicCodeGraph q a
      code.fullCode.toReciprocalCode).Adj]
    (u w : sizeTwoCyclicExteriorCell q a) :
    Function.Injective
      (sizeTwoCyclicCodeCommonNeighborToMatchingIntersection code u w) := by
  intro v v' h
  apply Subtype.ext
  apply Subtype.ext
  have hp := congrArg Subtype.val h
  change v.1.1 = v'.1.1 at hp
  exact hp

/-- The graph reconstructed from a full loopless cyclic code is `C4`-free. -/
theorem sizeTwoCyclicCodeGraph_not_containsC4
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullLooplessPermutationCode q a) :
    ¬ containsC4 (sizeTwoCyclicExteriorCell q a)
      (sizeTwoCyclicCodeGraph q a
        code.fullCode.toReciprocalCode) := by
  classical
  let C := sizeTwoCyclicCodeGraph q a
    code.fullCode.toReciprocalCode
  letI : DecidableEq (sizeTwoCyclicExteriorCell q a) := Classical.decEq _
  letI : DecidableRel C.Adj := Classical.decRel _
  apply not_containsC4_of_forall_common_le_one
  intro u w huw
  calc
    (C.neighborFinset u ∩ C.neighborFinset w).card =
        Fintype.card {v : sizeTwoCyclicExteriorCell q a //
          v ∈ C.neighborFinset u ∩ C.neighborFinset w} := by
      exact (Fintype.card_coe _).symm
    _ ≤ Fintype.card {e : SizeTwoCyclicAbsoluteGridEdge q //
        e ∈ sizeTwoCyclicSourceMatching code.fullCode
            (sizeTwoCyclicExteriorCellEquiv q a u) ∩
          sizeTwoCyclicSourceMatching code.fullCode
            (sizeTwoCyclicExteriorCellEquiv q a w)} :=
      Fintype.card_le_of_injective
        (sizeTwoCyclicCodeCommonNeighborToMatchingIntersection code u w)
        (sizeTwoCyclicCodeCommonNeighborToMatchingIntersection_injective
          code u w)
    _ = (sizeTwoCyclicSourceMatching code.fullCode
          (sizeTwoCyclicExteriorCellEquiv q a u) ∩
        sizeTwoCyclicSourceMatching code.fullCode
          (sizeTwoCyclicExteriorCellEquiv q a w)).card := Fintype.card_coe _
    _ ≤ 1 := sizeTwoCyclicSourceMatching_inter_card_le_one
      code.fullCode
      (sizeTwoCyclicExteriorCellEquiv q a u)
      (sizeTwoCyclicExteriorCellEquiv q a w)
      (fun h => huw ((sizeTwoCyclicExteriorCellEquiv q a).injective h))

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicCodeGraph_not_containsC4
#print axioms Erdos85.sizeTwoCyclicFullLooplessPermutationCode_of_grid
