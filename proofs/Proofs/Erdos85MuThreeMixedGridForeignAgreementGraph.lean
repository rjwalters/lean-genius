import Proofs.Erdos85MuThreeMixedGridForeignPermutationCompatibility
import Proofs.Erdos85MuThreeMixedGridSquarePartition

/-!
# The foreign-permutation agreement graph

Two centers are joined when their local row-to-column permutations agree on
a row eligible for both.  This graph is exactly the exterior common-neighbor
graph.  Together with the separately proved degree computation for that
graph, this shows that the elementary packing bound is sharp: each local
six-point graph meets exactly thirty others once and seventeen others not at
all.
-/

open SimpleGraph

namespace Erdos85

/-- Agreement of the canonical foreign permutations on a shared eligible
row. -/
def mixedGridForeignAgreementGraph
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    SimpleGraph (muThreeMixedCell K) where
  Adj u w := u ≠ w ∧ ∃ (x : X) (hxu : ¬ H x u.1.2) (hxw : ¬ H x w.1.2),
    (code.foreignRowColumnEquiv H K C u ⟨x, hxu⟩).1 =
      (code.foreignRowColumnEquiv H K C w ⟨x, hxw⟩).1
  symm := by
    constructor
    rintro u w ⟨huw, x, hxu, hxw, h⟩
    exact ⟨huw.symm, x, hxw, hxu, h.symm⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Local permutation agreement is precisely the existence of a common
exterior neighbor. -/
theorem MuThreeMixedGridCode.foreignAgreementGraph_eq_commonNeighborGraph
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridForeignAgreementGraph H K C code =
      mixedGridCommonNeighborGraph K C := by
  ext u w
  constructor
  · rintro ⟨huw, x, hxu, hxw, hagree⟩
    let ux := code.foreignRowNeighbor H K C u ⟨x, hxu⟩
    let wx := code.foreignRowNeighbor H K C w ⟨x, hxw⟩
    have heq : ux = wx := by
      apply Subtype.ext
      apply Prod.ext
      · exact (code.foreignRowNeighbor_spec H K C u ⟨x, hxu⟩).2.trans
          (code.foreignRowNeighbor_spec H K C w ⟨x, hxw⟩).2.symm
      · rw [← code.foreignRowColumnEquiv_value H K C u ⟨x, hxu⟩,
          ← code.foreignRowColumnEquiv_value H K C w ⟨x, hxw⟩]
        exact hagree
    refine ⟨huw, ?_⟩
    have hmem : ux ∈ C.neighborFinset u ∩ C.neighborFinset w := by
      apply Finset.mem_inter.mpr
      refine ⟨(C.mem_neighborFinset u ux).mpr
        (code.foreignRowNeighbor_spec H K C u ⟨x, hxu⟩).1, ?_⟩
      rw [heq]
      exact (C.mem_neighborFinset w wx).mpr
        (code.foreignRowNeighbor_spec H K C w ⟨x, hxw⟩).1
    have hpos : 0 < (C.neighborFinset u ∩ C.neighborFinset w).card :=
      Finset.card_pos.mpr ⟨ux, hmem⟩
    have hle := code.common_neighbor_card_le_one H K C u w huw
    omega
  · rintro ⟨huw, hone⟩
    have hnonempty : (C.neighborFinset u ∩ C.neighborFinset w).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hnonempty
    have hv' := Finset.mem_inter.mp hv
    have hvu := hv'.1
    have hvw := hv'.2
    have huv : C.Adj u v := (C.mem_neighborFinset u v).mp hvu
    have hwv : C.Adj w v := (C.mem_neighborFinset w v).mp hvw
    let hxu := code.not_H_row_of_adj H K C huv
    let hxw := code.not_H_row_of_adj H K C hwv
    refine ⟨huw, v.1.1, hxu, hxw, ?_⟩
    have hu := code.foreignRowColumnEquiv_of_adj H K C huv
    have hw := code.foreignRowColumnEquiv_of_adj H K C hwv
    exact congrArg Subtype.val hu |>.trans (congrArg Subtype.val hw).symm

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignAgreementGraph_eq_commonNeighborGraph
