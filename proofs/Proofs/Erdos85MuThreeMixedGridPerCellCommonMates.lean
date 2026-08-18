import Proofs.Erdos85MuThreeMixedGridPerCellRowLedger
import Proofs.Erdos85MuThreeMixedGridRoutePermutation

/-!
# Common-neighbour mates in one target row

Eligible intermediate neighbours of `u` are indexed by the columns allowed
for both the source and target rows.  Routing those intermediates into the
target row is then a bijection onto the common-neighbour (`Q`) mates there.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def mixedGridEligibleIntermediateNeighbors
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (u : muThreeMixedCell K) (x : X) : Finset (muThreeMixedCell K) :=
  (C.neighborFinset u).filter fun m => ¬ H x m.1.2

/-- Eligible intermediate neighbours are counted by the columns allowed for
both the source row and target row. -/
theorem MuThreeMixedGridCode.eligibleIntermediateNeighbors_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) :
    (mixedGridEligibleIntermediateNeighbors H K C u x).card =
      (mixedGridCommonAllowedColumns H u.1.1 x).card := by
  apply Finset.card_bij (fun m _ => m.1.2)
  · intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hum : C.Adj u m := (C.mem_neighborFinset u m).mp hm'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      mixedGrid_neighbor_column_allowed H K C code u m hum, hm'.2⟩
  · intro m hm n hn hcol
    by_contra hmn
    have hm' := Finset.mem_filter.mp hm
    have hn' := Finset.mem_filter.mp hn
    have hsep := code.rook u m n
      ((C.mem_neighborFinset u m).mp hm'.1)
      ((C.mem_neighborFinset u n).mp hn'.1) hmn
    exact hsep.2 hcol
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    obtain ⟨m, hum, _⟩ :=
      (code.existsUnique_column_neighbor_iff H K C u y).mpr hy'.1
    refine ⟨m, ?_, hum.2⟩
    apply Finset.mem_filter.mpr
    exact ⟨(C.mem_neighborFinset u m).mpr hum.1, by simpa [hum.2] using hy'.2⟩

/-- Send an eligible intermediate neighbour to its unique neighbour in the
target row. -/
noncomputable def mixedGridIntermediateToRowMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X)
    (m : {m // m ∈ mixedGridEligibleIntermediateNeighbors H K C u x}) :
    muThreeMixedCell K :=
  mixedGridRowRoute H K C code m.1 x (Finset.mem_filter.mp m.2).2

theorem mixedGridIntermediateToRowMate_spec
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X)
    (m : {m // m ∈ mixedGridEligibleIntermediateNeighbors H K C u x}) :
    C.Adj m.1 (mixedGridIntermediateToRowMate H K C code u x m) ∧
      (mixedGridIntermediateToRowMate H K C code u x m).1.1 = x := by
  exact mixedGridRowRoute_spec H K C code m.1 x (Finset.mem_filter.mp m.2).2

/-- Routing eligible intermediates gives a bijection onto the `Q`-mates of
`u` in the target row. -/
theorem MuThreeMixedGridCode.commonNeighborMatesInRow_card_eq_eligible
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow (mixedGridCommonNeighborGraph K C) u x).card =
      (mixedGridEligibleIntermediateNeighbors H K C u x).card := by
  symm
  apply Finset.card_bij (fun m hm =>
    mixedGridIntermediateToRowMate H K C code u x ⟨m, hm⟩)
  · intro m hm
    let ms : {m // m ∈ mixedGridEligibleIntermediateNeighbors H K C u x} :=
      ⟨m, hm⟩
    let v := mixedGridIntermediateToRowMate H K C code u x ms
    have hum : C.Adj u m := (C.mem_neighborFinset u m).mp
      (Finset.mem_filter.mp hm).1
    have hmv : C.Adj m v := (mixedGridIntermediateToRowMate_spec
      H K C code u x ms).1
    have hvrow : v.1.1 = x := (mixedGridIntermediateToRowMate_spec
      H K C code u x ms).2
    have huv : u ≠ v := by
      intro huv
      apply hxu
      simpa [huv] using hvrow.symm
    have hmcommon : m ∈ C.neighborFinset u ∩ C.neighborFinset v := by
      exact Finset.mem_inter.mpr
        ⟨(C.mem_neighborFinset u m).mpr hum,
          (C.mem_neighborFinset v m).mpr (C.adj_symm hmv)⟩
    have hpos : 0 < (C.neighborFinset u ∩ C.neighborFinset v).card :=
      Finset.card_pos.mpr ⟨m, hmcommon⟩
    have hle := code.common_neighbor_card_le_one H K C u v huv
    have hone : (C.neighborFinset u ∩ C.neighborFinset v).card = 1 := by omega
    apply Finset.mem_filter.mpr
    exact ⟨((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mpr
      ⟨huv, hone⟩, hvrow⟩
  · intro m hm n hn hmn
    let ms : {m // m ∈ mixedGridEligibleIntermediateNeighbors H K C u x} :=
      ⟨m, hm⟩
    let ns : {m // m ∈ mixedGridEligibleIntermediateNeighbors H K C u x} :=
      ⟨n, hn⟩
    let v := mixedGridIntermediateToRowMate H K C code u x ms
    have hvrow : v.1.1 = x :=
      (mixedGridIntermediateToRowMate_spec H K C code u x ms).2
    have huv : u ≠ v := by
      intro huv
      apply hxu
      simpa [huv] using hvrow.symm
    have hmcommon : m ∈ C.neighborFinset u ∩ C.neighborFinset v := by
      apply Finset.mem_inter.mpr
      refine ⟨(Finset.mem_filter.mp hm).1, ?_⟩
      exact (C.mem_neighborFinset v m).mpr (C.adj_symm
        (mixedGridIntermediateToRowMate_spec H K C code u x ms).1)
    have hncommon : n ∈ C.neighborFinset u ∩ C.neighborFinset v := by
      apply Finset.mem_inter.mpr
      refine ⟨(Finset.mem_filter.mp hn).1, ?_⟩
      have hnv := (mixedGridIntermediateToRowMate_spec H K C code u x ns).1
      have heq : mixedGridIntermediateToRowMate H K C code u x ns = v := hmn.symm
      rw [heq] at hnv
      exact (C.mem_neighborFinset v n).mpr (C.adj_symm hnv)
    exact Finset.card_le_one.mp
      (code.common_neighbor_card_le_one H K C u v huv) m hmcommon n hncommon
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    have hq := ((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mp hv'.1
    change u ≠ v ∧ (C.neighborFinset u ∩ C.neighborFinset v).card = 1 at hq
    have hnonempty : (C.neighborFinset u ∩ C.neighborFinset v).Nonempty :=
      Finset.card_pos.mp (by rw [hq.2]; omega)
    obtain ⟨m, hm⟩ := hnonempty
    have hm' := Finset.mem_inter.mp hm
    have hum : C.Adj u m := (C.mem_neighborFinset u m).mp hm'.1
    have hvm : C.Adj v m := (C.mem_neighborFinset v m).mp hm'.2
    have hmEligible : m ∈ mixedGridEligibleIntermediateNeighbors H K C u x := by
      apply Finset.mem_filter.mpr
      refine ⟨hm'.1, ?_⟩
      have hallowed := mixedGrid_neighbor_column_allowed H K C code v m hvm
      simpa [hv'.2] using hallowed
    refine ⟨m, hmEligible, ?_⟩
    apply mixedGridRowRoute_eq_of_adj_of_row H K C code
    · exact C.adj_symm hvm
    · exact hv'.2

/-- Exact per-row common-neighbour count: four plus the `H`-overlap of the
source and target rows. -/
theorem MuThreeMixedGridCode.commonNeighborMatesInRow_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow (mixedGridCommonNeighborGraph K C) u x).card =
      4 + (mixedGridHCommonColumns H u.1.1 x).card := by
  rw [code.commonNeighborMatesInRow_card_eq_eligible H K C u x hxu,
    code.eligibleIntermediateNeighbors_card H K C u x,
    code.commonAllowedColumns_card H K C u.1.1 x]

/-- **Per-cell defect row law.**  The residual count plus the `H` overlap
and the occupied rook indicator is exactly two. -/
theorem MuThreeMixedGridCode.residualMatesInRow_add_overlap_add_indicator
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow (mixedGridSquareResidualGraph K C) u x).card +
      (mixedGridHCommonColumns H u.1.1 x).card +
      (if K x u.1.2 then 0 else 1) = 2 := by
  have hledger := code.rowLedger_card H K C u x hxu
  have hQ := code.commonNeighborMatesInRow_card H K C u x hxu
  have hR := code.rookMatesInRow_card H K C u x hxu
  rw [hQ, hR] at hledger
  omega

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.eligibleIntermediateNeighbors_card
#print axioms Erdos85.mixedGridIntermediateToRowMate_spec
#print axioms
  Erdos85.MuThreeMixedGridCode.commonNeighborMatesInRow_card_eq_eligible
#print axioms Erdos85.MuThreeMixedGridCode.commonNeighborMatesInRow_card
#print axioms
  Erdos85.MuThreeMixedGridCode.residualMatesInRow_add_overlap_add_indicator
