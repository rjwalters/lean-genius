import Proofs.Erdos85MuThreeMixedGridOwnFiberCounts

/-!
# Canonical foreign-row and foreign-column bijections

For a fixed occupied cell `u`, its six exterior neighbours are indexed
bijectively both by the six rows not adjacent to `u`'s column in `H` and by
the six columns not adjacent to `u`'s row.  These equivalences expose the
foreign-fiber permutations where a mixed-sector contradiction must live.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The unique neighbour of `u` in an `H`-nonneighbor row. -/
noncomputable def MuThreeMixedGridCode.foreignRowNeighbor
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (x : {x : X // ¬ H x u.1.2}) : muThreeMixedCell K :=
  Classical.choose
    ((code.existsUnique_row_neighbor_iff H K C u x.1).mpr x.2)

theorem MuThreeMixedGridCode.foreignRowNeighbor_spec
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (x : {x : X // ¬ H x u.1.2}) :
    C.Adj u (code.foreignRowNeighbor H K C u x) ∧
      (code.foreignRowNeighbor H K C u x).1.1 = x.1 := by
  exact Classical.choose_spec
    ((code.existsUnique_row_neighbor_iff H K C u x.1).mpr x.2) |>.1

theorem MuThreeMixedGridCode.foreignRowNeighbor_unique
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (x : {x : X // ¬ H x u.1.2}) (v : muThreeMixedCell K)
    (huv : C.Adj u v) (hvx : v.1.1 = x.1) :
    v = code.foreignRowNeighbor H K C u x := by
  exact Classical.choose_spec
    ((code.existsUnique_row_neighbor_iff H K C u x.1).mpr x.2) |>.2
      v ⟨huv, hvx⟩

/-- The unique neighbour of `u` in an `H`-nonneighbor column. -/
noncomputable def MuThreeMixedGridCode.foreignColumnNeighbor
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (y : {y : Y // ¬ H u.1.1 y}) : muThreeMixedCell K :=
  Classical.choose
    ((code.existsUnique_column_neighbor_iff H K C u y.1).mpr y.2)

theorem MuThreeMixedGridCode.foreignColumnNeighbor_spec
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (y : {y : Y // ¬ H u.1.1 y}) :
    C.Adj u (code.foreignColumnNeighbor H K C u y) ∧
      (code.foreignColumnNeighbor H K C u y).1.2 = y.1 := by
  exact Classical.choose_spec
    ((code.existsUnique_column_neighbor_iff H K C u y.1).mpr y.2) |>.1

theorem MuThreeMixedGridCode.foreignColumnNeighbor_unique
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (y : {y : Y // ¬ H u.1.1 y}) (v : muThreeMixedCell K)
    (huv : C.Adj u v) (hvy : v.1.2 = y.1) :
    v = code.foreignColumnNeighbor H K C u y := by
  exact Classical.choose_spec
    ((code.existsUnique_column_neighbor_iff H K C u y.1).mpr y.2) |>.2
      v ⟨huv, hvy⟩

/-- Every actual neighbour of `u` lies in an `H`-nonneighbor row. -/
theorem MuThreeMixedGridCode.not_H_row_of_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) {u v : muThreeMixedCell K}
    (huv : C.Adj u v) : ¬ H v.1.1 u.1.2 := by
  intro hH
  have hzero := code.row_hit u v.1.1
  rw [if_pos hH] at hzero
  have hv : v ∈ (C.neighborFinset u).filter fun w => w.1.1 = v.1.1 :=
    Finset.mem_filter.mpr ⟨(C.mem_neighborFinset u v).mpr huv, rfl⟩
  rw [Finset.card_eq_zero.mp hzero] at hv
  exact Finset.notMem_empty v hv

/-- Every actual neighbour of `u` lies in an `H`-nonneighbor column. -/
theorem MuThreeMixedGridCode.not_H_column_of_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) {u v : muThreeMixedCell K}
    (huv : C.Adj u v) : ¬ H u.1.1 v.1.2 := by
  intro hH
  have hzero := code.column_hit u v.1.2
  rw [if_pos hH] at hzero
  have hv : v ∈ (C.neighborFinset u).filter fun w => w.1.2 = v.1.2 :=
    Finset.mem_filter.mpr ⟨(C.mem_neighborFinset u v).mpr huv, rfl⟩
  rw [Finset.card_eq_zero.mp hzero] at hv
  exact Finset.notMem_empty v hv

/-- The six eligible foreign rows are canonically equivalent to the six
neighbours of `u`. -/
noncomputable def MuThreeMixedGridCode.foreignRowEquivNeighbor
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    {x : X // ¬ H x u.1.2} ≃ {v // v ∈ C.neighborFinset u} where
  toFun x := ⟨code.foreignRowNeighbor H K C u x,
    (C.mem_neighborFinset u _).mpr (code.foreignRowNeighbor_spec H K C u x).1⟩
  invFun v := ⟨v.1.1.1, code.not_H_row_of_adj H K C
    ((C.mem_neighborFinset u v.1).mp v.2)⟩
  left_inv x := by
    apply Subtype.ext
    exact code.foreignRowNeighbor_spec H K C u x |>.2
  right_inv v := by
    apply Subtype.ext
    exact code.foreignRowNeighbor_unique H K C u
      ⟨v.1.1.1, code.not_H_row_of_adj H K C
        ((C.mem_neighborFinset u v.1).mp v.2)⟩ v.1
      ((C.mem_neighborFinset u v.1).mp v.2) rfl |>.symm

/-- Column-dual canonical equivalence. -/
noncomputable def MuThreeMixedGridCode.foreignColumnEquivNeighbor
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    {y : Y // ¬ H u.1.1 y} ≃ {v // v ∈ C.neighborFinset u} where
  toFun y := ⟨code.foreignColumnNeighbor H K C u y,
    (C.mem_neighborFinset u _).mpr (code.foreignColumnNeighbor_spec H K C u y).1⟩
  invFun v := ⟨v.1.1.2, code.not_H_column_of_adj H K C
    ((C.mem_neighborFinset u v.1).mp v.2)⟩
  left_inv y := by
    apply Subtype.ext
    exact code.foreignColumnNeighbor_spec H K C u y |>.2
  right_inv v := by
    apply Subtype.ext
    exact code.foreignColumnNeighbor_unique H K C u
      ⟨v.1.1.2, code.not_H_column_of_adj H K C
        ((C.mem_neighborFinset u v.1).mp v.2)⟩ v.1
      ((C.mem_neighborFinset u v.1).mp v.2) rfl |>.symm

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.foreignRowNeighbor_spec
#print axioms Erdos85.MuThreeMixedGridCode.foreignColumnNeighbor_spec
#print axioms Erdos85.MuThreeMixedGridCode.not_H_row_of_adj
#print axioms Erdos85.MuThreeMixedGridCode.not_H_column_of_adj
#print axioms Erdos85.MuThreeMixedGridCode.foreignRowEquivNeighbor
#print axioms Erdos85.MuThreeMixedGridCode.foreignColumnEquivNeighbor
