import Proofs.Erdos85MuThreeMixedGridCycleSectorPropagation

/-!
# Local closure of an occupied H-sector

If an occupied cell is an `H`-edge, then every `H`-edge incident with either
endpoint is also outside `K`.  Thus the occupied `H \ K` cells occur as whole
bipartite `H`-cycles, not isolated edges.
-/

open SimpleGraph

namespace Erdos85

/-- An occupied `H`-cell forces every other `H`-cell in its row to remain
occupied. -/
theorem MuThreeMixedGridCode.not_K_of_H_same_row_of_H_cell
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (huH : H u.1.1 u.1.2)
    {y : Y} (hyH : H u.1.1 y) : ¬ K u.1.1 y := by
  let c := (relationBipartiteGraph H).connectedComponentMk (Sum.inl u.1.1)
  have huc : Sum.inl u.1.1 ∈ c.supp :=
    (ConnectedComponent.mem_supp_iff c _).mpr rfl
  exact code.cycleComponent_all_not_K_of_cell H K C c u huH huc
    u.1.1 y hyH huc

/-- Column-dually, an occupied `H`-cell forces every other `H`-cell in its
column to remain occupied. -/
theorem MuThreeMixedGridCode.not_K_of_H_same_column_of_H_cell
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (huH : H u.1.1 u.1.2)
    {x : X} (hxH : H x u.1.2) : ¬ K x u.1.2 := by
  let c := (relationBipartiteGraph H).connectedComponentMk (Sum.inl u.1.1)
  have huc : Sum.inl u.1.1 ∈ c.supp :=
    (ConnectedComponent.mem_supp_iff c _).mpr rfl
  have hur : Sum.inr u.1.2 ∈ c.supp := by
    apply (ConnectedComponent.mem_supp_congr_adj c
      (show (relationBipartiteGraph H).Adj (Sum.inl u.1.1)
        (Sum.inr u.1.2) from huH)).mp
    exact huc
  have hxc : Sum.inl x ∈ c.supp := by
    apply (ConnectedComponent.mem_supp_congr_adj c
      (show (relationBipartiteGraph H).Adj (Sum.inr u.1.2)
        (Sum.inl x) from hxH)).mp
    exact hur
  exact code.cycleComponent_all_not_K_of_cell H K C c u huH huc
    x u.1.2 hxH hxc

/-- Both shores of an occupied `H`-cell are locally closed under the
two-factor `H`. -/
theorem MuThreeMixedGridCode.H_cell_local_cycle_closure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (huH : H u.1.1 u.1.2) :
    (∀ y, H u.1.1 y → ¬ K u.1.1 y) ∧
      (∀ x, H x u.1.2 → ¬ K x u.1.2) := by
  constructor
  · exact fun y hy => code.not_K_of_H_same_row_of_H_cell H K C u huH hy
  · exact fun x hx => code.not_K_of_H_same_column_of_H_cell H K C u huH hx

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.not_K_of_H_same_row_of_H_cell
#print axioms
  Erdos85.MuThreeMixedGridCode.not_K_of_H_same_column_of_H_cell
#print axioms Erdos85.MuThreeMixedGridCode.H_cell_local_cycle_closure
