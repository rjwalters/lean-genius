import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Own- and foreign-fiber counts in every mixed μ=3 sector

An occupied cell on an `H` edge misses its own row and column and hits all six
foreign fibers.  A non-`H` cell has one neighbour in its own row and column,
leaving five foreign-row and five foreign-column neighbours.  These statements
use only the uniform mixed-grid code, not an all-triangle or all-triangle-free
specialization.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact own-row count for an arbitrary occupied mixed-grid cell. -/
theorem MuThreeMixedGridCode.ownRow_neighbor_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    ((C.neighborFinset u).filter fun v => v.1.1 = u.1.1).card =
      if H u.1.1 u.1.2 then 0 else 1 := by
  exact code.row_hit u u.1.1

/-- Exact own-column count for an arbitrary occupied mixed-grid cell. -/
theorem MuThreeMixedGridCode.ownColumn_neighbor_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    ((C.neighborFinset u).filter fun v => v.1.2 = u.1.2).card =
      if H u.1.1 u.1.2 then 0 else 1 := by
  exact code.column_hit u u.1.2

/-- `H`-cells hit six foreign rows; non-`H` cells hit five. -/
theorem MuThreeMixedGridCode.foreignRow_neighbor_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    ((C.neighborFinset u).filter fun v => ¬ v.1.1 = u.1.1).card =
      if H u.1.1 u.1.2 then 6 else 5 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := C.neighborFinset u) (p := fun v => v.1.1 = u.1.1)
  have htotal : (C.neighborFinset u).card = 6 := by
    rw [C.card_neighborFinset_eq_degree, code.degree_eq_six H K C u]
  have hown := code.ownRow_neighbor_card H K C u
  change ((C.neighborFinset u).filter (fun v => v.1.1 = u.1.1)).card +
      ((C.neighborFinset u).filter (fun v => ¬ v.1.1 = u.1.1)).card =
        (C.neighborFinset u).card at hsplit
  rw [htotal] at hsplit
  by_cases hH : H u.1.1 u.1.2
  · have hown0 :
        ((C.neighborFinset u).filter (fun v => v.1.1 = u.1.1)).card = 0 := by
      simpa [hH] using hown
    have hforeign :
        ((C.neighborFinset u).filter (fun v => ¬ v.1.1 = u.1.1)).card = 6 := by
      omega
    simpa [hH] using hforeign
  · have hown1 :
        ((C.neighborFinset u).filter (fun v => v.1.1 = u.1.1)).card = 1 := by
      simpa [hH] using hown
    have hforeign :
        ((C.neighborFinset u).filter (fun v => ¬ v.1.1 = u.1.1)).card = 5 := by
      omega
    simpa [hH] using hforeign

/-- `H`-cells hit six foreign columns; non-`H` cells hit five. -/
theorem MuThreeMixedGridCode.foreignColumn_neighbor_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    ((C.neighborFinset u).filter fun v => ¬ v.1.2 = u.1.2).card =
      if H u.1.1 u.1.2 then 6 else 5 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := C.neighborFinset u) (p := fun v => v.1.2 = u.1.2)
  have htotal : (C.neighborFinset u).card = 6 := by
    rw [C.card_neighborFinset_eq_degree, code.degree_eq_six H K C u]
  have hown := code.ownColumn_neighbor_card H K C u
  change ((C.neighborFinset u).filter (fun v => v.1.2 = u.1.2)).card +
      ((C.neighborFinset u).filter (fun v => ¬ v.1.2 = u.1.2)).card =
        (C.neighborFinset u).card at hsplit
  rw [htotal] at hsplit
  by_cases hH : H u.1.1 u.1.2
  · have hown0 :
        ((C.neighborFinset u).filter (fun v => v.1.2 = u.1.2)).card = 0 := by
      simpa [hH] using hown
    have hforeign :
        ((C.neighborFinset u).filter (fun v => ¬ v.1.2 = u.1.2)).card = 6 := by
      omega
    simpa [hH] using hforeign
  · have hown1 :
        ((C.neighborFinset u).filter (fun v => v.1.2 = u.1.2)).card = 1 := by
      simpa [hH] using hown
    have hforeign :
        ((C.neighborFinset u).filter (fun v => ¬ v.1.2 = u.1.2)).card = 5 := by
      omega
    simpa [hH] using hforeign

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.ownRow_neighbor_card
#print axioms Erdos85.MuThreeMixedGridCode.ownColumn_neighbor_card
#print axioms Erdos85.MuThreeMixedGridCode.foreignRow_neighbor_card
#print axioms Erdos85.MuThreeMixedGridCode.foreignColumn_neighbor_card
