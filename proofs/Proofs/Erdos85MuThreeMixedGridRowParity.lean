import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Row parity in every mixed μ=3 grid

The row-hit law says that, inside any fixed row, the non-`H` occupied cells
have degree one in `C`, while the `H` occupied cells have degree zero.  Thus
the non-`H` cells in each row are paired, and in particular their number is
even.
-/

open SimpleGraph

namespace Erdos85

/-- The part of `C` whose edges stay in one grid row. -/
def mixedGridOwnRowGraph {X Y : Type*} {K : X → Y → Prop}
    (C : SimpleGraph (muThreeMixedCell K)) :
    SimpleGraph (muThreeMixedCell K) where
  Adj u v := C.Adj u v ∧ u.1.1 = v.1.1
  symm := by
    constructor
    intro u v huv
    exact ⟨(C.adj_comm u v).mp huv.1, huv.2.symm⟩
  loopless := by
    constructor
    intro u huu
    exact C.loopless.irrefl u huu.1

instance mixedGridOwnRowGraph_adjDecidable
    {X Y : Type*} [DecidableEq X]
    {K : X → Y → Prop} (C : SimpleGraph (muThreeMixedCell K))
    [DecidableRel C.Adj] :
    DecidableRel (mixedGridOwnRowGraph C).Adj :=
  fun u v => inferInstanceAs (Decidable (C.Adj u v ∧ u.1.1 = v.1.1))

theorem MuThreeMixedGridCode.ownRowGraph_degree
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    (mixedGridOwnRowGraph C).degree u =
      if H u.1.1 u.1.2 then 0 else 1 := by
  rw [← (mixedGridOwnRowGraph C).card_neighborFinset_eq_degree]
  have hfinset : (mixedGridOwnRowGraph C).neighborFinset u =
      (C.neighborFinset u).filter (fun v => v.1.1 = u.1.1) := by
    ext v
    simp [mixedGridOwnRowGraph, eq_comm]
  rw [hfinset]
  exact code.row_hit u u.1.1

/-- Globally, the number of occupied non-`H` cells is even.  Equivalently,
the own-row edges pair those cells. -/
theorem MuThreeMixedGridCode.even_card_occupied_not_H
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    Even (((Finset.univ : Finset (muThreeMixedCell K)).filter
      fun u => ¬ H u.1.1 u.1.2).card) := by
  have hset :
      ((Finset.univ : Finset (muThreeMixedCell K)).filter
        fun u => ¬ H u.1.1 u.1.2) =
      ((Finset.univ : Finset (muThreeMixedCell K)).filter
        fun u => Odd ((mixedGridOwnRowGraph C).degree u)) := by
    apply Finset.filter_congr
    intro u _
    rw [code.ownRowGraph_degree H K C]
    by_cases hH : H u.1.1 u.1.2 <;> simp [hH]
  rw [hset]
  exact (mixedGridOwnRowGraph C).even_card_odd_degree_vertices

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.ownRowGraph_degree
#print axioms Erdos85.MuThreeMixedGridCode.even_card_occupied_not_H
