import Proofs.Erdos85MuThreePartnerEdgeCapacity

/-!
# Row and column partner matchings

The partner graph splits canonically into its same-row and same-column
edges.  Each color has degree zero on an `H`-cell and degree one otherwise.
In the all-triangle sector, each color is therefore a 16-edge perfect
matching of the 32 non-`H` cells.
-/

open SimpleGraph

namespace Erdos85

/-- Exterior partner edges preserving the row coordinate. -/
def mixedGridRowPartnerGraph
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) :
    SimpleGraph (muThreeMixedCell K) where
  Adj u v := C.Adj u v ∧ u.1.1 = v.1.1
  symm := by
    constructor
    rintro u v ⟨huv, hrow⟩
    exact ⟨C.adj_symm huv, hrow.symm⟩
  loopless := by
    constructor
    intro u h
    exact C.irrefl u h.1

/-- Exterior partner edges preserving the column coordinate. -/
def mixedGridColumnPartnerGraph
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) :
    SimpleGraph (muThreeMixedCell K) where
  Adj u v := C.Adj u v ∧ u.1.2 = v.1.2
  symm := by
    constructor
    rintro u v ⟨huv, hcol⟩
    exact ⟨C.adj_symm huv, hcol.symm⟩
  loopless := by
    constructor
    intro u h
    exact C.irrefl u h.1

/-- The row-partner degree is zero on `H`-cells and one elsewhere. -/
theorem MuThreeMixedGridCode.rowPartnerGraph_degree
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    (mixedGridRowPartnerGraph K C).degree u =
      if H u.1.1 u.1.2 then 0 else 1 := by
  have hneighbors : (mixedGridRowPartnerGraph K C).neighborFinset u =
      (C.neighborFinset u).filter fun v => v.1.1 = u.1.1 := by
    ext v
    simp [mixedGridRowPartnerGraph, C.mem_neighborFinset]
  rw [← (mixedGridRowPartnerGraph K C).card_neighborFinset_eq_degree,
    hneighbors]
  exact code.row_hit u u.1.1

/-- Column dual of `rowPartnerGraph_degree`. -/
theorem MuThreeMixedGridCode.columnPartnerGraph_degree
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    (mixedGridColumnPartnerGraph K C).degree u =
      if H u.1.1 u.1.2 then 0 else 1 := by
  have hneighbors : (mixedGridColumnPartnerGraph K C).neighborFinset u =
      (C.neighborFinset u).filter fun v => v.1.2 = u.1.2 := by
    ext v
    simp [mixedGridColumnPartnerGraph, C.mem_neighborFinset]
  rw [← (mixedGridColumnPartnerGraph K C).card_neighborFinset_eq_degree,
    hneighbors]
  exact code.column_hit u u.1.2

/-- Each colored partner graph is a matching. -/
theorem MuThreeMixedGridCode.rowPartnerGraph_degree_le_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    (mixedGridRowPartnerGraph K C).degree u ≤ 1 := by
  rw [code.rowPartnerGraph_degree H K C u]
  split <;> omega

theorem MuThreeMixedGridCode.columnPartnerGraph_degree_le_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    (mixedGridColumnPartnerGraph K C).degree u ≤ 1 := by
  rw [code.columnPartnerGraph_degree H K C u]
  split <;> omega

/-- The two colored matchings partition the partner graph. -/
theorem mixedGrid_rowPartner_sup_columnPartner
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) :
    mixedGridRowPartnerGraph K C ⊔ mixedGridColumnPartnerGraph K C =
      mixedGridPartnerGraph K C := by
  ext u v
  simp [mixedGridRowPartnerGraph, mixedGridColumnPartnerGraph,
    mixedGridPartnerGraph, mixedGridRowColumnGraph, and_or_left]

/-- No partner edge can preserve both coordinates. -/
theorem mixedGrid_rowPartner_inf_columnPartner
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) :
    mixedGridRowPartnerGraph K C ⊓ mixedGridColumnPartnerGraph K C = ⊥ := by
  ext u v
  constructor
  · rintro ⟨⟨huv, hrow⟩, _huv', hcol⟩
    have huvEq : u = v := by
      apply Subtype.ext
      exact Prod.ext hrow hcol
    exact (C.ne_of_adj huv huvEq).elim
  · intro h
    exact False.elim h

/-- The row matching has 16 edges in the all-triangle sector. -/
theorem MuThreeMixedGridCode.rowPartnerGraph_card_edges_eq_sixteen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    (mixedGridRowPartnerGraph K C).edgeFinset.card = 16 := by
  classical
  let P := mixedGridRowPartnerGraph K C
  have hhand := P.sum_degrees_eq_twice_card_edges
  have hsum : ∑ u, P.degree u = 32 := by
    calc
      ∑ u, P.degree u = ∑ u, if H u.1.1 u.1.2 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro u _hu
        exact code.rowPartnerGraph_degree H K C u
      _ = (mixedGridNonHCells H K).card := by
        simp [mixedGridNonHCells]
      _ = 32 := code.card_nonHCells_eq_thirtyTwo H K C hdisjoint
  change (∑ u, P.degree u) = 2 * P.edgeFinset.card at hhand
  rw [hsum] at hhand
  omega

/-- The column matching also has 16 edges. -/
theorem MuThreeMixedGridCode.columnPartnerGraph_card_edges_eq_sixteen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    (mixedGridColumnPartnerGraph K C).edgeFinset.card = 16 := by
  classical
  let P := mixedGridColumnPartnerGraph K C
  have hhand := P.sum_degrees_eq_twice_card_edges
  have hsum : ∑ u, P.degree u = 32 := by
    calc
      ∑ u, P.degree u = ∑ u, if H u.1.1 u.1.2 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro u _hu
        exact code.columnPartnerGraph_degree H K C u
      _ = (mixedGridNonHCells H K).card := by
        simp [mixedGridNonHCells]
      _ = 32 := code.card_nonHCells_eq_thirtyTwo H K C hdisjoint
  change (∑ u, P.degree u) = 2 * P.edgeFinset.card at hhand
  rw [hsum] at hhand
  omega

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.rowPartnerGraph_degree
#print axioms Erdos85.MuThreeMixedGridCode.columnPartnerGraph_degree
#print axioms Erdos85.mixedGrid_rowPartner_sup_columnPartner
#print axioms Erdos85.mixedGrid_rowPartner_inf_columnPartner
#print axioms Erdos85.MuThreeMixedGridCode.rowPartnerGraph_card_edges_eq_sixteen
#print axioms Erdos85.MuThreeMixedGridCode.columnPartnerGraph_card_edges_eq_sixteen
