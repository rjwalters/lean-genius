import Proofs.Erdos85MuThreeMixedGridSquareDegrees

/-!
# The partner graph in the all-triangle mixed sector

Intersect exterior adjacency with the occupied rook graph.  At a cell whose
coordinates are `H`-adjacent, both same-coordinate hits vanish; every other
cell has one same-row and one same-column partner.  When `H` and the
forbidden factor `K` are edge-disjoint, this gives the characteristic
all-triangle split: 16 isolated `H`-cells and 32 degree-two partner cells.
-/

open SimpleGraph

namespace Erdos85

/-- Exterior edges that preserve one grid coordinate. -/
def mixedGridPartnerGraph
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) :
    SimpleGraph (muThreeMixedCell K) :=
  C ⊓ mixedGridRowColumnGraph K

/-- The partner graph has degree zero on an `H`-cell and degree two on every
other occupied cell. -/
theorem MuThreeMixedGridCode.partnerGraph_degree
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    (mixedGridPartnerGraph K C).degree u =
      if H u.1.1 u.1.2 then 0 else 2 := by
  classical
  let A := (C.neighborFinset u).filter fun v => v.1.1 = u.1.1
  let B := (C.neighborFinset u).filter fun v => v.1.2 = u.1.2
  have hneighbors : (mixedGridPartnerGraph K C).neighborFinset u = A ∪ B := by
    ext v
    simp only [mixedGridPartnerGraph, mem_neighborFinset, inf_adj,
      mixedGridRowColumnGraph, Finset.mem_union, A, B, Finset.mem_filter]
    constructor
    · rintro ⟨huv, _hne, hrow | hcol⟩
      · exact Or.inl ⟨(C.mem_neighborFinset u v).mpr huv, hrow⟩
      · exact Or.inr ⟨(C.mem_neighborFinset u v).mpr huv, hcol⟩
    · rintro (⟨huv, hrow⟩ | ⟨huv, hcol⟩)
      · have hadj := (C.mem_neighborFinset u v).mp huv
        exact ⟨hadj, C.ne_of_adj hadj, Or.inl hrow⟩
      · have hadj := (C.mem_neighborFinset u v).mp huv
        exact ⟨hadj, C.ne_of_adj hadj, Or.inr hcol⟩
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    have hrow := (Finset.mem_filter.mp hvA).2
    have hcol := (Finset.mem_filter.mp hvB).2
    have hvu : v = u := by
      apply Subtype.ext
      exact Prod.ext hrow hcol
    have hadj := (C.mem_neighborFinset u v).mp (Finset.mem_filter.mp hvA).1
    exact C.loopless u (hvu ▸ hadj)
  rw [← (mixedGridPartnerGraph K C).card_neighborFinset_eq_degree,
    hneighbors, Finset.card_union_of_disjoint hdisjoint]
  change A.card + B.card = _
  rw [show A.card = (if H u.1.1 u.1.2 then 0 else 1) from code.row_hit u u.1.1,
    show B.card = (if H u.1.1 u.1.2 then 0 else 1) from code.column_hit u u.1.2]
  split <;> simp_all

/-- Every partner edge lies entirely in the non-`H` sector. -/
theorem MuThreeMixedGridCode.partnerGraph_adj_nonH
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u v : muThreeMixedCell K}
    (huv : (mixedGridPartnerGraph K C).Adj u v) :
    ¬ H u.1.1 u.1.2 ∧ ¬ H v.1.1 v.1.2 := by
  constructor
  · intro huH
    have hdeg := code.partnerGraph_degree H K C u
    rw [if_pos huH] at hdeg
    have hmem : v ∈ (mixedGridPartnerGraph K C).neighborFinset u :=
      ((mixedGridPartnerGraph K C).mem_neighborFinset u v).mpr huv
    rw [← (mixedGridPartnerGraph K C).card_neighborFinset_eq_degree,
      hdeg, Finset.card_eq_zero] at hmem
    exact Finset.notMem_empty v hmem
  · intro hvH
    have hdeg := code.partnerGraph_degree H K C v
    rw [if_pos hvH] at hdeg
    have hmem : u ∈ (mixedGridPartnerGraph K C).neighborFinset v :=
      ((mixedGridPartnerGraph K C).mem_neighborFinset v u).mpr
        ((mixedGridPartnerGraph K C).adj_symm huv)
    rw [← (mixedGridPartnerGraph K C).card_neighborFinset_eq_degree,
      hdeg, Finset.card_eq_zero] at hmem
    exact Finset.notMem_empty u hmem

/-- Occupied cells whose coordinates form an `H`-edge. -/
def mixedGridHCells
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K] :
    Finset (muThreeMixedCell K) :=
  Finset.univ.filter fun u => H u.1.1 u.1.2

/-- Occupied cells whose coordinates are not an `H`-edge. -/
def mixedGridNonHCells
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K] :
    Finset (muThreeMixedCell K) :=
  Finset.univ.filter fun u => ¬ H u.1.1 u.1.2

/-- If `H` and `K` are edge-disjoint, all sixteen `H`-edges occur as
occupied cells. -/
theorem MuThreeMixedGridCode.card_HCells_eq_sixteen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    (mixedGridHCells H K).card = 16 := by
  classical
  have hmaps : ∀ u ∈ mixedGridHCells H K,
      u.1.1 ∈ (Finset.univ : Finset X) := by
    intro u _hu
    exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ x : X, (((mixedGridHCells H K).filter fun u => u.1.1 = x).card) =
        ∑ _x : X, 2 := by
      apply Finset.sum_congr rfl
      intro x _hx
      let S := (mixedGridHCells H K).filter fun u => u.1.1 = x
      let T := (Finset.univ : Finset Y).filter fun y => H x y
      have hST : S.card = T.card := by
        apply Finset.card_bij (fun u _hu => u.1.2)
        · intro u hu
          have huS := Finset.mem_filter.mp hu
          have huH := (Finset.mem_filter.mp huS.1).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [huS.2] using huH⟩
        · intro u hu v hv heq
          apply Subtype.ext
          apply Prod.ext
          · exact (Finset.mem_filter.mp hu).2.trans
              (Finset.mem_filter.mp hv).2.symm
          · exact heq
        · intro y hy
          have hyH : H x y := (Finset.mem_filter.mp hy).2
          let u : muThreeMixedCell K := ⟨(x, y), hdisjoint x y hyH⟩
          refine ⟨u, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hyH⟩, rfl⟩
      change S.card = 2
      rw [hST]
      exact code.H_twoRegular.1 x
    _ = 16 := by simp [code.card_left]

/-- The complementary partner-support sector has 32 cells. -/
theorem MuThreeMixedGridCode.card_nonHCells_eq_thirtyTwo
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    (mixedGridNonHCells H K).card = 32 := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (muThreeMixedCell K)))
    (p := fun u => H u.1.1 u.1.2)
  change (mixedGridHCells H K).card + (mixedGridNonHCells H K).card =
      Fintype.card (muThreeMixedCell K) at hpartition
  rw [code.card_HCells_eq_sixteen H K C hdisjoint,
    code.card_mixedCell_eq_fortyEight H K C] at hpartition
  omega

/-- In the all-triangle (`H`–`K` disjoint) sector, the partner graph has
exactly 32 edges: it is 2-regular on its 32-cell support and isolated on the
16 `H`-cells. -/
theorem MuThreeMixedGridCode.partnerGraph_card_edges_eq_thirtyTwo
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    (mixedGridPartnerGraph K C).edgeFinset.card = 32 := by
  classical
  let P := mixedGridPartnerGraph K C
  have hhand := P.sum_degrees_eq_twice_card_edges
  have hsum : ∑ u, P.degree u = 64 := by
    calc
      ∑ u, P.degree u = ∑ u, if H u.1.1 u.1.2 then 0 else 2 := by
        apply Finset.sum_congr rfl
        intro u _hu
        exact code.partnerGraph_degree H K C u
      _ = 2 * (mixedGridNonHCells H K).card := by
        classical
        simp [mixedGridNonHCells, Finset.mul_sum]
      _ = 64 := by rw [code.card_nonHCells_eq_thirtyTwo H K C hdisjoint]
  change (∑ u, P.degree u) = 2 * P.edgeFinset.card at hhand
  rw [hsum] at hhand
  omega

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.partnerGraph_degree
#print axioms Erdos85.MuThreeMixedGridCode.partnerGraph_adj_nonH
#print axioms Erdos85.MuThreeMixedGridCode.card_HCells_eq_sixteen
#print axioms Erdos85.MuThreeMixedGridCode.card_nonHCells_eq_thirtyTwo
#print axioms Erdos85.MuThreeMixedGridCode.partnerGraph_card_edges_eq_thirtyTwo
