import Proofs.Erdos85MuThreeMixedGridCode

/-!
# The square partition of a mixed `mu = 3` exterior grid

For distinct occupied cells there are exactly three possibilities: they share
a row or column, they have one common exterior neighbour, or they have none.
The rook law separates the first possibility from the second, while
C4-freeness makes the common-neighbour count zero or one.  This is the
combinatorial content of `Q + D_C + Rowcol = J - I`.
-/

open SimpleGraph

namespace Erdos85

/-- The rook graph on the occupied cells: distinct cells in one row or one
column. -/
def mixedGridRowColumnGraph {X Y : Type*} (K : X → Y → Prop) :
    SimpleGraph (muThreeMixedCell K) where
  Adj u v := u ≠ v ∧ (u.1.1 = v.1.1 ∨ u.1.2 = v.1.2)
  symm := by
    constructor
    rintro u v ⟨hne, hrow | hcol⟩
    · exact ⟨hne.symm, Or.inl hrow.symm⟩
    · exact ⟨hne.symm, Or.inr hcol.symm⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- The graph joining two cells when they have exactly one common exterior
neighbour.  Under C4-freeness, this is the support of the off-diagonal square
of the adjacency matrix. -/
def mixedGridCommonNeighborGraph {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj] :
    SimpleGraph (muThreeMixedCell K) where
  Adj u v := u ≠ v ∧
    (C.neighborFinset u ∩ C.neighborFinset v).card = 1
  symm := by
    constructor
    rintro u v ⟨hne, hcard⟩
    exact ⟨hne.symm, by simpa [Finset.inter_comm] using hcard⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- The residual relation in the square partition: distinct cross-cells with
no common exterior neighbour. -/
def mixedGridSquareResidualGraph {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj] :
    SimpleGraph (muThreeMixedCell K) where
  Adj u v := u ≠ v ∧
    ¬ (mixedGridRowColumnGraph K).Adj u v ∧
    (C.neighborFinset u ∩ C.neighborFinset v).card = 0
  symm := by
    constructor
    rintro u v ⟨hne, hrook, hcard⟩
    refine ⟨hne.symm, ?_, ?_⟩
    · intro h
      exact hrook ((mixedGridRowColumnGraph K).adj_symm h)
    · simpa [Finset.inter_comm] using hcard
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Canonical local-finiteness instances for the three constructed graphs.
Lean 4.31 no longer infers these uniformly at uses of `degree`, even though
their ambient cell type is finite. -/
noncomputable instance mixedGridRowColumnGraphLocallyFinite
    {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → Prop) [DecidableRel K] :
    (mixedGridRowColumnGraph K).LocallyFinite :=
  by classical exact fun _u => Fintype.ofFinite _

noncomputable instance mixedGridCommonNeighborGraphLocallyFinite
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj] :
    (mixedGridCommonNeighborGraph K C).LocallyFinite :=
  by classical exact fun _u => Fintype.ofFinite _

noncomputable instance mixedGridSquareResidualGraphLocallyFinite
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj] :
    (mixedGridSquareResidualGraph K C).LocallyFinite :=
  by classical exact fun _u => Fintype.ofFinite _

/-- A rook-related pair cannot have a common exterior neighbour. -/
theorem MuThreeMixedGridCode.rowColumn_common_neighbor_card_eq_zero
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u v : muThreeMixedCell K}
    (hrook : (mixedGridRowColumnGraph K).Adj u v) :
    (C.neighborFinset u ∩ C.neighborFinset v).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwu : C.Adj w u :=
    C.adj_symm ((C.mem_neighborFinset u w).mp (Finset.mem_inter.mp hw).1)
  have hwv : C.Adj w v :=
    C.adj_symm ((C.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).2)
  have hsep := code.rook w u v hwu hwv hrook.1
  exact hrook.2.elim hsep.1 hsep.2

/-- The three square relations cover the complete graph on occupied cells. -/
theorem MuThreeMixedGridCode.square_partition_sup_eq_top
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridCommonNeighborGraph K C ⊔
        mixedGridSquareResidualGraph K C ⊔
        mixedGridRowColumnGraph K = ⊤ := by
  ext u v
  simp only [sup_adj, mixedGridCommonNeighborGraph,
    mixedGridSquareResidualGraph, mixedGridRowColumnGraph, top_adj]
  constructor
  · rintro ((⟨hne, _⟩ | ⟨hne, _, _⟩) | ⟨hne, _⟩) <;> exact hne
  · intro hne
    by_cases hrook : u ≠ v ∧ (u.1.1 = v.1.1 ∨ u.1.2 = v.1.2)
    · exact Or.inr hrook
    · have hle := MuThreeMixedGridCode.common_neighbor_card_le_one
        H K C code u v hne
      by_cases hzero : (C.neighborFinset u ∩ C.neighborFinset v).card = 0
      · exact Or.inl (Or.inr ⟨hne, hrook, hzero⟩)
      · have hone : (C.neighborFinset u ∩ C.neighborFinset v).card = 1 := by
          omega
        exact Or.inl (Or.inl ⟨hne, hone⟩)

/-- The common-neighbour and rook relations are edge-disjoint. -/
theorem MuThreeMixedGridCode.common_inf_rowColumn_eq_bot
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridCommonNeighborGraph K C ⊓ mixedGridRowColumnGraph K = ⊥ := by
  ext u v
  constructor
  · intro h
    have hcommon := h.1
    have hrook := h.2
    have hzero := MuThreeMixedGridCode.rowColumn_common_neighbor_card_eq_zero
      H K C code hrook
    have hone := hcommon.2
    omega
  · intro h
    exact False.elim h

/-- The residual relation is disjoint from the other two by construction. -/
theorem mixedGridSquareResidualGraph_disjoint
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj] :
    mixedGridSquareResidualGraph K C ⊓
        (mixedGridCommonNeighborGraph K C ⊔ mixedGridRowColumnGraph K) = ⊥ := by
  ext u v
  constructor
  · intro h
    have hres := h.1
    rcases h.2 with hcommon | hrook
    · have hzero := hres.2.2
      have hone := hcommon.2
      omega
    · exact hres.2.1 hrook
  · intro h
    exact False.elim h

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.rowColumn_common_neighbor_card_eq_zero
#print axioms Erdos85.MuThreeMixedGridCode.square_partition_sup_eq_top
#print axioms Erdos85.MuThreeMixedGridCode.common_inf_rowColumn_eq_bot
#print axioms Erdos85.mixedGridSquareResidualGraph_disjoint
