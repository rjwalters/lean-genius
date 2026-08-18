import Proofs.Erdos85MuThreeAllTrianglePartnerMatchings

/-!
# Partner involutions on the non-`H` sector

The row and column partner matchings define two fixed-point-free involutions
on the 32 non-`H` cells of the all-triangle sector.  They cannot commute at
any cell: a commuting square would be a four-cycle in the exterior graph.
-/

open SimpleGraph

namespace Erdos85

/-- The support of the partner graph. -/
def mixedGridNonHCell
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) :=
  {u : muThreeMixedCell K // ¬ H u.1.1 u.1.2}

instance mixedGridNonHCellFintype
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K] :
    Fintype (mixedGridNonHCell H K) := by
  unfold mixedGridNonHCell
  infer_instance

instance mixedGridNonHCellDecidableEq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) : DecidableEq (mixedGridNonHCell H K) := by
  unfold mixedGridNonHCell
  infer_instance

/-- A non-`H` cell has a unique row partner. -/
theorem MuThreeMixedGridCode.existsUnique_rowPartner
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : mixedGridNonHCell H K) :
    ∃! v : muThreeMixedCell K, (mixedGridRowPartnerGraph K C).Adj u.1 v := by
  have hdeg := code.rowPartnerGraph_degree H K C u.1
  rw [if_neg u.2] at hdeg
  rw [← (mixedGridRowPartnerGraph K C).card_neighborFinset_eq_degree] at hdeg
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdeg
  have hvMem : v ∈ (mixedGridRowPartnerGraph K C).neighborFinset u.1 := by
    rw [hv]
    simp
  refine ⟨v, ((mixedGridRowPartnerGraph K C).mem_neighborFinset u.1 v).mp hvMem, ?_⟩
  intro w huw
  have hwMem : w ∈ (mixedGridRowPartnerGraph K C).neighborFinset u.1 :=
    ((mixedGridRowPartnerGraph K C).mem_neighborFinset u.1 w).mpr huw
  rw [hv] at hwMem
  simpa using hwMem

/-- A non-`H` cell has a unique column partner. -/
theorem MuThreeMixedGridCode.existsUnique_columnPartner
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : mixedGridNonHCell H K) :
    ∃! v : muThreeMixedCell K, (mixedGridColumnPartnerGraph K C).Adj u.1 v := by
  have hdeg := code.columnPartnerGraph_degree H K C u.1
  rw [if_neg u.2] at hdeg
  rw [← (mixedGridColumnPartnerGraph K C).card_neighborFinset_eq_degree] at hdeg
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdeg
  have hvMem : v ∈ (mixedGridColumnPartnerGraph K C).neighborFinset u.1 := by
    rw [hv]
    simp
  refine ⟨v, ((mixedGridColumnPartnerGraph K C).mem_neighborFinset u.1 v).mp hvMem, ?_⟩
  intro w huw
  have hwMem : w ∈ (mixedGridColumnPartnerGraph K C).neighborFinset u.1 :=
    ((mixedGridColumnPartnerGraph K C).mem_neighborFinset u.1 w).mpr huw
  rw [hv] at hwMem
  simpa using hwMem

/-- Canonical row mate on the non-`H` sector. -/
noncomputable def MuThreeMixedGridCode.rowMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : mixedGridNonHCell H K) : mixedGridNonHCell H K := by
  let v := Classical.choose (code.existsUnique_rowPartner H K C u)
  have huv := Classical.choose_spec (code.existsUnique_rowPartner H K C u) |>.1
  have hP : (mixedGridPartnerGraph K C).Adj u.1 v := by
    exact ⟨huv.1, ⟨C.ne_of_adj huv.1, Or.inl huv.2⟩⟩
  exact ⟨v, (code.partnerGraph_adj_nonH H K C hP).2⟩

/-- Canonical column mate. -/
noncomputable def MuThreeMixedGridCode.columnMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : mixedGridNonHCell H K) : mixedGridNonHCell H K := by
  let v := Classical.choose (code.existsUnique_columnPartner H K C u)
  have huv := Classical.choose_spec (code.existsUnique_columnPartner H K C u) |>.1
  have hP : (mixedGridPartnerGraph K C).Adj u.1 v := by
    exact ⟨huv.1, ⟨C.ne_of_adj huv.1, Or.inr huv.2⟩⟩
  exact ⟨v, (code.partnerGraph_adj_nonH H K C hP).2⟩

theorem MuThreeMixedGridCode.rowMate_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    (mixedGridRowPartnerGraph K C).Adj u.1 (code.rowMate H K C u).1 := by
  exact Classical.choose_spec (code.existsUnique_rowPartner H K C u) |>.1

theorem MuThreeMixedGridCode.columnMate_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    (mixedGridColumnPartnerGraph K C).Adj u.1 (code.columnMate H K C u).1 := by
  exact Classical.choose_spec (code.existsUnique_columnPartner H K C u) |>.1

/-- Both mate maps are fixed-point-free. -/
theorem MuThreeMixedGridCode.rowMate_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.rowMate H K C u ≠ u := by
  intro h
  have hadj := code.rowMate_adj H K C u
  have hloop : C.Adj u.1 u.1 := by simpa [h] using hadj.1
  exact C.irrefl hloop

theorem MuThreeMixedGridCode.columnMate_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.columnMate H K C u ≠ u := by
  intro h
  have hadj := code.columnMate_adj H K C u
  have hloop : C.Adj u.1 u.1 := by simpa [h] using hadj.1
  exact C.irrefl hloop

/-- Row mate is an involution. -/
theorem MuThreeMixedGridCode.rowMate_rowMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.rowMate H K C (code.rowMate H K C u) = u := by
  apply Subtype.ext
  have huniq := Classical.choose_spec
    (code.existsUnique_rowPartner H K C (code.rowMate H K C u)) |>.2
  exact (huniq u.1 ((mixedGridRowPartnerGraph K C).adj_symm
    (code.rowMate_adj H K C u))).symm

/-- Column mate is an involution. -/
theorem MuThreeMixedGridCode.columnMate_columnMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.columnMate H K C (code.columnMate H K C u) = u := by
  apply Subtype.ext
  have huniq := Classical.choose_spec
    (code.existsUnique_columnPartner H K C (code.columnMate H K C u)) |>.2
  exact (huniq u.1 ((mixedGridColumnPartnerGraph K C).adj_symm
    (code.columnMate_adj H K C u))).symm

/-- The two mates of a cell are distinct. -/
theorem MuThreeMixedGridCode.rowMate_ne_columnMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.rowMate H K C u ≠ code.columnMate H K C u := by
  intro h
  have hr := code.rowMate_adj H K C u
  have hc := code.columnMate_adj H K C u
  have huv : u.1 = (code.rowMate H K C u).1 := by
    apply Subtype.ext
    apply Prod.ext
    · exact hr.2
    · exact hc.2.trans (congrArg (fun z : mixedGridNonHCell H K => z.1.1.2) h).symm
  exact C.ne_of_adj hr.1 huv

/-- **No commuting partner square.**  Row and column mate involutions fail to
commute at every non-`H` cell; otherwise their four partner edges form a C4. -/
theorem MuThreeMixedGridCode.rowMate_columnMate_ne_columnMate_rowMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.rowMate H K C (code.columnMate H K C u) ≠
      code.columnMate H K C (code.rowMate H K C u) := by
  intro hcomm
  let r := code.rowMate H K C u
  let c := code.columnMate H K C u
  let w := code.rowMate H K C c
  have hur := code.rowMate_adj H K C u
  have huc := code.columnMate_adj H K C u
  have hcw := code.rowMate_adj H K C c
  have hrw : (mixedGridColumnPartnerGraph K C).Adj r.1 w.1 := by
    have h := code.columnMate_adj H K C r
    have hw : w = code.columnMate H K C r := hcomm
    simpa [hw] using h
  have hrc : r.1 ≠ c.1 := by
    intro h
    exact code.rowMate_ne_columnMate H K C u (Subtype.ext h)
  have hle := code.common_neighbor_card_le_one H K C r.1 c.1 hrc
  have huMem : u.1 ∈ C.neighborFinset r.1 ∩ C.neighborFinset c.1 := by
    apply Finset.mem_inter.mpr
    exact ⟨(C.mem_neighborFinset r.1 u.1).mpr hur.1.symm,
      (C.mem_neighborFinset c.1 u.1).mpr huc.1.symm⟩
  have hwMem : w.1 ∈ C.neighborFinset r.1 ∩ C.neighborFinset c.1 := by
    apply Finset.mem_inter.mpr
    exact ⟨(C.mem_neighborFinset r.1 w.1).mpr hrw.1,
      (C.mem_neighborFinset c.1 w.1).mpr hcw.1⟩
  have huw : u.1 = w.1 := Finset.card_le_one.mp hle u.1 huMem w.1 hwMem
  have hurBoth : u.1 = r.1 := by
    apply Subtype.ext
    apply Prod.ext
    · exact hur.2
    · exact (congrArg (fun z : muThreeMixedCell K => z.1.2) huw).trans hrw.2.symm
  exact C.ne_of_adj hur.1 hurBoth

/-- The non-`H` subtype has cardinality 32 in the all-triangle sector. -/
theorem MuThreeMixedGridCode.card_nonHCell_eq_thirtyTwo
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    Fintype.card (mixedGridNonHCell H K) = 32 := by
  unfold mixedGridNonHCell
  rw [Fintype.card_subtype]
  exact code.card_nonHCells_eq_thirtyTwo H K C hdisjoint

/-- Row mate as a fixed-point-free involutive permutation. -/
noncomputable def MuThreeMixedGridCode.rowMateEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridNonHCell H K ≃ mixedGridNonHCell H K where
  toFun := code.rowMate H K C
  invFun := code.rowMate H K C
  left_inv := code.rowMate_rowMate H K C
  right_inv := code.rowMate_rowMate H K C

/-- Column mate as an involutive permutation. -/
noncomputable def MuThreeMixedGridCode.columnMateEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridNonHCell H K ≃ mixedGridNonHCell H K where
  toFun := code.columnMate H K C
  invFun := code.columnMate H K C
  left_inv := code.columnMate_columnMate H K C
  right_inv := code.columnMate_columnMate H K C

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.rowMate_adj
#print axioms Erdos85.MuThreeMixedGridCode.columnMate_adj
#print axioms Erdos85.MuThreeMixedGridCode.rowMate_rowMate
#print axioms Erdos85.MuThreeMixedGridCode.columnMate_columnMate
#print axioms Erdos85.MuThreeMixedGridCode.rowMate_ne_columnMate
#print axioms
  Erdos85.MuThreeMixedGridCode.rowMate_columnMate_ne_columnMate_rowMate
#print axioms Erdos85.MuThreeMixedGridCode.card_nonHCell_eq_thirtyTwo
#print axioms Erdos85.MuThreeMixedGridCode.rowMateEquiv
#print axioms Erdos85.MuThreeMixedGridCode.columnMateEquiv
