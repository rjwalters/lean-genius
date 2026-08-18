import Proofs.Erdos85MuThreeMixedGridPerCellCommonMates

/-! # Column-dual per-cell ledger in the mixed μ=3 grid -/

open SimpleGraph

namespace Erdos85

noncomputable section

def mixedGridGraphMatesInColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (F : SimpleGraph (muThreeMixedCell K)) [DecidableRel F.Adj]
    (u : muThreeMixedCell K) (y : Y) : Finset (muThreeMixedCell K) :=
  (F.neighborFinset u).filter fun v => v.1.2 = y

def mixedGridHCommonRows
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (H : X → Y → Prop) [DecidableRel H] (y y' : Y) : Finset X :=
  Finset.univ.filter fun x => H x y ∧ H x y'

def mixedGridCommonAllowedRows'
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (H : X → Y → Prop) [DecidableRel H] (y y' : Y) : Finset X :=
  Finset.univ.filter fun x => ¬ H x y ∧ ¬ H x y'

theorem MuThreeMixedGridCode.commonAllowedRows_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y y' : Y) :
    (mixedGridCommonAllowedRows' H y y').card =
      4 + (mixedGridHCommonRows H y y').card := by
  let A := (Finset.univ : Finset X).filter fun x => H x y
  let B := (Finset.univ : Finset X).filter fun x => H x y'
  let T := mixedGridCommonAllowedRows' H y y'
  have hA : A.card = 2 := code.H_twoRegular.2 y
  have hB : B.card = 2 := code.H_twoRegular.2 y'
  have hIE := Finset.card_union_add_card_inter A B
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X)) (p := fun x => x ∈ A ∪ B)
  have hnot : ((Finset.univ : Finset X).filter fun x => ¬ x ∈ A ∪ B) = T := by
    ext x
    simp [A, B, T, mixedGridCommonAllowedRows']
  have hinter : A ∩ B = mixedGridHCommonRows H y y' := by
    ext x
    simp [A, B, mixedGridHCommonRows]
  have hunion : ((Finset.univ : Finset X).filter fun x => x ∈ A ∪ B) = A ∪ B := by
    ext x
    simp
  simp only [Finset.card_univ, code.card_left] at hpartition
  rw [hnot, hunion] at hpartition
  rw [hA, hB, hinter] at hIE
  change T.card = 4 + (mixedGridHCommonRows H y y').card
  omega

/-- The square-partition ledger in a foreign column. -/
theorem MuThreeMixedGridCode.columnLedger_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hyu : y ≠ u.1.2) :
    (mixedGridGraphMatesInColumn (mixedGridSquareResidualGraph K C) u y).card +
      (mixedGridGraphMatesInColumn (mixedGridCommonNeighborGraph K C) u y).card +
      (mixedGridGraphMatesInColumn (mixedGridRowColumnGraph K) u y).card = 6 := by
  let D := mixedGridGraphMatesInColumn (mixedGridSquareResidualGraph K C) u y
  let Q := mixedGridGraphMatesInColumn (mixedGridCommonNeighborGraph K C) u y
  let R := mixedGridGraphMatesInColumn (mixedGridRowColumnGraph K) u y
  let S := (Finset.univ : Finset (muThreeMixedCell K)).filter fun v => v.1.2 = y
  have hDQ : Disjoint D Q := by
    rw [Finset.disjoint_left]
    intro v hvD hvQ
    have hd := ((mixedGridSquareResidualGraph K C).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvD).1
    have hq := ((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvQ).1
    change u ≠ v ∧ (C.neighborFinset u ∩ C.neighborFinset v).card = 1 at hq
    rw [hd.2.2] at hq
    exact Nat.zero_ne_one hq.2
  have hDR : Disjoint D R := by
    rw [Finset.disjoint_left]
    intro v hvD hvR
    exact (((mixedGridSquareResidualGraph K C).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvD).1).2.1
      (((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp
        (Finset.mem_filter.mp hvR).1)
  have hQR : Disjoint Q R := by
    rw [Finset.disjoint_left]
    intro v hvQ hvR
    have hq := ((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvQ).1
    change u ≠ v ∧ (C.neighborFinset u ∩ C.neighborFinset v).card = 1 at hq
    have hr := ((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvR).1
    rw [code.rowColumn_common_neighbor_card_eq_zero H K C hr] at hq
    exact Nat.zero_ne_one hq.2
  have hcover : D ∪ Q ∪ R = S := by
    ext v
    simp only [Finset.mem_union, D, Q, R, S, mixedGridGraphMatesInColumn,
      Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
    constructor
    · intro hv
      rcases hv with (hd | hq) | hr
      · exact hd.2
      · exact hq.2
      · exact hr.2
    · intro hvcol
      have huv : u ≠ v := by
        intro huv
        subst v
        exact hyu hvcol.symm
      have hp := code.square_partition_sup_eq_top H K C
      have hadj := iff_of_eq (congrArg
        (fun G : SimpleGraph (muThreeMixedCell K) => G.Adj u v) hp)
      simp only [sup_adj, top_adj] at hadj
      rcases hadj.mpr huv with (hq | hd) | hr
      · exact Or.inl (Or.inr ⟨hq, hvcol⟩)
      · exact Or.inl (Or.inl ⟨hd, hvcol⟩)
      · exact Or.inr ⟨hr, hvcol⟩
  have hcardS : S.card = 6 := code.occupied_column_card_eq_six H K C y
  have hdisjoint : Disjoint (D ∪ Q) R :=
    Finset.disjoint_union_left.mpr ⟨hDR, hQR⟩
  change D.card + Q.card + R.card = 6
  rw [← hcardS, ← hcover, Finset.card_union_of_disjoint hdisjoint,
    Finset.card_union_of_disjoint hDQ]

theorem MuThreeMixedGridCode.rookMatesInColumn_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (_code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hyu : y ≠ u.1.2) :
    (mixedGridGraphMatesInColumn (mixedGridRowColumnGraph K) u y).card =
      if K u.1.1 y then 0 else 1 := by
  by_cases hK : K u.1.1 y
  · have hempty :
        mixedGridGraphMatesInColumn (mixedGridRowColumnGraph K) u y = ∅ := by
      ext v
      constructor
      · intro hv
        have hv' := Finset.mem_filter.mp hv
        have hadj := ((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp hv'.1
        rcases hadj.2 with hrow | hcol
        · exact (v.2 (by simpa [hrow, hv'.2] using hK)).elim
        · exact (hyu (hv'.2.symm.trans hcol.symm)).elim
      · simp
    simp [hK, hempty]
  · let v : muThreeMixedCell K := ⟨(u.1.1, y), hK⟩
    have hsingleton :
        mixedGridGraphMatesInColumn (mixedGridRowColumnGraph K) u y = {v} := by
      ext w
      constructor
      · intro hw
        have hw' := Finset.mem_filter.mp hw
        have hadj := ((mixedGridRowColumnGraph K).mem_neighborFinset u w).mp hw'.1
        apply Finset.mem_singleton.mpr
        apply Subtype.ext
        apply Prod.ext
        · rcases hadj.2 with hrow | hcol
          · exact hrow.symm
          · exact (hyu (hw'.2.symm.trans hcol.symm)).elim
        · exact hw'.2
      · intro hw
        have hwv := Finset.mem_singleton.mp hw
        subst w
        apply Finset.mem_filter.mpr
        refine ⟨((mixedGridRowColumnGraph K).mem_neighborFinset u v).mpr ?_, rfl⟩
        exact ⟨by
          intro huv
          apply hyu
          exact (by simpa [v] using
            (congrArg (fun z : muThreeMixedCell K => z.1.2) huv).symm),
          Or.inl rfl⟩
    simp [hK, hsingleton]

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.commonAllowedRows_card
#print axioms Erdos85.MuThreeMixedGridCode.columnLedger_card
#print axioms Erdos85.MuThreeMixedGridCode.rookMatesInColumn_card
