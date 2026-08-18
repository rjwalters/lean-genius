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

def mixedGridEligibleIntermediateNeighborsForColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (u : muThreeMixedCell K) (y : Y) : Finset (muThreeMixedCell K) :=
  (C.neighborFinset u).filter fun m => ¬ H m.1.1 y

theorem MuThreeMixedGridCode.eligibleIntermediateNeighborsForColumn_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) :
    (mixedGridEligibleIntermediateNeighborsForColumn H K C u y).card =
      (mixedGridCommonAllowedRows' H u.1.2 y).card := by
  apply Finset.card_bij (fun m _ => m.1.1)
  · intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hum : C.Adj u m := (C.mem_neighborFinset u m).mp hm'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      mixedGrid_neighbor_row_allowed H K C code u m hum, hm'.2⟩
  · intro m hm n hn hrow
    by_contra hmn
    have hm' := Finset.mem_filter.mp hm
    have hn' := Finset.mem_filter.mp hn
    have hsep := code.rook u m n
      ((C.mem_neighborFinset u m).mp hm'.1)
      ((C.mem_neighborFinset u n).mp hn'.1) hmn
    exact hsep.1 hrow
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    obtain ⟨m, hum, _⟩ :=
      (code.existsUnique_row_neighbor_iff H K C u x).mpr hx'.1
    refine ⟨m, ?_, hum.2⟩
    apply Finset.mem_filter.mpr
    exact ⟨(C.mem_neighborFinset u m).mpr hum.1,
      by simpa [hum.2] using hx'.2⟩

/-- The unique neighbour of `m` in an allowed target column. -/
noncomputable def mixedGridColumnRoute
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (m : muThreeMixedCell K) (y : Y) (hy : ¬ H m.1.1 y) :
    muThreeMixedCell K :=
  Classical.choose
    ((code.existsUnique_column_neighbor_iff H K C m y).mpr hy)

theorem mixedGridColumnRoute_spec
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (m : muThreeMixedCell K) (y : Y) (hy : ¬ H m.1.1 y) :
    C.Adj m (mixedGridColumnRoute H K C code m y hy) ∧
      (mixedGridColumnRoute H K C code m y hy).1.2 = y :=
  (Classical.choose_spec
    ((code.existsUnique_column_neighbor_iff H K C m y).mpr hy)).1

theorem mixedGridColumnRoute_eq_of_adj_of_column
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (m v : muThreeMixedCell K) (y : Y) (hy : ¬ H m.1.1 y)
    (hmv : C.Adj m v) (hvcol : v.1.2 = y) :
    mixedGridColumnRoute H K C code m y hy = v := by
  exact ((Classical.choose_spec
    ((code.existsUnique_column_neighbor_iff H K C m y).mpr hy)).2
      v ⟨hmv, hvcol⟩).symm

noncomputable def mixedGridIntermediateToColumnMate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y)
    (m : {m // m ∈ mixedGridEligibleIntermediateNeighborsForColumn H K C u y}) :
    muThreeMixedCell K :=
  mixedGridColumnRoute H K C code m.1 y (Finset.mem_filter.mp m.2).2

theorem mixedGridIntermediateToColumnMate_spec
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y)
    (m : {m // m ∈ mixedGridEligibleIntermediateNeighborsForColumn H K C u y}) :
    C.Adj m.1 (mixedGridIntermediateToColumnMate H K C code u y m) ∧
      (mixedGridIntermediateToColumnMate H K C code u y m).1.2 = y :=
  mixedGridColumnRoute_spec H K C code m.1 y (Finset.mem_filter.mp m.2).2

theorem MuThreeMixedGridCode.commonNeighborMatesInColumn_card_eq_eligible
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hyu : y ≠ u.1.2) :
    (mixedGridGraphMatesInColumn (mixedGridCommonNeighborGraph K C) u y).card =
      (mixedGridEligibleIntermediateNeighborsForColumn H K C u y).card := by
  symm
  apply Finset.card_bij (fun m hm =>
    mixedGridIntermediateToColumnMate H K C code u y ⟨m, hm⟩)
  · intro m hm
    let ms : {m // m ∈ mixedGridEligibleIntermediateNeighborsForColumn H K C u y} :=
      ⟨m, hm⟩
    let v := mixedGridIntermediateToColumnMate H K C code u y ms
    have hum : C.Adj u m := (C.mem_neighborFinset u m).mp
      (Finset.mem_filter.mp hm).1
    have hmv : C.Adj m v :=
      (mixedGridIntermediateToColumnMate_spec H K C code u y ms).1
    have hvcol : v.1.2 = y :=
      (mixedGridIntermediateToColumnMate_spec H K C code u y ms).2
    have huv : u ≠ v := by
      intro huv
      apply hyu
      simpa [huv] using hvcol.symm
    have hmcommon : m ∈ C.neighborFinset u ∩ C.neighborFinset v :=
      Finset.mem_inter.mpr ⟨(C.mem_neighborFinset u m).mpr hum,
        (C.mem_neighborFinset v m).mpr (C.adj_symm hmv)⟩
    have hpos : 0 < (C.neighborFinset u ∩ C.neighborFinset v).card :=
      Finset.card_pos.mpr ⟨m, hmcommon⟩
    have hle := code.common_neighbor_card_le_one H K C u v huv
    have hone : (C.neighborFinset u ∩ C.neighborFinset v).card = 1 := by omega
    exact Finset.mem_filter.mpr
      ⟨((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mpr
        ⟨huv, hone⟩, hvcol⟩
  · intro m hm n hn hmn
    let ms : {m // m ∈ mixedGridEligibleIntermediateNeighborsForColumn H K C u y} :=
      ⟨m, hm⟩
    let ns : {m // m ∈ mixedGridEligibleIntermediateNeighborsForColumn H K C u y} :=
      ⟨n, hn⟩
    let v := mixedGridIntermediateToColumnMate H K C code u y ms
    have hvcol : v.1.2 = y :=
      (mixedGridIntermediateToColumnMate_spec H K C code u y ms).2
    have huv : u ≠ v := by
      intro huv
      apply hyu
      simpa [huv] using hvcol.symm
    have hmcommon : m ∈ C.neighborFinset u ∩ C.neighborFinset v := by
      apply Finset.mem_inter.mpr
      refine ⟨(Finset.mem_filter.mp hm).1, ?_⟩
      exact (C.mem_neighborFinset v m).mpr (C.adj_symm
        (mixedGridIntermediateToColumnMate_spec H K C code u y ms).1)
    have hncommon : n ∈ C.neighborFinset u ∩ C.neighborFinset v := by
      apply Finset.mem_inter.mpr
      refine ⟨(Finset.mem_filter.mp hn).1, ?_⟩
      have hnv := (mixedGridIntermediateToColumnMate_spec H K C code u y ns).1
      have heq : mixedGridIntermediateToColumnMate H K C code u y ns = v := hmn.symm
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
    have hvm : C.Adj v m := (C.mem_neighborFinset v m).mp hm'.2
    have hmEligible : m ∈ mixedGridEligibleIntermediateNeighborsForColumn H K C u y := by
      apply Finset.mem_filter.mpr
      refine ⟨hm'.1, ?_⟩
      have hallowed := mixedGrid_neighbor_row_allowed H K C code v m hvm
      simpa [hv'.2] using hallowed
    refine ⟨m, hmEligible, ?_⟩
    apply mixedGridColumnRoute_eq_of_adj_of_column H K C code
    · exact C.adj_symm hvm
    · exact hv'.2

theorem MuThreeMixedGridCode.commonNeighborMatesInColumn_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hyu : y ≠ u.1.2) :
    (mixedGridGraphMatesInColumn (mixedGridCommonNeighborGraph K C) u y).card =
      4 + (mixedGridHCommonRows H u.1.2 y).card := by
  rw [code.commonNeighborMatesInColumn_card_eq_eligible H K C u y hyu,
    code.eligibleIntermediateNeighborsForColumn_card H K C u y,
    code.commonAllowedRows_card H K C u.1.2 y]

theorem MuThreeMixedGridCode.residualMatesInColumn_add_overlap_add_indicator
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hyu : y ≠ u.1.2) :
    (mixedGridGraphMatesInColumn (mixedGridSquareResidualGraph K C) u y).card +
      (mixedGridHCommonRows H u.1.2 y).card +
      (if K u.1.1 y then 0 else 1) = 2 := by
  have hledger := code.columnLedger_card H K C u y hyu
  have hQ := code.commonNeighborMatesInColumn_card H K C u y hyu
  have hR := code.rookMatesInColumn_card H K C u y hyu
  rw [hQ, hR] at hledger
  omega

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.commonAllowedRows_card
#print axioms Erdos85.MuThreeMixedGridCode.columnLedger_card
#print axioms Erdos85.MuThreeMixedGridCode.rookMatesInColumn_card
#print axioms
  Erdos85.MuThreeMixedGridCode.eligibleIntermediateNeighborsForColumn_card
#print axioms Erdos85.mixedGridIntermediateToColumnMate_spec
#print axioms Erdos85.MuThreeMixedGridCode.commonNeighborMatesInColumn_card
#print axioms
  Erdos85.MuThreeMixedGridCode.residualMatesInColumn_add_overlap_add_indicator
