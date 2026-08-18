import Proofs.Erdos85MuThreeMixedGridSquareDegrees

/-!
# Per-cell row ledger in the mixed μ=3 grid

For a cell `u` and a different target row, the six occupied cells in that
row split into residual (`D`), common-neighbour (`Q`), and rook mates.  The
rook contribution is the indicator that the cell in `u`'s column is occupied.
-/

open SimpleGraph

namespace Erdos85

def mixedGridGraphMatesInRow
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (F : SimpleGraph (muThreeMixedCell K)) [DecidableRel F.Adj]
    (u : muThreeMixedCell K) (x : X) : Finset (muThreeMixedCell K) :=
  (F.neighborFinset u).filter fun v => v.1.1 = x

/-- In a foreign row the square-partition relations split all six occupied
cells exactly. -/
theorem MuThreeMixedGridCode.rowLedger_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow (mixedGridSquareResidualGraph K C) u x).card +
      (mixedGridGraphMatesInRow (mixedGridCommonNeighborGraph K C) u x).card +
      (mixedGridGraphMatesInRow (mixedGridRowColumnGraph K) u x).card = 6 := by
  let D := mixedGridGraphMatesInRow (mixedGridSquareResidualGraph K C) u x
  let Q := mixedGridGraphMatesInRow (mixedGridCommonNeighborGraph K C) u x
  let R := mixedGridGraphMatesInRow (mixedGridRowColumnGraph K) u x
  let S := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun v => v.1.1 = x
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
    have hd := ((mixedGridSquareResidualGraph K C).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvD).1
    have hr := ((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvR).1
    exact hd.2.1 hr
  have hQR : Disjoint Q R := by
    rw [Finset.disjoint_left]
    intro v hvQ hvR
    have hq := ((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvQ).1
    change u ≠ v ∧ (C.neighborFinset u ∩ C.neighborFinset v).card = 1 at hq
    have hr := ((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp
      (Finset.mem_filter.mp hvR).1
    have hzero := code.rowColumn_common_neighbor_card_eq_zero H K C hr
    rw [hzero] at hq
    exact Nat.zero_ne_one hq.2
  have hcover : D ∪ Q ∪ R = S := by
    ext v
    simp only [Finset.mem_union, D, Q, R, S, mixedGridGraphMatesInRow,
      Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
    constructor
    · intro hv
      rcases hv with (hd | hq) | hr
      · exact hd.2
      · exact hq.2
      · exact hr.2
    · intro hvrow
      have huv : u ≠ v := by
        intro huv
        subst v
        exact hxu hvrow.symm
      have hpartition := code.square_partition_sup_eq_top H K C
      have hadj := iff_of_eq (congrArg
        (fun G : SimpleGraph (muThreeMixedCell K) => G.Adj u v) hpartition)
      simp only [sup_adj, top_adj] at hadj
      rcases hadj.mpr huv with (hq | hd) | hr
      · exact Or.inl (Or.inr ⟨hq, hvrow⟩)
      · exact Or.inl (Or.inl ⟨hd, hvrow⟩)
      · exact Or.inr ⟨hr, hvrow⟩
  have hcardS : S.card = 6 := code.occupied_row_card_eq_six H K C x
  have hdisjointDQ_R : Disjoint (D ∪ Q) R :=
    Finset.disjoint_union_left.mpr ⟨hDR, hQR⟩
  change D.card + Q.card + R.card = 6
  rw [← hcardS, ← hcover, Finset.card_union_of_disjoint hdisjointDQ_R,
    Finset.card_union_of_disjoint hDQ]

/-- The rook contribution in a different row is exactly the occupied-cell
indicator at `(x,u.column)`. -/
theorem MuThreeMixedGridCode.rookMatesInRow_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow (mixedGridRowColumnGraph K) u x).card =
      if K x u.1.2 then 0 else 1 := by
  by_cases hK : K x u.1.2
  · have hempty :
        mixedGridGraphMatesInRow (mixedGridRowColumnGraph K) u x = ∅ := by
      ext v
      constructor
      · intro hv
        have hv' := Finset.mem_filter.mp hv
        have hadj := ((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp hv'.1
        rcases hadj.2 with hrow | hcol
        · exact (hxu (hv'.2.symm.trans hrow.symm)).elim
        · exact (v.2 (by simpa [hv'.2, hcol] using hK)).elim
      · simp
    simp [hK, hempty]
  · let v : muThreeMixedCell K := ⟨(x, u.1.2), hK⟩
    have hsingleton :
        mixedGridGraphMatesInRow (mixedGridRowColumnGraph K) u x = {v} := by
      ext w
      constructor
      · intro hw
        have hw' := Finset.mem_filter.mp hw
        have hadj := ((mixedGridRowColumnGraph K).mem_neighborFinset u w).mp hw'.1
        apply Finset.mem_singleton.mpr
        apply Subtype.ext
        apply Prod.ext
        · exact hw'.2
        · rcases hadj.2 with hrow | hcol
          · exact (hxu (hw'.2.symm.trans hrow.symm)).elim
          · exact hcol.symm
      · intro hw
        have hwv := Finset.mem_singleton.mp hw
        subst w
        apply Finset.mem_filter.mpr
        refine ⟨((mixedGridRowColumnGraph K).mem_neighborFinset u v).mpr ?_, rfl⟩
        exact ⟨by
          intro huv
          apply hxu
          exact (by simpa [v] using
            (congrArg (fun z : muThreeMixedCell K => z.1.1) huv).symm),
          Or.inr rfl⟩
    simp [hK, hsingleton]

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.rowLedger_card
#print axioms Erdos85.MuThreeMixedGridCode.rookMatesInRow_card
