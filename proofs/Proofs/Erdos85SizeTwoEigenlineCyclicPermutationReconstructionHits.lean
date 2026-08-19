import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReconstruction

/-!
# Hit laws for the graph reconstructed from a cyclic permutation code

The permutation attached to a source cell chooses exactly one target
difference in every admissible target row.  This file translates that
tautological code-level fact back into the graph-level row-hit law.
-/

namespace Erdos85

noncomputable section

theorem sizeTwoCyclicCodeRouteRel_cellAt_iff
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (v : sizeTwoCyclicExteriorCell q a) :
    sizeTwoCyclicCodeRouteRel q a code
        (sizeTwoCyclicCellAt q a x t) v ↔
      ∃ r : SizeTwoAdmissibleTargetRow q t.1,
        v = sizeTwoCyclicCellAt q a (x + r.1)
          (code.targetDifference x t r) := by
  unfold sizeTwoCyclicCodeRouteRel
  rw [sizeTwoCyclicExteriorCellEquiv_cellAt]

theorem sizeTwoCyclicCodeGraph_adj_cellAt_iff
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (v : sizeTwoCyclicExteriorCell q a) :
    (sizeTwoCyclicCodeGraph q a code).Adj
        (sizeTwoCyclicCellAt q a x t) v ↔
      ∃ r : SizeTwoAdmissibleTargetRow q t.1,
        v = sizeTwoCyclicCellAt q a (x + r.1)
          (code.targetDifference x t r) := by
  rw [sizeTwoCyclicCodeGraph_adj_iff q a code hloop]
  exact sizeTwoCyclicCodeRouteRel_cellAt_iff q a code x t v

/-- Every admissible absolute target row contains exactly one neighbor of a
source cell in the reconstructed graph. -/
theorem sizeTwoCyclicCodeGraph_existsUnique_neighbor_in_admissible_row
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (x y : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hy : t.1 ≠ y - x ∧ t.1 ≠ (y - x) - 1) :
    ∃! v : sizeTwoCyclicExteriorCell q a,
      (sizeTwoCyclicCodeGraph q a code).Adj
          (sizeTwoCyclicCellAt q a x t) v ∧ v.1.1 = y := by
  let r : SizeTwoAdmissibleTargetRow q t.1 := ⟨y - x, hy⟩
  let v := sizeTwoCyclicCellAt q a (x + r.1)
    (code.targetDifference x t r)
  refine ⟨v, ?_, ?_⟩
  · constructor
    · rw [sizeTwoCyclicCodeGraph_adj_cellAt_iff q a code hloop]
      exact ⟨r, rfl⟩
    · simp [v, r]
  · intro w hw
    rw [sizeTwoCyclicCodeGraph_adj_cellAt_iff q a code hloop] at hw
    obtain ⟨⟨r', hr'⟩, rfl⟩ := hw.1
    have hrow : x + r' = y := by
      simpa using hw.2
    have hrr : r' = y - x := by
      have := congrArg (fun z : ZMod q => z - x) hrow
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    have hre : (⟨r', hr'⟩ : SizeTwoAdmissibleTargetRow q t.1) = r := by
      apply Subtype.ext
      exact hrr
    rw [hre]

/-- Cardinal form of the row-hit law for a source in cyclic coordinates. -/
theorem sizeTwoCyclicCodeGraph_row_hit_cellAt
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    [DecidableRel (sizeTwoCyclicCodeGraph q a code).Adj]
    (x y : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (((sizeTwoCyclicCodeGraph q a code).neighborFinset
        (sizeTwoCyclicCellAt q a x t)).filter fun v => v.1.1 = y).card =
      if t.1 = y - x ∨ t.1 = (y - x) - 1 then 0 else 1 := by
  by_cases hbad : t.1 = y - x ∨ t.1 = (y - x) - 1
  · rw [if_pos hbad, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hadj : (sizeTwoCyclicCodeGraph q a code).Adj
        (sizeTwoCyclicCellAt q a x t) w := by
      simpa using (Finset.mem_filter.mp hw).1
    have hrow : w.1.1 = y := (Finset.mem_filter.mp hw).2
    rw [sizeTwoCyclicCodeGraph_adj_cellAt_iff q a code hloop] at hadj
    obtain ⟨r, rfl⟩ := hadj
    have hr : r.1 = y - x := by
      have hxy : x + r.1 = y := by simpa using hrow
      have := congrArg (fun z : ZMod q => z - x) hxy
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    rcases hbad with hbad | hbad
    · exact r.2.1 (hbad.trans hr.symm)
    · exact r.2.2 (hbad.trans
        (congrArg (fun z : ZMod q => z - 1) hr).symm)
  · rw [if_neg hbad, Finset.card_eq_one]
    have hy : t.1 ≠ y - x ∧ t.1 ≠ (y - x) - 1 := not_or.mp hbad
    obtain ⟨v, hv, huniq⟩ :=
      sizeTwoCyclicCodeGraph_existsUnique_neighbor_in_admissible_row
        q a code hloop x y t hy
    refine ⟨v, Finset.ext ?_⟩
    intro w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_singleton]
    constructor
    · exact huniq w
    · rintro rfl
      exact hv

/-- The reconstructed graph satisfies the normalized row-hit law in the
coordinate-free form consumed by the cyclic grid pipeline. -/
theorem sizeTwoCyclicCodeGraph_row_hit
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    [DecidableRel (sizeTwoCyclicCodeGraph q a code).Adj]
    (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q) :
    (((sizeTwoCyclicCodeGraph q a code).neighborFinset u).filter
        fun v => v.1.1 = y).card =
      if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1 := by
  let z := sizeTwoCyclicExteriorCellEquiv q a u
  have hu : u = sizeTwoCyclicCellAt q a z.1 z.2 := by
    apply (sizeTwoCyclicExteriorCellEquiv q a).injective
    simp [z]
  rw [hu, sizeTwoCyclicCodeGraph_row_hit_cellAt q a code hloop]
  have hiff :
      (z.2.1 = y - z.1 ∨ z.2.1 = (y - z.1) - 1) ↔
        (z.1 + z.2.1 = y ∨ z.1 + z.2.1 = y - 1) := by
    constructor
    · rintro (h | h)
      · left
        rw [h]
        abel
      · right
        rw [h]
        abel
    · rintro (h | h)
      · left
        calc
          z.2.1 = (z.1 + z.2.1) - z.1 := by abel
          _ = y - z.1 := by rw [h]
      · right
        calc
          z.2.1 = (z.1 + z.2.1) - z.1 := by abel
          _ = (y - 1) - z.1 := by rw [h]
          _ = (y - z.1) - 1 := by abel
  simp only [sizeTwoCyclicCellAt_snd]
  rw [if_congr hiff rfl rfl]

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicCodeRouteRel_cellAt_iff
#print axioms Erdos85.sizeTwoCyclicCodeGraph_adj_cellAt_iff
#print axioms Erdos85.sizeTwoCyclicCodeGraph_existsUnique_neighbor_in_admissible_row
#print axioms Erdos85.sizeTwoCyclicCodeGraph_row_hit_cellAt
#print axioms Erdos85.sizeTwoCyclicCodeGraph_row_hit
