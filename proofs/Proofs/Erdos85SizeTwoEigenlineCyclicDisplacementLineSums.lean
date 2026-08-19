import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementCollision

/-!
# Row and column line sums of the displacement tensor

Row hits give horizontal tensor slices.  Column hits give diagonal slices,
because the target column of `(x+r, x+r+s)` is `x+(r+s)`.  Keeping both
families is the exact transportation interface for the cyclic quotient.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Reparametrization of the exterior cells in one fixed column by their
allowed difference labels. -/
def sizeTwoCyclicColumnEquiv
    (q : ℕ) (a : ZMod q) (z : ZMod q) :
    sizeTwoAllowedDifference q a ≃
      {v : sizeTwoCyclicExteriorCell q a // v.1.2 = z} where
  toFun s := ⟨sizeTwoCyclicCellAt q a (z - s.1) s, by
    simp [sub_eq_add_neg, add_assoc]⟩
  invFun v := (sizeTwoCyclicExteriorCellEquiv q a v.1).2
  left_inv s := by
    apply Subtype.ext
    simp [sizeTwoCyclicCellAt]
  right_inv v := by
    apply Subtype.ext
    apply (sizeTwoCyclicExteriorCellEquiv q a).injective
    apply Prod.ext
    · have hz : (sizeTwoCyclicExteriorCellEquiv q a v.1).1 +
          (sizeTwoCyclicExteriorCellEquiv q a v.1).2.1 = z := by
        change v.1.1.1 + (v.1.1.2 - v.1.1.1) = z
        simpa using v.2
      simp only [sizeTwoCyclicExteriorCellEquiv_cellAt]
      exact (sub_eq_iff_eq_add).2 hz.symm
    · simp [sizeTwoCyclicCellAt]

/-- The column-hit law expressed using allowed target differences. -/
theorem sizeTwoCyclic_column_hit_difference_card
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q) :
    ((Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter fun s =>
      C.Adj u (sizeTwoCyclicCellAt q a (z - s.1) s)).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1 := by
  rw [← hcol_hit u z]
  apply Finset.card_bij
    (fun s _ => sizeTwoCyclicCellAt q a (z - s.1) s)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨(C.mem_neighborFinset _ _).mpr hs.2, by
      simp [sub_eq_add_neg, add_assoc]⟩
  · intro s₁ _ s₂ _ h
    apply (sizeTwoCyclicColumnEquiv q a z).injective
    apply Subtype.ext
    exact h
  · intro v hv
    rw [Finset.mem_filter] at hv
    let s := (sizeTwoCyclicExteriorCellEquiv q a v).2
    have hz : (sizeTwoCyclicExteriorCellEquiv q a v).1 + s.1 = z := by
      change v.1.1 + (v.1.2 - v.1.1) = z
      simpa using hv.2
    have hcell : sizeTwoCyclicCellAt q a (z - s.1) s = v := by
      apply (sizeTwoCyclicExteriorCellEquiv q a).injective
      apply Prod.ext
      · simp only [sizeTwoCyclicExteriorCellEquiv_cellAt]
        exact (sub_eq_iff_eq_add).2 hz.symm
      · simp [sizeTwoCyclicCellAt, s]
    refine ⟨s, ?_, hcell⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcell ▸ (C.mem_neighborFinset _ _).mp hv.1⟩

/-- Exact diagonal displacement slices forced by the column-hit law. -/
theorem sizeTwoDisplacementEdgeCount_sum_targetColumn
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (t : sizeTwoAllowedDifference q a) (c : ZMod q) :
    (∑ s : sizeTwoAllowedDifference q a,
      sizeTwoDisplacementEdgeCount q a C t s (c - s.1)) =
        if (c = 0 ∨ c = -1) then 0 else q := by
  calc
    _ = ∑ s : sizeTwoAllowedDifference q a, ∑ x : ZMod q,
        if C.Adj (sizeTwoCyclicCellAt q a x t)
          (sizeTwoCyclicCellAt q a (x + (c - s.1)) s) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      unfold sizeTwoDisplacementEdgeCount sizeTwoDisplacementEdgeFiber
      rw [Fintype.card_subtype, Finset.card_filter]
    _ = ∑ x : ZMod q, ∑ s : sizeTwoAllowedDifference q a,
        if C.Adj (sizeTwoCyclicCellAt q a x t)
          (sizeTwoCyclicCellAt q a ((x + c) - s.1) s) then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro s _
      congr 3
      abel
    _ = ∑ _x : ZMod q, if (c = 0 ∨ c = -1) then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro x _
      have h := sizeTwoCyclic_column_hit_difference_card q a C hcol_hit
        (sizeTwoCyclicCellAt q a x t) (x + c)
      rw [Finset.card_filter] at h
      have hc : c + 1 = 0 ↔ c = -1 := by
        constructor
        · intro hc
          have hc' := congrArg (fun z : ZMod q => z - 1) hc
          simpa [sub_eq_add_neg, add_assoc] using hc'
        · intro hc
          rw [hc]
          simp
      simpa [add_assoc, hc] using h
    _ = _ := by
      by_cases h : c = 0 ∨ c = -1 <;> simp [h, ZMod.card]

/-- The two exact line-sum families required of a displacement tensor. -/
structure SizeTwoDisplacementLineSumConstraints
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj] : Prop where
  row : ∀ (t : sizeTwoAllowedDifference q a) (r : ZMod q),
    (∑ s, sizeTwoDisplacementEdgeCount q a C t s r) =
      if t.1 = r ∨ t.1 = r - 1 then 0 else q
  column : ∀ (t : sizeTwoAllowedDifference q a) (c : ZMod q),
    (∑ s, sizeTwoDisplacementEdgeCount q a C t s (c - s.1)) =
      if c = 0 ∨ c = -1 then 0 else q

theorem sizeTwoDisplacementLineSumConstraints_of_hits
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    SizeTwoDisplacementLineSumConstraints q a C where
  row := sizeTwoDisplacementEdgeCount_sum_targetDifference q a C hrow_hit
  column := sizeTwoDisplacementEdgeCount_sum_targetColumn q a C hcol_hit

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclic_column_hit_difference_card
#print axioms Erdos85.sizeTwoDisplacementEdgeCount_sum_targetColumn
#print axioms Erdos85.sizeTwoDisplacementLineSumConstraints_of_hits
