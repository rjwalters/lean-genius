import Proofs.Erdos85SizeTwoEigenlineCyclicOrbitSecondMoment

/-!
# Displacement-resolved cyclic orbit incidence

The orbit matrix sums away one essential coordinate.  Here an exterior edge
from `(x,x+t)` to `(y,y+s)` is also indexed by its cyclic displacement
`r = y-x`.  The resulting tensor retains the exact row-routing information
while making no translation-invariance assumption on the unknown graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Edges from difference `t` to difference `s` at fixed base displacement
`r`; the subtype records the source base point. -/
def sizeTwoDisplacementEdgeFiber
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) (r : ZMod q) :=
  {x : ZMod q // C.Adj (sizeTwoCyclicCellAt q a x t)
    (sizeTwoCyclicCellAt q a (x + r) s)}

noncomputable instance (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t s : sizeTwoAllowedDifference q a) (r : ZMod q) :
    Fintype (sizeTwoDisplacementEdgeFiber q a C t s r) :=
  Subtype.fintype _

/-- The displacement-resolved orbit incidence tensor. -/
def sizeTwoDisplacementEdgeCount
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t s : sizeTwoAllowedDifference q a) (r : ZMod q) : ℕ :=
  Fintype.card (sizeTwoDisplacementEdgeFiber q a C t s r)

/-- Reversing an edge negates its displacement and swaps its difference
labels. -/
def sizeTwoDisplacementEdgeFiberReverse
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) (r : ZMod q) :
    sizeTwoDisplacementEdgeFiber q a C t s r ≃
      sizeTwoDisplacementEdgeFiber q a C s t (-r) where
  toFun x := ⟨x.1 + r, by
    simpa [add_assoc] using C.adj_symm x.2⟩
  invFun y := ⟨y.1 - r, by
    have h := C.adj_symm y.2
    simpa [sub_eq_add_neg, add_assoc] using h⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- Tensor reversal symmetry, valid without cyclic symmetry of `C`. -/
theorem sizeTwoDisplacementEdgeCount_reverse
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t s : sizeTwoAllowedDifference q a) (r : ZMod q) :
    sizeTwoDisplacementEdgeCount q a C t s r =
      sizeTwoDisplacementEdgeCount q a C s t (-r) := by
  exact Fintype.card_congr
    (sizeTwoDisplacementEdgeFiberReverse q a C t s r)

/-- Splitting an orbit-pair edge by `r = y-x` is exact. -/
def sizeTwoDifferenceEdgeFiberDisplacementEquiv
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) :
    sizeTwoDifferenceEdgeFiber q a C t s ≃
      (Σ r : ZMod q, sizeTwoDisplacementEdgeFiber q a C t s r) where
  toFun p := ⟨p.1.2 - p.1.1, ⟨p.1.1, by
    simpa using p.2⟩⟩
  invFun p := ⟨(p.2.1, p.2.1 + p.1), p.2.2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv p := by
    rcases p with ⟨r, ⟨x, h⟩⟩
    apply Sigma.subtype_ext
    · simp
    · rfl

/-- Summing the displacement coordinate recovers the orbit-incidence matrix. -/
theorem sizeTwoDisplacementEdgeCount_sum
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t s : sizeTwoAllowedDifference q a) :
    (∑ r : ZMod q, sizeTwoDisplacementEdgeCount q a C t s r) =
      sizeTwoDifferenceEdgeCount q a C t s := by
  rw [sizeTwoDifferenceEdgeCount]
  rw [Fintype.card_congr
    (sizeTwoDifferenceEdgeFiberDisplacementEquiv q a C t s),
    Fintype.card_sigma]
  rfl

@[simp] theorem sizeTwoCyclicExteriorCellEquiv_cellAt
    (q : ℕ) (a : ZMod q) (x : ZMod q)
    (t : sizeTwoAllowedDifference q a) :
    sizeTwoCyclicExteriorCellEquiv q a (sizeTwoCyclicCellAt q a x t) =
      (x, t) := by
  simp [sizeTwoCyclicCellAt]

@[simp] theorem sizeTwoCyclicCellAt_fst
    (q : ℕ) (a : ZMod q) (x : ZMod q)
    (t : sizeTwoAllowedDifference q a) :
    (sizeTwoCyclicCellAt q a x t).1.1 = x := by
  change (sizeTwoCyclicExteriorCellEquiv q a
    (sizeTwoCyclicCellAt q a x t)).1 = x
  simp

@[simp] theorem sizeTwoCyclicCellAt_snd
    (q : ℕ) (a : ZMod q) (x : ZMod q)
    (t : sizeTwoAllowedDifference q a) :
    (sizeTwoCyclicCellAt q a x t).1.2 = x + t.1 := by
  simp [sizeTwoCyclicCellAt, sizeTwoCyclicExteriorCellEquiv]

/-- Reparametrization of the exterior cells in one fixed row by their allowed
difference labels. -/
def sizeTwoCyclicRowEquiv
    (q : ℕ) (a : ZMod q) (y : ZMod q) :
    sizeTwoAllowedDifference q a ≃
      {v : sizeTwoCyclicExteriorCell q a // v.1.1 = y} where
  toFun s := ⟨sizeTwoCyclicCellAt q a y s, by
    change (sizeTwoCyclicExteriorCellEquiv q a
      (sizeTwoCyclicCellAt q a y s)).1 = y
    simp [sizeTwoCyclicCellAt]⟩
  invFun v := (sizeTwoCyclicExteriorCellEquiv q a v.1).2
  left_inv s := by
    apply Subtype.ext
    simp [sizeTwoCyclicCellAt]
  right_inv v := by
    apply Subtype.ext
    have hbase : (sizeTwoCyclicExteriorCellEquiv q a v.1).1 = y := by
      change v.1.1.1 = y
      exact v.2
    apply (sizeTwoCyclicExteriorCellEquiv q a).injective
    apply Prod.ext
    · exact hbase.symm
    · simp [sizeTwoCyclicCellAt]

/-- The row-hit law in difference coordinates: at target row `y`, summing
over all allowed target differences counts the same cells as the original
row fiber. -/
theorem sizeTwoCyclic_row_hit_difference_card
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q) :
    ((Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter fun s =>
      C.Adj u (sizeTwoCyclicCellAt q a y s)).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1 := by
  rw [← hrow_hit u y]
  apply Finset.card_bij
    (fun s _ => sizeTwoCyclicCellAt q a y s)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨(C.mem_neighborFinset _ _).mpr hs.2,
      by
        change (sizeTwoCyclicExteriorCellEquiv q a
          (sizeTwoCyclicCellAt q a y s)).1 = y
        simp [sizeTwoCyclicCellAt]⟩
  · intro s₁ _ s₂ _ h
    apply (sizeTwoCyclicRowEquiv q a y).injective
    apply Subtype.ext
    exact h
  · intro v hv
    rw [Finset.mem_filter] at hv
    let s := (sizeTwoCyclicExteriorCellEquiv q a v).2
    have hbase : (sizeTwoCyclicExteriorCellEquiv q a v).1 = y := by
      change v.1.1 = y
      exact hv.2
    have hcoord : sizeTwoCyclicExteriorCellEquiv q a v = (y, s) := by
      apply Prod.ext
      · exact hbase
      · rfl
    refine ⟨s, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [show sizeTwoCyclicCellAt q a y s = v by
        unfold sizeTwoCyclicCellAt
        rw [← hcoord]
        simp]
      exact (C.mem_neighborFinset _ _).mp hv.1
    · unfold sizeTwoCyclicCellAt
      rw [← hcoord]
      simp

/-- Exact displacement-slice totals forced by the row-hit law.  The condition
is written in the form appearing directly after substituting
`u=(x,x+t)` and target row `x+r`. -/
theorem sizeTwoDisplacementEdgeCount_sum_targetDifference
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (t : sizeTwoAllowedDifference q a) (r : ZMod q) :
    (∑ s : sizeTwoAllowedDifference q a,
      sizeTwoDisplacementEdgeCount q a C t s r) =
        if (t.1 = r ∨ t.1 = r - 1) then 0 else q := by
  calc
    _ = ∑ s : sizeTwoAllowedDifference q a, ∑ x : ZMod q,
        if C.Adj (sizeTwoCyclicCellAt q a x t)
          (sizeTwoCyclicCellAt q a (x + r) s) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      unfold sizeTwoDisplacementEdgeCount sizeTwoDisplacementEdgeFiber
      rw [Fintype.card_subtype, Finset.card_filter]
    _ = ∑ x : ZMod q, ∑ s : sizeTwoAllowedDifference q a,
        if C.Adj (sizeTwoCyclicCellAt q a x t)
          (sizeTwoCyclicCellAt q a (x + r) s) then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _x : ZMod q, if (t.1 = r ∨ t.1 = r - 1) then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro x _
      have h := sizeTwoCyclic_row_hit_difference_card q a C hrow_hit
        (sizeTwoCyclicCellAt q a x t) (x + r)
      rw [Finset.card_filter] at h
      simpa [sub_eq_add_neg, add_assoc] using h
    _ = _ := by
      by_cases h : t.1 = r ∨ t.1 = r - 1 <;> simp [h, ZMod.card]

end

end Erdos85

#print axioms Erdos85.sizeTwoDisplacementEdgeCount_reverse
#print axioms Erdos85.sizeTwoDisplacementEdgeCount_sum
#print axioms Erdos85.sizeTwoCyclic_row_hit_difference_card
#print axioms Erdos85.sizeTwoDisplacementEdgeCount_sum_targetDifference
