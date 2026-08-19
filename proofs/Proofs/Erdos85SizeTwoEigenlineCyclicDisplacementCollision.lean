import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementTensor

/-!
# Displacement-resolved common-neighbor collisions

The one-edge displacement tensor retains routing, but C4-freeness is a
two-edge condition.  This file records the corresponding collision tensor:
two translated cells in one difference orbit meet the same target cell.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Source bases whose cells at separation `d` both meet the target at
difference `s` and displacement `r` from the first source base. -/
def sizeTwoDisplacementCollisionFiber
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t : sizeTwoAllowedDifference q a) (d : ZMod q)
    (s : sizeTwoAllowedDifference q a) (r : ZMod q) :=
  {x : ZMod q //
    C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a (x + r) s) ∧
    C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
      (sizeTwoCyclicCellAt q a (x + r) s)}

noncomputable instance (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t : sizeTwoAllowedDifference q a) (d : ZMod q)
    (s : sizeTwoAllowedDifference q a) (r : ZMod q) :
    Fintype (sizeTwoDisplacementCollisionFiber q a C t d s r) :=
  Subtype.fintype _

/-- The displacement-resolved two-source collision tensor. -/
def sizeTwoDisplacementCollisionCount
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t : sizeTwoAllowedDifference q a) (d : ZMod q)
    (s : sizeTwoAllowedDifference q a) (r : ZMod q) : ℕ :=
  Fintype.card (sizeTwoDisplacementCollisionFiber q a C t d s r)

/-- For a fixed source base, `(r,s)` are exact coordinates on all exterior
target cells. -/
def sizeTwoCyclicTargetFromDisplacementEquiv
    (q : ℕ) (a x : ZMod q) :
    (ZMod q × sizeTwoAllowedDifference q a) ≃
      sizeTwoCyclicExteriorCell q a where
  toFun p := sizeTwoCyclicCellAt q a (x + p.1) p.2
  invFun v := ((sizeTwoCyclicExteriorCellEquiv q a v).1 - x,
    (sizeTwoCyclicExteriorCellEquiv q a v).2)
  left_inv p := by
    apply Prod.ext
    · simp
    · simp [sizeTwoCyclicCellAt]
  right_inv v := by
    apply (sizeTwoCyclicExteriorCellEquiv q a).injective
    apply Prod.ext <;> simp [sizeTwoCyclicCellAt]

@[simp] theorem sizeTwoCyclicTargetFromDisplacementEquiv_apply
    (q : ℕ) (a x r : ZMod q) (s : sizeTwoAllowedDifference q a) :
    sizeTwoCyclicTargetFromDisplacementEquiv q a x (r, s) =
      sizeTwoCyclicCellAt q a (x + r) s := by
  rfl

/-- Two distinct translated source cells have at most one common target in a
C4-free graph. -/
theorem sizeTwoTranslated_commonNeighbor_card_le_one
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (t : sizeTwoAllowedDifference q a) (x d : ZMod q) (hd : d ≠ 0) :
    ((Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)).filter fun v =>
      C.Adj (sizeTwoCyclicCellAt q a x t) v ∧
      C.Adj (sizeTwoCyclicCellAt q a (x + d) t) v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro v hv w hw
  rw [Finset.mem_filter] at hv hw
  by_contra hvw
  apply hfree
  have hsrc : sizeTwoCyclicCellAt q a x t ≠
      sizeTwoCyclicCellAt q a (x + d) t := by
    intro heq
    apply hd
    have hx := sizeTwoCyclicCellAt_injective q a t heq
    apply add_left_cancel (a := x)
    simpa using hx
  exact containsC4_of_two_common hsrc hvw
    (C.adj_symm hv.2.1) (C.adj_symm hv.2.2)
    (C.adj_symm hw.2.1) (C.adj_symm hw.2.2)

/-- **Displacement collision bound.**  At every nonzero separation `d`, the
total number of common-target collisions across all `q` translated source
pairs is at most `q`. -/
theorem sizeTwoDisplacementCollisionCount_sum_le
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (t : sizeTwoAllowedDifference q a) (d : ZMod q) (hd : d ≠ 0) :
    (∑ s : sizeTwoAllowedDifference q a, ∑ r : ZMod q,
      sizeTwoDisplacementCollisionCount q a C t d s r) ≤ q := by
  calc
    _ = ∑ r : ZMod q, ∑ s : sizeTwoAllowedDifference q a,
        ∑ x : ZMod q,
          if C.Adj (sizeTwoCyclicCellAt q a x t)
              (sizeTwoCyclicCellAt q a (x + r) s) ∧
            C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
              (sizeTwoCyclicCellAt q a (x + r) s) then 1 else 0 := by
      simp_rw [sizeTwoDisplacementCollisionCount,
        sizeTwoDisplacementCollisionFiber, Fintype.card_subtype,
        Finset.card_filter]
      rw [Finset.sum_comm]
    _ = ∑ r : ZMod q, ∑ x : ZMod q,
        ∑ s : sizeTwoAllowedDifference q a,
          if C.Adj (sizeTwoCyclicCellAt q a x t)
              (sizeTwoCyclicCellAt q a (x + r) s) ∧
            C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
              (sizeTwoCyclicCellAt q a (x + r) s) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ x : ZMod q, ∑ r : ZMod q,
        ∑ s : sizeTwoAllowedDifference q a,
          if C.Adj (sizeTwoCyclicCellAt q a x t)
              (sizeTwoCyclicCellAt q a (x + r) s) ∧
            C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
              (sizeTwoCyclicCellAt q a (x + r) s) then 1 else 0 :=
      Finset.sum_comm
    _ ≤ ∑ _x : ZMod q, 1 := by
      apply Finset.sum_le_sum
      intro x _
      have hx := sizeTwoTranslated_commonNeighbor_card_le_one
        q a C hfree t x d hd
      rw [Finset.card_filter] at hx
      have heq : (∑ r : ZMod q,
          ∑ s : sizeTwoAllowedDifference q a,
            if C.Adj (sizeTwoCyclicCellAt q a x t)
                (sizeTwoCyclicCellAt q a (x + r) s) ∧
              C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
                (sizeTwoCyclicCellAt q a (x + r) s) then 1 else 0) =
          ∑ v : sizeTwoCyclicExteriorCell q a,
            if C.Adj (sizeTwoCyclicCellAt q a x t) v ∧
              C.Adj (sizeTwoCyclicCellAt q a (x + d) t) v
            then 1 else 0 := by
        rw [← Fintype.sum_prod_type']
        apply Fintype.sum_equiv
          (sizeTwoCyclicTargetFromDisplacementEquiv q a x)
        intro p
        rcases p with ⟨r, s⟩
        rfl
      rw [heq]
      exact hx
    _ = q := by simp [ZMod.card]

end

end Erdos85

#print axioms Erdos85.sizeTwoTranslated_commonNeighbor_card_le_one
#print axioms Erdos85.sizeTwoDisplacementCollisionCount_sum_le
