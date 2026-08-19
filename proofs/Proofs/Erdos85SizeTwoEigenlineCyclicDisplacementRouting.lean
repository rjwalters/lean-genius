import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementCollisionMarginals

/-!
# Pointwise routing in the cyclic displacement grid

Tensor marginals forget which source base uses which target.  The hit laws
are stronger: for every individual source cell, each admissible target row
and column contains a unique neighbor.  These unique routing statements are
the partial-permutation interface needed for a pointwise C4 argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem existsUnique_of_univ_filter_card_one
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Y → Prop) [DecidablePred P]
    (hcard : ((Finset.univ : Finset Y).filter P).card = 1) :
    ∃! y, P y := by
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
  have hyP : P y := by
    have : y ∈ (Finset.univ : Finset Y).filter P := by rw [hy]; simp
    exact (Finset.mem_filter.mp this).2
  refine ⟨y, hyP, ?_⟩
  intro z hzP
  have hz : z ∈ (Finset.univ : Finset Y).filter P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzP⟩
  rw [hy] at hz
  simpa using hz

/-- Every admissible relative target row has a unique target difference. -/
theorem sizeTwoCyclic_existsUnique_targetDifference_in_row
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (r : ZMod q)
    (hr : t.1 ≠ r ∧ t.1 ≠ r - 1) :
    ∃! s : sizeTwoAllowedDifference q a,
      C.Adj (sizeTwoCyclicCellAt q a x t)
        (sizeTwoCyclicCellAt q a (x + r) s) := by
  letI : DecidableEq (sizeTwoAllowedDifference q a) := Classical.decEq _
  apply existsUnique_of_univ_filter_card_one
  have h := sizeTwoCyclic_row_hit_difference_card q a C hrow_hit
    (sizeTwoCyclicCellAt q a x t) (x + r)
  have hbad : ¬(x + t.1 = x + r ∨ x + t.1 = x + r - 1) := by
    push Not
    constructor
    · intro heq
      exact hr.1 (add_left_cancel heq)
    · intro heq
      apply hr.2
      apply add_left_cancel (a := x)
      simpa [sub_eq_add_neg, add_assoc] using heq
  rw [sizeTwoCyclicCellAt_snd] at h
  rw [if_neg hbad] at h
  simpa using h

/-- Every admissible relative target column has a unique target difference;
the target row displacement is then `c-s`. -/
theorem sizeTwoCyclic_existsUnique_targetDifference_in_column
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (c : ZMod q)
    (hc : c ≠ 0 ∧ c ≠ -1) :
    ∃! s : sizeTwoAllowedDifference q a,
      C.Adj (sizeTwoCyclicCellAt q a x t)
        (sizeTwoCyclicCellAt q a ((x + c) - s.1) s) := by
  letI : DecidableEq (sizeTwoAllowedDifference q a) := Classical.decEq _
  apply existsUnique_of_univ_filter_card_one
  have h := sizeTwoCyclic_column_hit_difference_card q a C hcol_hit
    (sizeTwoCyclicCellAt q a x t) (x + c)
  have hbad : ¬(x = x + c ∨ x = x + c + 1) := by
    push Not
    constructor
    · intro heq
      apply hc.1
      have := congrArg (fun z : ZMod q => z - x) heq
      simpa [sub_eq_add_neg, add_assoc] using this.symm
    · intro heq
      apply hc.2
      have hz : c + 1 = 0 := by
        apply add_left_cancel (a := x)
        simpa [add_assoc] using heq.symm
      have hz' := congrArg (fun z : ZMod q => z - 1) hz
      simpa [sub_eq_add_neg, add_assoc] using hz'
  rw [sizeTwoCyclicCellAt_fst] at h
  rw [if_neg hbad] at h
  simpa using h

/-- Pointwise row/column routing retained from both hit laws. -/
structure SizeTwoCyclicRoutingConstraints
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) : Prop where
  row : ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a) (r : ZMod q),
    t.1 ≠ r ∧ t.1 ≠ r - 1 →
      ∃! s : sizeTwoAllowedDifference q a,
        C.Adj (sizeTwoCyclicCellAt q a x t)
          (sizeTwoCyclicCellAt q a (x + r) s)
  column : ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a) (c : ZMod q),
    c ≠ 0 ∧ c ≠ -1 →
      ∃! s : sizeTwoAllowedDifference q a,
        C.Adj (sizeTwoCyclicCellAt q a x t)
          (sizeTwoCyclicCellAt q a ((x + c) - s.1) s)

theorem sizeTwoCyclicRoutingConstraints_of_hits
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    SizeTwoCyclicRoutingConstraints q a C where
  row := fun x t r hr =>
    sizeTwoCyclic_existsUnique_targetDifference_in_row q a C hrow_hit x t r hr
  column := fun x t c hc =>
    sizeTwoCyclic_existsUnique_targetDifference_in_column q a C hcol_hit x t c hc

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclic_existsUnique_targetDifference_in_row
#print axioms Erdos85.sizeTwoCyclic_existsUnique_targetDifference_in_column
#print axioms Erdos85.sizeTwoCyclicRoutingConstraints_of_hits
