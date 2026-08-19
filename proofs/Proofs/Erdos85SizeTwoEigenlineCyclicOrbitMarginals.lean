import Proofs.Erdos85SizeTwoEigenlineCyclicOrbitSecondMoment
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts

/-!
# Row and column marginals of one cyclic difference orbit

The orbit second moment is constrained not only by its total mass.  Both hit
laws force its target multiplicity matrix to have every row and every column
sum equal to `q - 2`.  These are the linear constraints used by the small
exact-grid cores and retained by any uniform packing argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Source bases whose cell in orbit `t` is allowed to hit target row `y`. -/
def sizeTwoOrbitAdmissibleSourceBaseForRow
    (q : ℕ) (t y : ZMod q) :=
  {x : ZMod q // x + t ≠ y ∧ x + t ≠ y - 1}

noncomputable instance (q : ℕ) [NeZero q] (t y : ZMod q) :
    Fintype (sizeTwoOrbitAdmissibleSourceBaseForRow q t y) :=
  Subtype.fintype _

/-- Translation identifies admissible source bases with the standard
two-hole relative-row type. -/
def sizeTwoOrbitAdmissibleSourceBaseForRowEquiv
    (q : ℕ) (t y : ZMod q) :
    sizeTwoOrbitAdmissibleSourceBaseForRow q t y ≃
      SizeTwoAdmissibleTargetRow q t where
  toFun x := ⟨y - x.1, by
    constructor
    · intro h
      apply x.2.1
      calc
        x.1 + t = x.1 + (y - x.1) := congrArg (fun z => x.1 + z) h
        _ = y := by abel
    · intro h
      apply x.2.2
      calc
        x.1 + t = x.1 + ((y - x.1) - 1) :=
          congrArg (fun z => x.1 + z) h
        _ = y - 1 := by abel⟩
  invFun r := ⟨y - r.1, by
    constructor
    · intro h
      apply r.2.1
      calc
        t = -(y - r.1) + ((y - r.1) + t) := by abel
        _ = -(y - r.1) + y := by rw [h]
        _ = r.1 := by abel
    · intro h
      apply r.2.2
      calc
        t = -(y - r.1) + ((y - r.1) + t) := by abel
        _ = -(y - r.1) + (y - 1) := by rw [h]
        _ = r.1 - 1 := by abel⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv r := by
    apply Subtype.ext
    simp

theorem sizeTwoOrbitAdmissibleSourceBaseForRow_card
    (q : ℕ) [NeZero q] (t y : ZMod q) (hq1 : (1 : ZMod q) ≠ 0) :
    Fintype.card (sizeTwoOrbitAdmissibleSourceBaseForRow q t y) = q - 2 := by
  rw [Fintype.card_congr
    (sizeTwoOrbitAdmissibleSourceBaseForRowEquiv q t y)]
  exact sizeTwoAdmissibleTargetRow_card q t hq1

/-- Every absolute target row receives total multiplicity `q - 2` from one
fixed source-difference orbit. -/
theorem sizeTwoOrbitNeighborMultiplicity_row_sum
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hq1 : (1 : ZMod q) ≠ 0)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (t : sizeTwoAllowedDifference q a) (y : ZMod q) :
    (∑ v : sizeTwoCyclicExteriorCell q a,
      if v.1.1 = y then sizeTwoOrbitNeighborMultiplicity q a C t v else 0) =
      q - 2 := by
  classical
  calc
    _ = ∑ v : sizeTwoCyclicExteriorCell q a, ∑ x : ZMod q,
        if v.1.1 = y ∧ C.Adj (sizeTwoCyclicCellAt q a x t) v
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      unfold sizeTwoOrbitNeighborMultiplicity
      rw [Finset.card_filter]
      by_cases hv : v.1.1 = y <;> simp [hv]
    _ = ∑ x : ZMod q, ∑ v : sizeTwoCyclicExteriorCell q a,
        if v.1.1 = y ∧ C.Adj (sizeTwoCyclicCellAt q a x t) v
          then 1 else 0 := Finset.sum_comm
    _ = ∑ x : ZMod q,
        ((C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          fun v => v.1.1 = y).card := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show (C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          (fun v => v.1.1 = y) =
          (Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)).filter
            (fun v => v.1.1 = y ∧
              C.Adj (sizeTwoCyclicCellAt q a x t) v) by
        ext v
        simp [C.mem_neighborFinset, and_comm]]
      rw [Finset.card_filter]
    _ = ∑ x : ZMod q,
        if x + t.1 = y ∨ x + t.1 = y - 1 then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hrow_hit]
      simp [sizeTwoCyclicCellAt_snd]
    _ = Fintype.card (sizeTwoOrbitAdmissibleSourceBaseForRow q t.1 y) := by
      change (∑ x : ZMod q,
          if x + t.1 = y ∨ x + t.1 = y - 1 then 0 else 1) =
        Fintype.card {x : ZMod q //
          x + t.1 ≠ y ∧ x + t.1 ≠ y - 1}
      rw [Fintype.card_subtype]
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x + t.1 = y ∨ x + t.1 = y - 1
      · have hn : ¬(x + t.1 ≠ y ∧ x + t.1 ≠ y - 1) := by
          intro hb
          exact h.elim hb.1 hb.2
        simp [h, hn]
      · have hn : x + t.1 ≠ y ∧ x + t.1 ≠ y - 1 := not_or.mp h
        simp [h, hn]
    _ = q - 2 := sizeTwoOrbitAdmissibleSourceBaseForRow_card q t.1 y hq1

/-- Source bases whose cell in any fixed orbit is allowed to hit target
column `z`.  Unlike the row predicate, this does not depend on the orbit
difference. -/
def sizeTwoOrbitAdmissibleSourceBaseForColumn
    (q : ℕ) (z : ZMod q) :=
  {x : ZMod q // x ≠ z ∧ x ≠ z + 1}

noncomputable instance (q : ℕ) [NeZero q] (z : ZMod q) :
    Fintype (sizeTwoOrbitAdmissibleSourceBaseForColumn q z) :=
  Subtype.fintype _

theorem sizeTwoOrbitAdmissibleSourceBaseForColumn_card
    (q : ℕ) [NeZero q] (z : ZMod q) (hq1 : (1 : ZMod q) ≠ 0) :
    Fintype.card (sizeTwoOrbitAdmissibleSourceBaseForColumn q z) = q - 2 := by
  classical
  have hzne : z ≠ z + 1 := by
    intro h
    apply hq1
    have hz := congrArg (fun w : ZMod q => w - z) h
    simpa using hz.symm
  change Fintype.card {x : ZMod q // x ≠ z ∧ x ≠ z + 1} = q - 2
  rw [Fintype.card_subtype]
  rw [show ({x : ZMod q | x ≠ z ∧ x ≠ z + 1} : Finset (ZMod q)) =
      Finset.univ \ {z, z + 1} by
    ext x
    simp [not_or]]
  simp [Finset.card_sdiff, ZMod.card, hzne]

/-- Every absolute target column receives total multiplicity `q - 2` from
one fixed source-difference orbit. -/
theorem sizeTwoOrbitNeighborMultiplicity_column_sum
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hq1 : (1 : ZMod q) ≠ 0)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (t : sizeTwoAllowedDifference q a) (z : ZMod q) :
    (∑ v : sizeTwoCyclicExteriorCell q a,
      if v.1.2 = z then sizeTwoOrbitNeighborMultiplicity q a C t v else 0) =
      q - 2 := by
  classical
  calc
    _ = ∑ v : sizeTwoCyclicExteriorCell q a, ∑ x : ZMod q,
        if v.1.2 = z ∧ C.Adj (sizeTwoCyclicCellAt q a x t) v
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      unfold sizeTwoOrbitNeighborMultiplicity
      rw [Finset.card_filter]
      by_cases hv : v.1.2 = z <;> simp [hv]
    _ = ∑ x : ZMod q, ∑ v : sizeTwoCyclicExteriorCell q a,
        if v.1.2 = z ∧ C.Adj (sizeTwoCyclicCellAt q a x t) v
          then 1 else 0 := Finset.sum_comm
    _ = ∑ x : ZMod q,
        ((C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          fun v => v.1.2 = z).card := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show (C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          (fun v => v.1.2 = z) =
          (Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)).filter
            (fun v => v.1.2 = z ∧
              C.Adj (sizeTwoCyclicCellAt q a x t) v) by
        ext v
        simp [C.mem_neighborFinset, and_comm]]
      rw [Finset.card_filter]
    _ = ∑ x : ZMod q, if x = z ∨ x = z + 1 then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hcol_hit]
      simp [sizeTwoCyclicCellAt_fst]
    _ = Fintype.card (sizeTwoOrbitAdmissibleSourceBaseForColumn q z) := by
      change (∑ x : ZMod q,
          if x = z ∨ x = z + 1 then 0 else 1) =
        Fintype.card {x : ZMod q // x ≠ z ∧ x ≠ z + 1}
      rw [Fintype.card_subtype, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x = z ∨ x = z + 1
      · have hn : ¬(x ≠ z ∧ x ≠ z + 1) := by
          intro hb
          exact h.elim hb.1 hb.2
        simp [h, hn]
      · have hn : x ≠ z ∧ x ≠ z + 1 := not_or.mp h
        simp [h, hn]
    _ = q - 2 := sizeTwoOrbitAdmissibleSourceBaseForColumn_card q z hq1

end

end Erdos85

#print axioms Erdos85.sizeTwoOrbitAdmissibleSourceBaseForRow_card
#print axioms Erdos85.sizeTwoOrbitNeighborMultiplicity_row_sum
#print axioms Erdos85.sizeTwoOrbitAdmissibleSourceBaseForColumn_card
#print axioms Erdos85.sizeTwoOrbitNeighborMultiplicity_column_sum
