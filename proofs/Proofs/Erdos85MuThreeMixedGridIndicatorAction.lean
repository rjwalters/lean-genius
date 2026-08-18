import Proofs.Erdos85MuThreeMixedGridCommutingOperator

/-!
# Forced action on row and column indicators

The row/column hit laws determine the exterior adjacency operator on the
span of occupied-row and occupied-column indicators.  All remaining freedom
therefore lies in the simultaneous zero-row-sum and zero-column-sum sector.
-/

open SimpleGraph

namespace Erdos85

/-- Integer indicator of one occupied row. -/
def mixedGridRowIndicator
    {X Y : Type*} [DecidableEq X] (K : X → Y → Prop) (x : X) :
    muThreeMixedCell K → ℤ :=
  fun u => if u.1.1 = x then 1 else 0

/-- Integer indicator of one occupied column. -/
def mixedGridColumnIndicator
    {X Y : Type*} [DecidableEq Y] (K : X → Y → Prop) (y : Y) :
    muThreeMixedCell K → ℤ :=
  fun u => if u.1.2 = y then 1 else 0

/-- The adjacency action on a row indicator is exactly the row-hit count. -/
theorem MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicator_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (u : muThreeMixedCell K) :
    (C.adjMatrix ℤ).mulVec (mixedGridRowIndicator K x) u =
      if H x u.1.2 then 0 else 1 := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  simp only [mixedGridRowIndicator]
  change (∑ v ∈ C.neighborFinset u, if v.1.1 = x then (1 : ℤ) else 0) = _
  have hsum :
      (∑ v ∈ C.neighborFinset u, if v.1.1 = x then (1 : ℤ) else 0) =
        (((C.neighborFinset u).filter fun v => v.1.1 = x).card : ℤ) := by
    simpa using (Finset.sum_boole (R := ℤ)
      (fun v : muThreeMixedCell K => v.1.1 = x) (C.neighborFinset u))
  rw [hsum]
  exact_mod_cast code.row_hit u x

/-- Column dual of the forced indicator action. -/
theorem MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicator_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (y : Y) (u : muThreeMixedCell K) :
    (C.adjMatrix ℤ).mulVec (mixedGridColumnIndicator K y) u =
      if H u.1.1 y then 0 else 1 := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  simp only [mixedGridColumnIndicator]
  change (∑ v ∈ C.neighborFinset u, if v.1.2 = y then (1 : ℤ) else 0) = _
  have hsum :
      (∑ v ∈ C.neighborFinset u, if v.1.2 = y then (1 : ℤ) else 0) =
        (((C.neighborFinset u).filter fun v => v.1.2 = y).card : ℤ) := by
    simpa using (Finset.sum_boole (R := ℤ)
      (fun v : muThreeMixedCell K => v.1.2 = y) (C.neighborFinset u))
  rw [hsum]
  exact_mod_cast code.column_hit u y

/-- An `H`-row mask is the sum of the two corresponding column indicators. -/
theorem sum_columnIndicator_eq_if
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H]
    (x : X) (u : muThreeMixedCell K) :
    ∑ y ∈ (Finset.univ.filter fun y : Y => H x y),
        mixedGridColumnIndicator K y u =
      if H x u.1.2 then 1 else 0 := by
  classical
  by_cases hH : H x u.1.2
  · rw [if_pos hH]
    have hu : u.1.2 ∈ (Finset.univ.filter fun y : Y => H x y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH⟩
    calc
      ∑ y ∈ (Finset.univ.filter fun y : Y => H x y),
          mixedGridColumnIndicator K y u =
          mixedGridColumnIndicator K u.1.2 u := by
        apply Finset.sum_eq_single u.1.2
        · intro y hy hyne
          simp [mixedGridColumnIndicator, Ne.symm hyne]
        · exact fun h => (h hu).elim
      _ = 1 := by simp [mixedGridColumnIndicator]
  · rw [if_neg hH]
    apply Finset.sum_eq_zero
    intro y hy
    have hyH := (Finset.mem_filter.mp hy).2
    by_cases heq : u.1.2 = y
    · subst y
      exact (hH hyH).elim
    · simp [mixedGridColumnIndicator, heq]

/-- The row-indicator action as `1` minus the sum of the two `H`-selected
column indicators. -/
theorem MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicator_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (x : X) :
    (C.adjMatrix ℤ).mulVec (mixedGridRowIndicator K x) =
      (fun _ => (1 : ℤ)) -
        ∑ y ∈ (Finset.univ.filter fun y : Y => H x y),
          mixedGridColumnIndicator K y := by
  funext u
  rw [MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicator_apply H K C code,
    Pi.sub_apply]
  simp only [Finset.sum_apply]
  rw [sum_columnIndicator_eq_if H K x u]
  split_ifs <;> norm_num

/-- An `H`-column mask is the sum of its selected row indicators. -/
theorem sum_rowIndicator_eq_if
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (H K : X → Y → Prop) [DecidableRel H]
    (y : Y) (u : muThreeMixedCell K) :
    ∑ x ∈ (Finset.univ.filter fun x : X => H x y),
        mixedGridRowIndicator K x u =
      if H u.1.1 y then 1 else 0 := by
  classical
  by_cases hH : H u.1.1 y
  · rw [if_pos hH]
    have hu : u.1.1 ∈ (Finset.univ.filter fun x : X => H x y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH⟩
    calc
      ∑ x ∈ (Finset.univ.filter fun x : X => H x y),
          mixedGridRowIndicator K x u = mixedGridRowIndicator K u.1.1 u := by
        apply Finset.sum_eq_single u.1.1
        · intro x hx hxne
          simp [mixedGridRowIndicator, Ne.symm hxne]
        · exact fun h => (h hu).elim
      _ = 1 := by simp [mixedGridRowIndicator]
  · rw [if_neg hH]
    apply Finset.sum_eq_zero
    intro x hx
    have hxH := (Finset.mem_filter.mp hx).2
    by_cases heq : u.1.1 = x
    · subst x
      exact (hH hxH).elim
    · simp [mixedGridRowIndicator, heq]

/-- Column-indicator action as `1` minus the corresponding selected rows. -/
theorem MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicator_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y : Y) :
    (C.adjMatrix ℤ).mulVec (mixedGridColumnIndicator K y) =
      (fun _ => (1 : ℤ)) -
        ∑ x ∈ (Finset.univ.filter fun x : X => H x y),
          mixedGridRowIndicator K x := by
  funext u
  rw [MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicator_apply H K C code,
    Pi.sub_apply]
  simp only [Finset.sum_apply]
  rw [sum_rowIndicator_eq_if H K y u]
  split_ifs <;> norm_num

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicator_apply
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicator_apply
#print axioms Erdos85.MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicator_eq
#print axioms Erdos85.MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicator_eq
