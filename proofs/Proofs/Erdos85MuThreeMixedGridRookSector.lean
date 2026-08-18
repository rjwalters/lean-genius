import Proofs.Erdos85MuThreeMixedGridMinusTwoSector

/-!
# Forced and free sectors of the mixed `mu = 3` grid

The `-2` eigenspace of the occupied rook graph is the sector with zero sum
on every occupied row and column.  Its complement is spanned by the row and
column indicators, on which the exterior adjacency action is completely
forced by the hit laws.
-/

open SimpleGraph

namespace Erdos85

section


variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  (K : X → Y → Prop) [DecidableRel K]

/-- Integral indicator of an occupied row. -/
def mixedGridRowIndicatorInt (x : X) : muThreeMixedCell K → ℤ :=
  fun u => if u.1.1 = x then 1 else 0

/-- Integral indicator of an occupied column. -/
def mixedGridColumnIndicatorInt (y : Y) : muThreeMixedCell K → ℤ :=
  fun u => if u.1.2 = y then 1 else 0

/-- Sum of a vector on one occupied row. -/
def mixedGridRowSum (f : muThreeMixedCell K → ℤ) (x : X) : ℤ :=
  ∑ u, if u.1.1 = x then f u else 0

/-- Sum of a vector on one occupied column. -/
def mixedGridColumnSum (f : muThreeMixedCell K → ℤ) (y : Y) : ℤ :=
  ∑ u, if u.1.2 = y then f u else 0

/-- Entrywise action of the occupied rook graph. -/
theorem mixedGridRowColumnGraph_mulVec_apply
    (f : muThreeMixedCell K → ℤ) (u : muThreeMixedCell K) :
    ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f u =
      mixedGridRowSum K f u.1.1 + mixedGridColumnSum K f u.1.2 - 2 * f u := by
  classical
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
    mixedGridRowColumnGraph, mixedGridRowSum, mixedGridColumnSum]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x, (if x ≠ u ∧ (x.1.1 = u.1.1 ∨ x.1.2 = u.1.2) then 1 else 0) * f x) =
        ∑ x, ((if x.1.1 = u.1.1 then f x else 0) +
          (if x.1.2 = u.1.2 then f x else 0) -
          (if x = u then 2 * f x else 0)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxu : x = u
      · subst x
        simp
      · by_cases hr : x.1.1 = u.1.1 <;>
          by_cases hc : x.1.2 = u.1.2 <;> simp [hxu, hr, hc]
    _ = _ := by
      simp [Finset.sum_sub_distrib]

/-- Zero row and column sums imply rook eigenvalue `-2`. -/
theorem mixedGridRowColumnGraph_mulVec_eq_negTwo_of_zero_sums
    (f : muThreeMixedCell K → ℤ)
    (hrow : ∀ x, mixedGridRowSum K f x = 0)
    (hcol : ∀ y, mixedGridColumnSum K f y = 0) :
    ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f = (-2 : ℤ) • f := by
  funext u
  rw [mixedGridRowColumnGraph_mulVec_apply K, hrow, hcol]
  simp

end

section Code

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
  (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]

/-- Any two rows have a column occupied in both: each forbids only two of
the eight columns. -/
theorem MuThreeMixedGridCode.exists_common_occupied_column
    (code : MuThreeMixedGridCode H K C) (x x' : X) :
    ∃ y, ¬ K x y ∧ ¬ K x' y := by
  classical
  by_contra h
  push_neg at h
  let S := (Finset.univ : Finset Y).filter fun y => K x y
  let T := (Finset.univ : Finset Y).filter fun y => K x' y
  have hsub : (Finset.univ : Finset Y) ⊆ S ∪ T := by
    intro y _hy
    rcases h y with hxy | hx'y
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hxy⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hx'y⟩))
  have hle := Finset.card_le_card hsub
  have hunion := Finset.card_union_le S T
  have hS : S.card = 2 := code.K_twoRegular.1 x
  have hT : T.card = 2 := code.K_twoRegular.1 x'
  simp only [Finset.card_univ, code.card_right] at hle
  omega

/-- Any two columns have a row occupied in both. -/
theorem MuThreeMixedGridCode.exists_common_occupied_row
    (code : MuThreeMixedGridCode H K C) (y y' : Y) :
    ∃ x, ¬ K x y ∧ ¬ K x y' := by
  classical
  by_contra h
  push_neg at h
  let S := (Finset.univ : Finset X).filter fun x => K x y
  let T := (Finset.univ : Finset X).filter fun x => K x y'
  have hsub : (Finset.univ : Finset X) ⊆ S ∪ T := by
    intro x _hx
    rcases h x with hxy | hxy'
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hxy⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hxy'⟩))
  have hle := Finset.card_le_card hsub
  have hunion := Finset.card_union_le S T
  have hS : S.card = 2 := code.K_twoRegular.2 y
  have hT : T.card = 2 := code.K_twoRegular.2 y'
  simp only [Finset.card_univ, code.card_left] at hle
  omega

/-- The rook `-2` eigen-equation forces every occupied row and column sum
to vanish. -/
theorem MuThreeMixedGridCode.zero_sums_of_rowColumn_mulVec_eq_negTwo
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ)
    (hnegTwo : ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f =
      (-2 : ℤ) • f) :
    (∀ x, mixedGridRowSum K f x = 0) ∧
      (∀ y, mixedGridColumnSum K f y = 0) := by
  have hcell : ∀ u : muThreeMixedCell K,
      mixedGridRowSum K f u.1.1 + mixedGridColumnSum K f u.1.2 = 0 := by
    intro u
    have hu := congrFun hnegTwo u
    rw [mixedGridRowColumnGraph_mulVec_apply K] at hu
    simp only [Pi.smul_apply, smul_eq_mul] at hu
    omega

/-- Exact characterization of the rook `-2` sector. -/
theorem MuThreeMixedGridCode.rowColumn_mulVec_eq_negTwo_iff_zero_sums
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ) :
    ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f = (-2 : ℤ) • f ↔
      (∀ x, mixedGridRowSum K f x = 0) ∧
        (∀ y, mixedGridColumnSum K f y = 0) := by
  constructor
  · exact code.zero_sums_of_rowColumn_mulVec_eq_negTwo H K C f
  · rintro ⟨hrow, hcol⟩
    exact mixedGridRowColumnGraph_mulVec_eq_negTwo_of_zero_sums K f hrow hcol

/-- Every vector in the rook `-2` sector is automatically zero-sum. -/
theorem MuThreeMixedGridCode.sum_eq_zero_of_rowColumn_mulVec_eq_negTwo
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ)
    (hnegTwo : ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f =
      (-2 : ℤ) • f) :
    ∑ u, f u = 0 := by
  have hrow := (code.rowColumn_mulVec_eq_negTwo_iff_zero_sums H K C f).mp
    hnegTwo |>.1
  calc
    ∑ u, f u = ∑ x, mixedGridRowSum K f x := by
      classical
      simp only [mixedGridRowSum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _hu
      simp
    _ = 0 := by simp [hrow]

/-- The `D = 7I - C²` formula on the rook `-2` sector needs no separate
zero-sum hypothesis. -/
theorem MuThreeMixedGridCode.squareResidual_mulVec_of_rowColumn_negTwo'
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ)
    (hnegTwo : ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f =
      (-2 : ℤ) • f) :
    ((mixedGridSquareResidualGraph K C).adjMatrix ℤ).mulVec f =
      (7 : ℤ) • f - (C.adjMatrix ℤ).mulVec ((C.adjMatrix ℤ).mulVec f) := by
  exact code.squareResidual_mulVec_of_rowColumn_negTwo H K C f
    (code.sum_eq_zero_of_rowColumn_mulVec_eq_negTwo H K C f hnegTwo) hnegTwo
  have hrowEq : ∀ x x', mixedGridRowSum K f x = mixedGridRowSum K f x' := by
    intro x x'
    obtain ⟨y, hxy, hx'y⟩ := code.exists_common_occupied_column H K C x x'
    let u : muThreeMixedCell K := ⟨(x, y), hxy⟩
    let u' : muThreeMixedCell K := ⟨(x', y), hx'y⟩
    have hu := hcell u
    have hu' := hcell u'
    change mixedGridRowSum K f x + mixedGridColumnSum K f y = 0 at hu
    change mixedGridRowSum K f x' + mixedGridColumnSum K f y = 0 at hu'
    omega
  have hcolEq : ∀ y y', mixedGridColumnSum K f y = mixedGridColumnSum K f y' := by
    intro y y'
    obtain ⟨x, hxy, hxy'⟩ := code.exists_common_occupied_row H K C y y'
    let u : muThreeMixedCell K := ⟨(x, y), hxy⟩
    let u' : muThreeMixedCell K := ⟨(x, y'), hxy'⟩
    have hu := hcell u
    have hu' := hcell u'
    change mixedGridRowSum K f x + mixedGridColumnSum K f y = 0 at hu
    change mixedGridRowSum K f x + mixedGridColumnSum K f y' = 0 at hu'
    omega
  have hrowTotal : (∑ x, mixedGridRowSum K f x) = ∑ u, f u := by
    classical
    simp only [mixedGridRowSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _hu
    simp
  have hcolTotal : (∑ y, mixedGridColumnSum K f y) = ∑ u, f u := by
    classical
    simp only [mixedGridColumnSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _hu
    simp
  constructor
  · intro x
    obtain ⟨y, hxy, _⟩ := code.exists_common_occupied_column H K C x x
    let u : muThreeMixedCell K := ⟨(x, y), hxy⟩
    have hu := hcell u
    change mixedGridRowSum K f x + mixedGridColumnSum K f y = 0 at hu
    have hrows : (∑ z, mixedGridRowSum K f z) =
        8 * mixedGridRowSum K f x := by
      calc
        _ = ∑ _z : X, mixedGridRowSum K f x := by
          apply Finset.sum_congr rfl
          intro z _hz
          exact hrowEq z x
        _ = _ := by simp [code.card_left]
    have hcols : (∑ z, mixedGridColumnSum K f z) =
        8 * mixedGridColumnSum K f y := by
      calc
        _ = ∑ _z : Y, mixedGridColumnSum K f y := by
          apply Finset.sum_congr rfl
          intro z _hz
          exact hcolEq z y
        _ = _ := by simp [code.card_right]
    rw [hrowTotal, hcolTotal] at hrows hcols
    omega
  · intro y
    obtain ⟨x, hxy, _⟩ := code.exists_common_occupied_row H K C y y
    have hxzero : mixedGridRowSum K f x = 0 := by
      obtain ⟨y', hxy', _⟩ := code.exists_common_occupied_column H K C x x
      let u : muThreeMixedCell K := ⟨(x, y'), hxy'⟩
      have hu := hcell u
      change mixedGridRowSum K f x + mixedGridColumnSum K f y' = 0 at hu
      have hrows : (∑ z, mixedGridRowSum K f z) =
          8 * mixedGridRowSum K f x := by
        calc
          _ = ∑ _z : X, mixedGridRowSum K f x := by
            apply Finset.sum_congr rfl
            intro z _hz
            exact hrowEq z x
          _ = _ := by simp [code.card_left]
      have hcols : (∑ z, mixedGridColumnSum K f z) =
          8 * mixedGridColumnSum K f y' := by
        calc
          _ = ∑ _z : Y, mixedGridColumnSum K f y' := by
            apply Finset.sum_congr rfl
            intro z _hz
            exact hcolEq z y'
          _ = _ := by simp [code.card_right]
      rw [hrowTotal, hcolTotal] at hrows hcols
      omega
    let u : muThreeMixedCell K := ⟨(x, y), hxy⟩
    have hu := hcell u
    change mixedGridRowSum K f x + mixedGridColumnSum K f y = 0 at hu
    omega

/-- Exterior adjacency on a row indicator is completely prescribed by `H`:
the value at `u` records whether row `x` is hit from `u`. -/
theorem MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicatorInt_apply
    (code : MuThreeMixedGridCode H K C) (x : X)
    (u : muThreeMixedCell K) :
    (C.adjMatrix ℤ).mulVec (mixedGridRowIndicatorInt K x) u =
      if H x u.1.2 then 0 else 1 := by
  classical
  calc
    (C.adjMatrix ℤ).mulVec (mixedGridRowIndicatorInt K x) u =
        ((((C.neighborFinset u).filter fun v => v.1.1 = x).card : ℕ) : ℤ) := by
      simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
        mixedGridRowIndicatorInt]
      rw [Finset.sum_boole]
      apply congrArg (fun s : Finset (muThreeMixedCell K) => (s.card : ℤ))
      ext v
      simp [C.mem_neighborFinset]
    _ = if H x u.1.2 then 0 else 1 := by
      rw [code.row_hit u x]
      split <;> simp_all

/-- Column dual of the forced row-indicator action. -/
theorem MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicatorInt_apply
    (code : MuThreeMixedGridCode H K C) (y : Y)
    (u : muThreeMixedCell K) :
    (C.adjMatrix ℤ).mulVec (mixedGridColumnIndicatorInt K y) u =
      if H u.1.1 y then 0 else 1 := by
  classical
  calc
    (C.adjMatrix ℤ).mulVec (mixedGridColumnIndicatorInt K y) u =
        ((((C.neighborFinset u).filter fun v => v.1.2 = y).card : ℕ) : ℤ) := by
      simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
        mixedGridColumnIndicatorInt]
      rw [Finset.sum_boole]
      apply congrArg (fun s : Finset (muThreeMixedCell K) => (s.card : ℤ))
      ext v
      simp [C.mem_neighborFinset]
    _ = if H u.1.1 y then 0 else 1 := by
      rw [code.column_hit u y]
      split <;> simp_all

end Code


end Erdos85

#print axioms Erdos85.mixedGridRowColumnGraph_mulVec_apply
#print axioms Erdos85.mixedGridRowColumnGraph_mulVec_eq_negTwo_of_zero_sums
#print axioms
  Erdos85.MuThreeMixedGridCode.zero_sums_of_rowColumn_mulVec_eq_negTwo
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicatorInt_apply
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicatorInt_apply
#print axioms
  Erdos85.MuThreeMixedGridCode.rowColumn_mulVec_eq_negTwo_iff_zero_sums
#print axioms
  Erdos85.MuThreeMixedGridCode.squareResidual_mulVec_of_rowColumn_negTwo'
