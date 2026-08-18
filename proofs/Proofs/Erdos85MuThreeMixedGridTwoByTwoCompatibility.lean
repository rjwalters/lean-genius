import Proofs.Erdos85MuThreeMixedGridPerCellColumnMates
import Proofs.Erdos85BranchDeficitSymmetry

/-!
# Two-by-two row/column compatibility

When a component occupies two cells in a column and two cells in a hole row,
the residual edges in that `2 × 2` block can be counted by either margin.
The exact per-cell row and column laws then equate the corresponding sums of
`H` overlaps.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def mixedGridPredicateRowFiber
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (P : muThreeMixedCell K → Prop) [DecidablePred P] (x : X) :=
  (Finset.univ : Finset (muThreeMixedCell K)).filter fun u => P u ∧ u.1.1 = x

def mixedGridPredicateColumnFiber
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (P : muThreeMixedCell K → Prop) [DecidablePred P] (y : Y) :=
  (Finset.univ : Finset (muThreeMixedCell K)).filter fun u => P u ∧ u.1.2 = y

/-- The row/column overlap equation forced by a component's two-cell fibers
around a forbidden cell `(h,y)`. -/
theorem MuThreeMixedGridCode.twoByTwo_overlap_compatibility
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (P : muThreeMixedCell K → Prop) [DecidablePred P]
    (u u' v v' : muThreeMixedCell K) (h : X) (y : Y)
    (huu' : u ≠ u') (hvv' : v ≠ v')
    (huP : P u) (hu'P : P u') (hvP : P v) (hv'P : P v')
    (hconf : ∀ {a b}, P a → (mixedGridSquareResidualGraph K C).Adj a b → P b)
    (hrowFiber : mixedGridPredicateRowFiber P h = {v, v'})
    (hcolFiber : mixedGridPredicateColumnFiber P y = {u, u'})
    (hucol : u.1.2 = y) (hu'col : u'.1.2 = y)
    (hvrow : v.1.1 = h) (hv'row : v'.1.1 = h)
    (hhu : h ≠ u.1.1) (hhu' : h ≠ u'.1.1)
    (hyv : y ≠ v.1.2) (hyv' : y ≠ v'.1.2)
    (hhole : K h y) :
    (mixedGridHCommonColumns H u.1.1 h).card +
      (mixedGridHCommonColumns H u'.1.1 h).card =
      (mixedGridHCommonRows H v.1.2 y).card +
        (mixedGridHCommonRows H v'.1.2 y).card := by
  let D := mixedGridSquareResidualGraph K C
  let S : Finset (muThreeMixedCell K) := {u, u'}
  let T : Finset (muThreeMixedCell K) := {v, v'}
  have rowSet (a : muThreeMixedCell K) (haP : P a) :
      mixedGridGraphMatesInRow D a h = T.filter fun b => D.Adj a b := by
    ext b
    constructor
    · intro hb
      have hb' := Finset.mem_filter.mp hb
      have hbP := hconf haP ((D.mem_neighborFinset a b).mp hb'.1)
      have hbFiber : b ∈ mixedGridPredicateRowFiber P h :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbP, hb'.2⟩
      apply Finset.mem_filter.mpr
      exact ⟨by simpa [T, hrowFiber] using hbFiber,
        (D.mem_neighborFinset a b).mp hb'.1⟩
    · intro hb
      have hb' := Finset.mem_filter.mp hb
      have hbFiber : b ∈ mixedGridPredicateRowFiber P h := by
        rw [hrowFiber]
        simpa [T] using hb'.1
      have hbData := Finset.mem_filter.mp hbFiber
      apply Finset.mem_filter.mpr
      exact ⟨(D.mem_neighborFinset a b).mpr hb'.2, hbData.2.2⟩
  have colSet (b : muThreeMixedCell K) (hbP : P b) :
      mixedGridGraphMatesInColumn D b y = S.filter fun a => D.Adj a b := by
    ext a
    constructor
    · intro ha
      have ha' := Finset.mem_filter.mp ha
      have hba : D.Adj b a := (D.mem_neighborFinset b a).mp ha'.1
      have haP := hconf hbP hba
      have haFiber : a ∈ mixedGridPredicateColumnFiber P y :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, haP, ha'.2⟩
      apply Finset.mem_filter.mpr
      exact ⟨by simpa [S, hcolFiber] using haFiber, D.adj_symm hba⟩
    · intro ha
      have ha' := Finset.mem_filter.mp ha
      have haFiber : a ∈ mixedGridPredicateColumnFiber P y := by
        rw [hcolFiber]
        simpa [S] using ha'.1
      have haData := Finset.mem_filter.mp haFiber
      apply Finset.mem_filter.mpr
      exact ⟨(D.mem_neighborFinset b a).mpr (D.adj_symm ha'.2), haData.2.2⟩
  have hdouble := sum_card_filter_relation_comm S T (fun a b => D.Adj a b)
  have hmargin :
      (mixedGridGraphMatesInRow D u h).card +
        (mixedGridGraphMatesInRow D u' h).card =
      (mixedGridGraphMatesInColumn D v y).card +
        (mixedGridGraphMatesInColumn D v' y).card := by
    rw [rowSet u huP, rowSet u' hu'P, colSet v hvP, colSet v' hv'P]
    simpa [S, T, huu', hvv'] using hdouble
  have huLaw := code.residualMatesInRow_add_overlap_add_indicator
    H K C u h hhu
  have hu'Law := code.residualMatesInRow_add_overlap_add_indicator
    H K C u' h hhu'
  have hvLaw := code.residualMatesInColumn_add_overlap_add_indicator
    H K C v y hyv
  have hv'Law := code.residualMatesInColumn_add_overlap_add_indicator
    H K C v' y hyv'
  dsimp [D] at hmargin
  simp [hucol, hu'col, hvrow, hv'row, hhole] at huLaw hu'Law hvLaw hv'Law
  omega

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.twoByTwo_overlap_compatibility
