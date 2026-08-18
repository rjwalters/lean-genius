import Proofs.Erdos85MuThreeMixedGridZeroSector
import Proofs.Erdos85MuThreeMixedGridRookSector

/-!
# Identifying the canonical zero sector with the rook `-2` eigenspace

This bridges the indicator/dot-product API for the invariant zero-row and
zero-column sector to the exact rook-eigenvector characterization.  It also
shows intrinsically that the residual square relation preserves the same
sector and acts there as `7I - C²`.
-/

open SimpleGraph

namespace Erdos85

/-- Dotting with a row indicator is the explicit occupied-row sum. -/
theorem mixedGridRowIndicator_dot_eq_rowSum
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (f : muThreeMixedCell K → ℤ) (x : X) :
    mixedGridRowIndicator K x ⬝ᵥ f = mixedGridRowSum K f x := by
  simp [dotProduct, mixedGridRowIndicator, mixedGridRowSum]

/-- Column dual of `mixedGridRowIndicator_dot_eq_rowSum`. -/
theorem mixedGridColumnIndicator_dot_eq_columnSum
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (f : muThreeMixedCell K → ℤ) (y : Y) :
    mixedGridColumnIndicator K y ⬝ᵥ f = mixedGridColumnSum K f y := by
  simp [dotProduct, mixedGridColumnIndicator, mixedGridColumnSum]

/-- **Canonical sector identification.**  The simultaneous zero-row and
zero-column sector is exactly the `-2` eigenspace of the occupied rook
graph. -/
theorem MuThreeMixedGridCode.zeroRowColumn_iff_rowColumn_negTwo
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ) :
    MixedGridZeroRowColumn K f ↔
      ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f = (-2 : ℤ) • f := by
  rw [code.rowColumn_mulVec_eq_negTwo_iff_zero_sums H K C f]
  constructor
  · intro hf
    constructor
    · intro x
      rw [← mixedGridRowIndicator_dot_eq_rowSum K f x]
      exact hf.1 x
    · intro y
      rw [← mixedGridColumnIndicator_dot_eq_columnSum K f y]
      exact hf.2 y
  · rintro ⟨hrow, hcol⟩
    constructor
    · intro x
      rw [mixedGridRowIndicator_dot_eq_rowSum K f x]
      exact hrow x
    · intro y
      rw [mixedGridColumnIndicator_dot_eq_columnSum K f y]
      exact hcol y

/-- On the canonical zero sector, residual adjacency is exactly `7I-C²`. -/
theorem MuThreeMixedGridCode.squareResidual_mulVec_of_zeroRowColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    ((mixedGridSquareResidualGraph K C).adjMatrix ℤ).mulVec f =
      (7 : ℤ) • f - (C.adjMatrix ℤ).mulVec ((C.adjMatrix ℤ).mulVec f) := by
  apply code.squareResidual_mulVec_of_rowColumn_negTwo' H K C
  exact (code.zeroRowColumn_iff_rowColumn_negTwo H K C f).mp hf

/-- Residual adjacency preserves the canonical zero sector. -/
theorem MuThreeMixedGridCode.zeroRowColumn_squareResidual_invariant
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    MixedGridZeroRowColumn K
      (((mixedGridSquareResidualGraph K C).adjMatrix ℤ).mulVec f) := by
  apply (code.zeroRowColumn_iff_rowColumn_negTwo H K C _).mpr
  apply code.squareResidual_mulVec_preserves_rowColumn_negTwo H K C
  exact (code.zeroRowColumn_iff_rowColumn_negTwo H K C f).mp hf

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.zeroRowColumn_iff_rowColumn_negTwo
#print axioms
  Erdos85.MuThreeMixedGridCode.squareResidual_mulVec_of_zeroRowColumn
#print axioms
  Erdos85.MuThreeMixedGridCode.zeroRowColumn_squareResidual_invariant
