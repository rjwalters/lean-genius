import Proofs.Erdos85MuThreeSixPointDerangementTypeCocycle
import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyCocycle

/-!
# Cycle-type closure on a rectangle-monodromy triangle

For three eligible rows and two columns, the three rectangle monodromies are
fixed-point-free permutations of the same six-cell column fiber and satisfy
the exact cocycle law.  The abstract six-point calculation therefore says
that any two `(3,3)` types force the third: exactly two `(3,3)` rectangles are
impossible.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Rectangle type cocycle.**  On three distinct eligible rows, any two
`(3,3)` rectangle monodromies force the third to have type `(3,3)`. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_threeThree_pairwise_closure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' a'' : X) (haa' : a ≠ a') (haa'' : a ≠ a'')
    (ha'a'' : a' ≠ a'')
    (b b' : Y) (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b') :
    let σ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
      code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b'
    let τ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
      code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
        ha'b ha'b' ha''b ha''b'
    let υ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
      code.foreignRectangleMonodromyEquiv H K C a a'' b b'
        hab hab' ha''b ha''b'
    (σ.cycleType = {3, 3} ∧ τ.cycleType = {3, 3} →
      υ.cycleType = {3, 3}) ∧
    (τ.cycleType = {3, 3} ∧ υ.cycleType = {3, 3} →
      σ.cycleType = {3, 3}) ∧
    (σ.cycleType = {3, 3} ∧ υ.cycleType = {3, 3} →
      τ.cycleType = {3, 3}) := by
  dsimp only
  let σ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a' b b'
      hab hab' ha'b ha'b'
  let τ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
      ha'b ha'b' ha''b ha''b'
  let υ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a a'' b b'
      hab hab' ha''b ha''b'
  have hσfree : ∀ x, σ x ≠ x := by
    exact code.foreignRectangleMonodromyEquiv_ne H K C haa' hbb'
      hab hab' ha'b ha'b'
  have hτfree : ∀ x, τ x ≠ x := by
    exact code.foreignRectangleMonodromyEquiv_ne H K C ha'a'' hbb'
      ha'b ha'b' ha''b ha''b'
  have hυfree : ∀ x, υ x ≠ x := by
    exact code.foreignRectangleMonodromyEquiv_ne H K C haa'' hbb'
      hab hab' ha''b ha''b'
  have hmul : τ * σ = υ := by
    apply Equiv.ext
    intro u
    exact Equiv.congr_fun
      (code.foreignRectangleMonodromyEquiv_trans H K C a a' a'' b b'
        hab hab' ha'b ha'b' ha''b ha''b') u
  have hclosure := sixElement_threeThree_cocycle_pairwise_closure
    (code.card_occupiedColumnFiber_eq_six H K C b)
    σ τ hσfree hτfree (by simpa [hmul] using hυfree)
  simpa [hmul] using hclosure

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_threeThree_pairwise_closure
