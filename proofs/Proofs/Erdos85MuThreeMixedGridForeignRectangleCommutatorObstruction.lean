import Proofs.Erdos85MuThreeMixedGridForeignRectangleCommutatorTrichotomy

/-!
# The exact commutator obstruction socket for K-geometry

This file does not assume an unsupported preservation law.  Instead it states
the precise downstream obligation: if `K`-geometry can show that every
eligible three-row rectangle commutator avoids the power identities `5`, `3`,
and `2`, then H-C4-freeness is impossible.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The missing K-side statement, isolated as an explicit proposition: every
eligible three-row rectangle commutator avoids orders dividing `5`, `3`, and
`2`. -/
def MuThreeMixedGridCode.RectangleCommutatorsAvoidTwoThreeFive
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) : Prop :=
  ∀ (a a' a'' : X), a ≠ a' → a ≠ a'' → a' ≠ a'' →
    ∀ (b b' : Y), b ≠ b' →
    ∀ (hab : ¬ H a b) (hab' : ¬ H a b')
      (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
      (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b'),
      let κ := permCommutator
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b')
        (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
          ha'b ha'b' ha''b ha''b')
      κ ^ 5 ≠ 1 ∧ κ ^ 3 ≠ 1 ∧ κ ^ 2 ≠ 1

/-- **Conditional all-triangle algebra capstone.**  H-C4-freeness contradicts
the exact small-order prohibition above.  A future K-geometry theorem need
only establish `RectangleCommutatorsAvoidTwoThreeFive`; all overlap, parity,
cycle-type, conjugacy, and finite-group bookkeeping is discharged here. -/
theorem MuThreeMixedGridCode.false_of_c4Free_of_rectangleCommutatorsAvoidTwoThreeFive
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hc4 : ¬ containsC4 (X ⊕ Y) (relationBipartiteGraph H))
    (havoid : code.RectangleCommutatorsAvoidTwoThreeFive H K C) : False := by
  obtain ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', hpow⟩ :=
    code.exists_rectangle_commutator_pow_five_or_three_or_two_of_c4Free
      H K C hc4
  have hne := havoid a.1 a'.1 a''.1
    (fun h => haa' (Subtype.ext h))
    (fun h => haa'' (Subtype.ext h))
    (fun h => ha'a'' (Subtype.ext h))
    b b' hbb' a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2
  rcases hpow with h5 | h3 | h2
  · exact hne.1 h5
  · exact hne.2.1 h3
  · exact hne.2.2 h2

end


end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.false_of_c4Free_of_rectangleCommutatorsAvoidTwoThreeFive
