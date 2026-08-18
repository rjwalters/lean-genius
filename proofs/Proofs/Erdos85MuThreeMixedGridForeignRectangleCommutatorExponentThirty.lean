import Proofs.Erdos85MuThreeMixedGridForeignRectangleCommutatorTrichotomy

/-!
# A single exponent-30 rectangle commutator identity

Orders dividing `2`, `3`, or `5` all divide `30`.  Thus the unavoidable
trichotomy collapses to one identity, `κ ^ 30 = 1`.  This is a simpler and
strictly weaker downstream target for K-geometry than excluding three power
identities separately.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Unavoidable exponent thirty.**  H-C4-freeness forces a concrete
three-row rectangle commutator whose thirtieth power is the identity. -/
theorem MuThreeMixedGridCode.exists_rectangle_commutator_pow_thirty_of_c4Free
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hc4 : ¬ containsC4 (X ⊕ Y) (relationBipartiteGraph H)) :
    ∃ b b' : Y, b ≠ b' ∧
      ∃ a a' a'' : commonForeignRows H b b',
        a ≠ a' ∧ a ≠ a'' ∧ a' ≠ a'' ∧
        let κ := permCommutator
          (code.foreignRectangleMonodromyEquiv H K C a.1 a'.1 b b'
            a.2.1 a.2.2 a'.2.1 a'.2.2)
          (code.foreignRectangleMonodromyEquiv H K C a'.1 a''.1 b b'
            a'.2.1 a'.2.2 a''.2.1 a''.2.2)
        κ ^ 30 = 1 := by
  obtain ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', hpow⟩ :=
    code.exists_rectangle_commutator_pow_five_or_three_or_two_of_c4Free
      H K C hc4
  refine ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', ?_⟩
  dsimp only
  rcases hpow with h5 | h3 | h2
  · rw [show 30 = 5 * 6 by norm_num, pow_mul, h5, one_pow]
  · rw [show 30 = 3 * 10 by norm_num, pow_mul, h3, one_pow]
  · rw [show 30 = 2 * 15 by norm_num, pow_mul, h2, one_pow]

/-- The exact single-identity K-side obligation. -/
def MuThreeMixedGridCode.RectangleCommutatorsAvoidThirty
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
      κ ^ 30 ≠ 1

/-- **Single-socket conditional capstone.**  If K-geometry rules out
thirtieth-power identity for every eligible rectangle commutator, then
H-C4-freeness is impossible. -/
theorem MuThreeMixedGridCode.false_of_c4Free_of_rectangleCommutatorsAvoidThirty
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hc4 : ¬ containsC4 (X ⊕ Y) (relationBipartiteGraph H))
    (havoid : code.RectangleCommutatorsAvoidThirty H K C) : False := by
  obtain ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', h30⟩ :=
    code.exists_rectangle_commutator_pow_thirty_of_c4Free H K C hc4
  exact (havoid a.1 a'.1 a''.1
    (fun h => haa' (Subtype.ext h))
    (fun h => haa'' (Subtype.ext h))
    (fun h => ha'a'' (Subtype.ext h))
    b b' hbb' a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2) h30

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.exists_rectangle_commutator_pow_thirty_of_c4Free
#print axioms Erdos85.MuThreeMixedGridCode.false_of_c4Free_of_rectangleCommutatorsAvoidThirty
