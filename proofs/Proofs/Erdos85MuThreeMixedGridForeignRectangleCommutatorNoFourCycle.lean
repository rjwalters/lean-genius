import Proofs.Erdos85MuThreeMixedGridForeignRectangleCommutatorExponentThirty

/-!
# A forced rectangle commutator without a four-cycle

For a permutation, every cycle length divides the order.  Hence `κ ^ 30 = 1`
rules out a cycle of length four.  This turns the exponent socket into a more
geometric K-side target: proving that every eligible rectangle commutator has
a four-cycle would close the branch.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A permutation whose thirtieth power is one has no four-cycle. -/
theorem four_not_mem_cycleType_of_pow_thirty
    {α : Type*} [Fintype α] [DecidableEq α]
    (κ : Equiv.Perm α) (h30 : κ ^ 30 = 1) : 4 ∉ κ.cycleType := by
  intro hfour
  have hdvd : 4 ∣ 30 :=
    (Equiv.Perm.dvd_of_mem_cycleType hfour).trans
      (orderOf_dvd_of_pow_eq_one h30)
  norm_num at hdvd

/-- **Unavoidable no-four-cycle commutator.**  H-C4-freeness forces a
concrete rectangle commutator whose cycle type does not contain `4`. -/
theorem MuThreeMixedGridCode.exists_rectangle_commutator_four_not_mem_cycleType_of_c4Free
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
        4 ∉ κ.cycleType := by
  obtain ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', h30⟩ :=
    code.exists_rectangle_commutator_pow_thirty_of_c4Free H K C hc4
  exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'',
    four_not_mem_cycleType_of_pow_thirty _ h30⟩

/-- The geometric K-side socket: every eligible rectangle commutator has a
four-cycle. -/
def MuThreeMixedGridCode.RectangleCommutatorsHaveFourCycle
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
      4 ∈ κ.cycleType

/-- **Geometric conditional capstone.**  If K-geometry forces a four-cycle in
every eligible rectangle commutator, H-C4-freeness is impossible. -/
theorem MuThreeMixedGridCode.false_of_c4Free_of_rectangleCommutatorsHaveFourCycle
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hc4 : ¬ containsC4 (X ⊕ Y) (relationBipartiteGraph H))
    (hhave : code.RectangleCommutatorsHaveFourCycle H K C) : False := by
  obtain ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', hno4⟩ :=
    code.exists_rectangle_commutator_four_not_mem_cycleType_of_c4Free
      H K C hc4
  exact hno4 (hhave a.1 a'.1 a''.1
    (fun h => haa' (Subtype.ext h))
    (fun h => haa'' (Subtype.ext h))
    (fun h => ha'a'' (Subtype.ext h))
    b b' hbb' a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2)

end


end Erdos85

#print axioms Erdos85.four_not_mem_cycleType_of_pow_thirty
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_rectangle_commutator_four_not_mem_cycleType_of_c4Free
#print axioms
  Erdos85.MuThreeMixedGridCode.false_of_c4Free_of_rectangleCommutatorsHaveFourCycle
