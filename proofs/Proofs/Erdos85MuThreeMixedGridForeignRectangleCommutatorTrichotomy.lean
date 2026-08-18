import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyTypePatterns
import Proofs.Erdos85MuThreeSixPointDerangementCommutatorOrder

/-!
# An unavoidable rectangle commutator of order dividing 5, 3, or 2

The overlap-one parity pigeonhole forces an even monodromy triangle.  Its five
possible cycle-type patterns have already been compressed into three
commutator identities.  This file packages the entire chain into one
graph-facing theorem.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Unavoidable commutator-order trichotomy.**  If the bipartite H-factor is
C4-free, some pair of columns and three common eligible rows produce a
rectangle commutator whose order divides `5`, `3`, or `2`. -/
theorem MuThreeMixedGridCode.exists_rectangle_commutator_pow_five_or_three_or_two_of_c4Free
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
        κ ^ 5 = 1 ∨ κ ^ 3 = 1 ∨ κ ^ 2 = 1 := by
  obtain ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', hpattern⟩ :=
    code.exists_even_monodromy_triangle_typePattern_of_c4Free H K C hc4
  let σ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a.1 a'.1 b b'
      a.2.1 a.2.2 a'.2.1 a'.2.2
  let τ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a'.1 a''.1 b b'
      a'.2.1 a'.2.2 a''.2.1 a''.2.2
  let υ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a.1 a''.1 b b'
      a.2.1 a.2.2 a''.2.1 a''.2.2
  have hmul : τ * σ = υ := by
    apply Equiv.ext
    intro u
    exact Equiv.congr_fun
      (code.foreignRectangleMonodromyEquiv_trans H K C
        a.1 a'.1 a''.1 b b' a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2) u
  unfold sixElementCocycleTypePattern at hpattern
  rcases hpattern with hall42 | hσ33 | hτ33 | hp33 | hall33
  · have h5 := code.foreignRectangleMonodromy_allFourTwo_commutator_pow_five
      H K C a.1 a'.1 a''.1
      (fun h => haa' (Subtype.ext h)) (fun h => haa'' (Subtype.ext h))
      (fun h => ha'a'' (Subtype.ext h)) b b' hbb'
      a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2
      hall42.1 hall42.2.1 (by simpa [σ, τ, υ, hmul] using hall42.2.2)
    exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', Or.inl h5⟩
  · have h3 := code.foreignRectangleMonodromy_exactlyOneThreeThree_commutator_pow_three
      H K C a.1 a'.1 a''.1
      (fun h => haa' (Subtype.ext h)) (fun h => haa'' (Subtype.ext h))
      (fun h => ha'a'' (Subtype.ext h)) b b' hbb'
      a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2
      (Or.inl ⟨hσ33.1, hσ33.2.1,
        by simpa [σ, τ, υ, hmul] using hσ33.2.2⟩)
    exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', Or.inr (Or.inl h3)⟩
  · have h3 := code.foreignRectangleMonodromy_exactlyOneThreeThree_commutator_pow_three
      H K C a.1 a'.1 a''.1
      (fun h => haa' (Subtype.ext h)) (fun h => haa'' (Subtype.ext h))
      (fun h => ha'a'' (Subtype.ext h)) b b' hbb'
      a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2
      (Or.inr (Or.inl ⟨hτ33.1, hτ33.2.1,
        by simpa [σ, τ, υ, hmul] using hτ33.2.2⟩))
    exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', Or.inr (Or.inl h3)⟩
  · have h3 := code.foreignRectangleMonodromy_exactlyOneThreeThree_commutator_pow_three
      H K C a.1 a'.1 a''.1
      (fun h => haa' (Subtype.ext h)) (fun h => haa'' (Subtype.ext h))
      (fun h => ha'a'' (Subtype.ext h)) b b' hbb'
      a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2
      (Or.inr (Or.inr ⟨hp33.1, hp33.2.1,
        by simpa [σ, τ, υ, hmul] using hp33.2.2⟩))
    exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', Or.inr (Or.inl h3)⟩
  · have h2 := code.foreignRectangleMonodromy_allThreeThree_commutator_pow_two
      H K C a.1 a'.1 a''.1
      (fun h => haa' (Subtype.ext h)) (fun h => haa'' (Subtype.ext h))
      (fun h => ha'a'' (Subtype.ext h)) b b' hbb'
      a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2
      hall33.1 hall33.2.1 (by simpa [σ, τ, υ, hmul] using hall33.2.2)
    exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', Or.inr (Or.inr h2)⟩

end


end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.exists_rectangle_commutator_pow_five_or_three_or_two_of_c4Free
