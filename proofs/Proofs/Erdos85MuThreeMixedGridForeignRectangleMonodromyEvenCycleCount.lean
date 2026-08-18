import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromySign
import Proofs.Erdos85MuThreeMixedGridForeignRowTransportSaturation
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Cycle count of even rectangle monodromy

An axiom-clean cycle-type argument replaces finite permutation enumeration:
an even fixed-point-free permutation of a six-element type has exactly two
nontrivial cycles.  Applied to rectangle monodromy, this leaves precisely the
`(4,2)` and `(3,3)` possibilities whenever the rectangle sign is positive.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An even derangement of a six-element type has exactly two nontrivial
cycles. -/
theorem even_fixedPointFree_cycleType_card_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6) (σ : Equiv.Perm α)
    (hfree : ∀ x, σ x ≠ x) (heven : Equiv.Perm.sign σ = 1) :
    σ.cycleType.card = 2 := by
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support, hfree x]
  have hsum : σ.cycleType.sum = 6 := by
    rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ, hcard]
  have hbound_aux : ∀ m : Multiset ℕ,
      (∀ n ∈ m, 2 ≤ n) → 2 * m.card ≤ m.sum := by
    intro m hm
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons n s ih =>
        rw [Multiset.card_cons, Multiset.sum_cons]
        have hn : 2 ≤ n := hm n (by simp)
        have ih' : ∀ k ∈ s, 2 ≤ k := by
          intro k hk
          exact hm k (by simp [hk])
        have hi := ih ih'
        omega
  have hbound : 2 * σ.cycleType.card ≤ σ.cycleType.sum :=
    hbound_aux σ.cycleType (fun n hn => Equiv.Perm.two_le_of_mem_cycleType hn)
  have hpositive : 0 < σ.cycleType.card := by
    by_contra h
    have hc : σ.cycleType.card = 0 := Nat.eq_zero_of_not_pos h
    have hm : σ.cycleType = 0 := Multiset.card_eq_zero.mp hc
    simp [hm] at hsum
  have hcard_le : σ.cycleType.card ≤ 3 := by omega
  have hpow : (-1 : ℤˣ) ^ (6 + σ.cycleType.card) = 1 := by
    rw [← hsum]
    exact (Equiv.Perm.sign_of_cycleType σ).symm.trans heven
  have hparity : Even (6 + σ.cycleType.card) :=
    (neg_one_pow_eq_one_iff_even (by norm_num)).mp hpow
  rcases hparity with ⟨k, hk⟩
  omega

/-- Exact axiom-clean classification: an even derangement on six points has
cycle type `(4,2)` or `(3,3)`. -/
theorem even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6) (σ : Equiv.Perm α)
    (hfree : ∀ x, σ x ≠ x) (heven : Equiv.Perm.sign σ = 1) :
    σ.cycleType = {2, 4} ∨ σ.cycleType = {3, 3} := by
  have hc := even_fixedPointFree_cycleType_card_eq_two hcard σ hfree heven
  rcases Multiset.card_eq_two.mp hc with ⟨x, y, hxy⟩
  have hsupp : σ.support = Finset.univ := by
    ext z
    simp [Equiv.Perm.mem_support, hfree z]
  have hsum : x + y = 6 := by
    rw [← Multiset.sum_pair, ← hxy, Equiv.Perm.sum_cycleType,
      hsupp, Finset.card_univ, hcard]
  have hxmem : x ∈ σ.cycleType := by rw [hxy]; simp
  have hymem : y ∈ σ.cycleType := by rw [hxy]; simp
  have hx : 2 ≤ x := Equiv.Perm.two_le_of_mem_cycleType hxmem
  have hy : 2 ≤ y := Equiv.Perm.two_le_of_mem_cycleType hymem
  have hcases :
      (x = 2 ∧ y = 4) ∨ (x = 3 ∧ y = 3) ∨ (x = 4 ∧ y = 2) := by
    omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hxy
  · exact Or.inr hxy
  · apply Or.inl
    rw [hxy]
    change 4 ::ₘ 2 ::ₘ 0 = 2 ::ₘ 4 ::ₘ 0
    exact Multiset.cons_swap 4 2 0

/-- A positive-sign H-empty rectangle monodromy has exactly two cycles. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_even_cycleType_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {a a' : X} (haa' : a ≠ a') {b b' : Y} (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (heven : Equiv.Perm.sign
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b') = 1) :
    (Equiv.Perm.cycleType
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b')).card = 2 := by
  apply even_fixedPointFree_cycleType_card_eq_two
    (code.card_occupiedColumnFiber_eq_six H K C b) _ _ heven
  exact code.foreignRectangleMonodromyEquiv_ne H K C haa' hbb'
    hab hab' ha'b ha'b'

/-- Exact cycle-type alternative for a positive-sign H-empty rectangle. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_even_cycleType
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {a a' : X} (haa' : a ≠ a') {b b' : Y} (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (heven : Equiv.Perm.sign
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b') = 1) :
    Equiv.Perm.cycleType
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') = {2, 4} ∨
      Equiv.Perm.cycleType
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') = {3, 3} := by
  apply even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
    (code.card_occupiedColumnFiber_eq_six H K C b) _ _ heven
  exact code.foreignRectangleMonodromyEquiv_ne H K C haa' hbb'
    hab hab' ha'b ha'b'

end

end Erdos85

#print axioms Erdos85.even_fixedPointFree_cycleType_card_eq_two
#print axioms Erdos85.even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_even_cycleType_card
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_even_cycleType
