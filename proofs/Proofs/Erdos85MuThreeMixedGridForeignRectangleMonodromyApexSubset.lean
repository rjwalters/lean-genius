import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyParityPigeonhole

/-!
# Two-point apex subsets distinguish even monodromy types

An even derangement on six points is `(4,2)` or `(3,3)`.  If it preserves a
two-element subset, its restriction swaps those two points, producing a
point fixed by the square.  This excludes `(3,3)`, so the monodromy must have
cycle type `(4,2)`.
-/

namespace Erdos85

noncomputable section

/-- A fixed-point-free permutation preserving a two-element finset has a
point of that finset fixed by its square. -/
theorem exists_mem_sq_fixed_of_fixedPointFree_maps_twoSet
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (A : Finset α) (hA : A.card = 2)
    (hfree : ∀ x, σ x ≠ x) (hmap : ∀ x ∈ A, σ x ∈ A) :
    ∃ x ∈ A, (σ ^ 2) x = x := by
  rcases Finset.card_eq_two.mp hA with ⟨p, q, hpq, hAeq⟩
  have hpA : p ∈ A := by rw [hAeq]; simp
  have hqA : q ∈ A := by rw [hAeq]; simp
  have hpimage := hmap p hpA
  have hqimage := hmap q hqA
  rw [hAeq] at hpimage hqimage
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpimage hqimage
  have hpqimage : σ p = q := hpimage.resolve_left (hfree p)
  have hqpimage : σ q = p := hqimage.resolve_right (hfree q)
  refine ⟨p, hpA, ?_⟩
  simp [pow_two, hpqimage, hqpimage]

/-- An even six-point derangement with a square-fixed point cannot be the
`(3,3)` type, so it is `(4,2)`. -/
theorem even_fixedPointFree_cycleType_eq_fourTwo_of_exists_sq_fixed
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6) (σ : Equiv.Perm α)
    (hfree : ∀ x, σ x ≠ x) (heven : Equiv.Perm.sign σ = 1)
    (hsq : ∃ x, (σ ^ 2) x = x) :
    σ.cycleType = {2, 4} := by
  rcases even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
    hcard σ hfree heven with hfourTwo | hthreeThree
  · exact hfourTwo
  · exfalso
    have hpow3 : σ ^ 3 = 1 := by
      rw [Equiv.Perm.pow_prime_eq_one_iff]
      intro n hn
      rw [hthreeThree] at hn
      simp at hn
      omega
    rcases hsq with ⟨x, hx2⟩
    have hx3 := congrArg (fun τ : Equiv.Perm α => τ x) hpow3
    have hfix : σ x = x := by
      simpa [show σ ^ 3 = σ * σ ^ 2 by group, hx2] using hx3
    exact hfree x hfix

/-- Combined criterion: an even derangement on six points preserving a
two-element subset has cycle type `(4,2)`. -/
theorem even_fixedPointFree_cycleType_eq_fourTwo_of_maps_twoSet
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6) (σ : Equiv.Perm α)
    (hfree : ∀ x, σ x ≠ x) (heven : Equiv.Perm.sign σ = 1)
    (A : Finset α) (hA : A.card = 2) (hmap : ∀ x ∈ A, σ x ∈ A) :
    σ.cycleType = {2, 4} := by
  apply even_fixedPointFree_cycleType_eq_fourTwo_of_exists_sq_fixed
    hcard σ hfree heven
  obtain ⟨x, _hxA, hx2⟩ :=
    exists_mem_sq_fixed_of_fixedPointFree_maps_twoSet σ A hA hfree hmap
  exact ⟨x, hx2⟩

/-- Rectangle specialization: an even H-empty rectangle monodromy preserving
any two-element subset of its six-cell source fiber has type `(4,2)`. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_even_cycleType_eq_fourTwo_of_maps_twoSet
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
        hab hab' ha'b ha'b') = 1)
    (A : Finset {u : muThreeMixedCell K // u.1.2 = b}) (hA : A.card = 2)
    (hmap : ∀ u ∈ A,
      code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b' u ∈ A) :
    Equiv.Perm.cycleType
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') = {2, 4} := by
  apply even_fixedPointFree_cycleType_eq_fourTwo_of_maps_twoSet
    (code.card_occupiedColumnFiber_eq_six H K C b) _ _ heven A hA hmap
  exact code.foreignRectangleMonodromyEquiv_ne H K C haa' hbb'
    hab hab' ha'b ha'b'

end

end Erdos85

#print axioms Erdos85.exists_mem_sq_fixed_of_fixedPointFree_maps_twoSet
#print axioms
  Erdos85.even_fixedPointFree_cycleType_eq_fourTwo_of_exists_sq_fixed
#print axioms Erdos85.even_fixedPointFree_cycleType_eq_fourTwo_of_maps_twoSet
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_even_cycleType_eq_fourTwo_of_maps_twoSet
