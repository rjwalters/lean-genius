import Mathlib

/-!
# Arithmetic endpoint for the order-49 miss bidegrees

The open-code collision argument reduces the support-zero side to 25 values
in `{2,3}` summing to 66, and the support-one side to 18 values in `{0,1}`
summing to 15.  This file records the resulting exact profiles independently
of the graph plumbing.
-/

namespace Erdos85

theorem card_fibers_two_three_of_card_sum
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (k : Z → ℕ)
    (hcard : Fintype.card Z = 25)
    (hrange : ∀ z, k z = 2 ∨ k z = 3)
    (hsum : ∑ z, k z = 66) :
    (Finset.univ.filter fun z => k z = 2).card = 9 ∧
      (Finset.univ.filter fun z => k z = 3).card = 16 := by
  let A := Finset.univ.filter fun z => k z = 2
  let B := Finset.univ.filter fun z => k z = 3
  have hpoint (z : Z) : k z = 2 + if k z = 3 then 1 else 0 := by
    rcases hrange z with hz | hz <;> simp [hz]
  have hsumB : (∑ z : Z, k z) = 2 * Fintype.card Z + B.card := by
    calc
      (∑ z : Z, k z) = ∑ z : Z, (2 + if k z = 3 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        exact hpoint z
      _ = (∑ _z : Z, 2) + ∑ z : Z, (if k z = 3 then 1 else 0) :=
        Finset.sum_add_distrib
      _ = 2 * Fintype.card Z + B.card := by
        rw [Finset.sum_const, Finset.sum_boole]
        simp [B, Nat.mul_comm]
  have hB : B.card = 16 := by omega
  have hcover : A ∪ B = Finset.univ := by
    ext z
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact iff_true_intro (hrange z)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    simp [A] at hzA
    simp [B] at hzB
    omega
  have hcards : A.card + B.card = Fintype.card Z := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]
  change A.card = 9 ∧ B.card = 16
  exact ⟨by omega, hB⟩

theorem card_fibers_zero_one_of_card_sum
    {U : Type*} [Fintype U] [DecidableEq U]
    (ell : U → ℕ)
    (hcard : Fintype.card U = 18)
    (hrange : ∀ u, ell u = 0 ∨ ell u = 1)
    (hsum : ∑ u, ell u = 15) :
    (Finset.univ.filter fun u => ell u = 0).card = 3 ∧
      (Finset.univ.filter fun u => ell u = 1).card = 15 := by
  let A := Finset.univ.filter fun u => ell u = 0
  let B := Finset.univ.filter fun u => ell u = 1
  have hpoint (u : U) : ell u = if ell u = 1 then 1 else 0 := by
    rcases hrange u with hu | hu <;> simp [hu]
  have hB : B.card = 15 := by
    have : (∑ u : U, ell u) = B.card := by
      calc
        (∑ u : U, ell u) = ∑ u : U, (if ell u = 1 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro u _
          exact hpoint u
        _ = B.card := by rw [Finset.sum_boole]; simp [B]
    omega
  have hcover : A ∪ B = Finset.univ := by
    ext u
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact iff_true_intro (hrange u)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u huA huB
    simp [A] at huA
    simp [B] at huB
    omega
  have hcards : A.card + B.card = Fintype.card U := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]
  change A.card = 3 ∧ B.card = 15
  exact ⟨by omega, hB⟩

/-- The support-zero miss degrees are `1^9, 3^16`. -/
theorem miss_profile_zero_side
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (k : Z → ℕ)
    (hcard : Fintype.card Z = 25)
    (hrange : ∀ z, k z = 2 ∨ k z = 3)
    (hsum : ∑ z, k z = 66) :
    (Finset.univ.filter fun z => 2 * k z - 3 = 1).card = 9 ∧
      (Finset.univ.filter fun z => 2 * k z - 3 = 3).card = 16 := by
  obtain ⟨h2, h3⟩ := card_fibers_two_three_of_card_sum k hcard hrange hsum
  have hfilter1 :
      (Finset.univ.filter fun z => 2 * k z - 3 = 1) =
        Finset.univ.filter fun z => k z = 2 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hrange z with hz | hz <;> simp [hz]
  have hfilter3 :
      (Finset.univ.filter fun z => 2 * k z - 3 = 3) =
        Finset.univ.filter fun z => k z = 3 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hrange z with hz | hz <;> simp [hz]
  rw [hfilter1, hfilter3, h2, h3]
  exact ⟨rfl, rfl⟩

/-- The support-one miss degrees are `3^15, 4^3`. -/
theorem miss_profile_one_side
    {U : Type*} [Fintype U] [DecidableEq U]
    (ell : U → ℕ)
    (hcard : Fintype.card U = 18)
    (hrange : ∀ u, ell u = 0 ∨ ell u = 1)
    (hsum : ∑ u, ell u = 15) :
    (Finset.univ.filter fun u => 4 - ell u = 3).card = 15 ∧
      (Finset.univ.filter fun u => 4 - ell u = 4).card = 3 := by
  obtain ⟨h0, h1⟩ := card_fibers_zero_one_of_card_sum ell hcard hrange hsum
  have hfilter3 :
      (Finset.univ.filter fun u => 4 - ell u = 3) =
        Finset.univ.filter fun u => ell u = 1 := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hrange u with hu | hu <;> simp [hu]
  have hfilter4 :
      (Finset.univ.filter fun u => 4 - ell u = 4) =
        Finset.univ.filter fun u => ell u = 0 := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hrange u with hu | hu <;> simp [hu]
  rw [hfilter3, hfilter4, h1, h0]
  exact ⟨rfl, rfl⟩

end Erdos85

#print axioms Erdos85.miss_profile_zero_side
#print axioms Erdos85.miss_profile_one_side
