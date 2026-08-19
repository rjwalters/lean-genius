import Proofs.Erdos85SizeTwoMuNegFiveEightEightAllTriangleCases

/-! # Shore switching from the `mu=-5` to the `mu=3` C8+C8 branch -/

open Finset

namespace Erdos85

noncomputable section

/-- Negating a signed vector on one shore changes block row sums
`(-1,-4)` into eigenvalue three. -/
theorem bipartition_signSwitch_eigen_three
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hcover : ∀ x, D.neighborFinset x ⊆ A ∪ B)
    (s : X → ℤ)
    (hAA : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = -s x)
    (hABsum : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = -4 * s x)
    (hBB : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = -s x)
    (hBAsum : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = -4 * s x) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    ∀ x ∈ A ∪ B, ∑ y ∈ D.neighborFinset x, t y = 3 * t x := by
  classical
  dsimp only
  intro x hx
  have hsplit : D.neighborFinset x =
      (D.neighborFinset x).filter (· ∈ A) ∪
        (D.neighborFinset x).filter (· ∈ B) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hy
      have hyAB := hcover x hy
      rcases Finset.mem_union.mp hyAB with hyA | hyB
      · exact Or.inl ⟨hy, hyA⟩
      · exact Or.inr ⟨hy, hyB⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  have hfilters : Disjoint
      ((D.neighborFinset x).filter (· ∈ A))
      ((D.neighborFinset x).filter (· ∈ B)) := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    exact (Finset.disjoint_left.mp hAB)
      (Finset.mem_filter.mp hyA).2 (Finset.mem_filter.mp hyB).2
  rcases Finset.mem_union.mp hx with hxA | hxB
  · have hxnotB : x ∉ B := by
      intro hxB
      exact Finset.disjoint_left.mp hAB hxA hxB
    rw [hsplit, Finset.sum_union hfilters]
    have hsumA : ∑ y ∈ (D.neighborFinset x).filter (· ∈ A),
        (if y ∈ B then -s y else s y) =
        ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyA := (Finset.mem_filter.mp hy).2
      have hynotB : y ∉ B := by
        intro hyB
        exact Finset.disjoint_left.mp hAB hyA hyB
      simp [hynotB]
    have hsumB : ∑ y ∈ (D.neighborFinset x).filter (· ∈ B),
        (if y ∈ B then -s y else s y) =
        -∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      simp [(Finset.mem_filter.mp hy).2]
    rw [hsumA, hsumB, hAA x hxA, hABsum x hxA]
    simp [hxnotB]
    ring
  · rw [hsplit, Finset.sum_union hfilters]
    have hsumA : ∑ y ∈ (D.neighborFinset x).filter (· ∈ A),
        (if y ∈ B then -s y else s y) =
        ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyA := (Finset.mem_filter.mp hy).2
      have hynotB : y ∉ B := by
        intro hyB
        exact Finset.disjoint_left.mp hAB hyA hyB
      simp [hynotB]
    have hsumB : ∑ y ∈ (D.neighborFinset x).filter (· ∈ B),
        (if y ∈ B then -s y else s y) =
        -∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      simp [(Finset.mem_filter.mp hy).2]
    rw [hsumA, hsumB, hBAsum x hxB, hBB x hxB]
    simp [hxB]
    ring

end

end Erdos85

#print axioms Erdos85.bipartition_signSwitch_eigen_three
