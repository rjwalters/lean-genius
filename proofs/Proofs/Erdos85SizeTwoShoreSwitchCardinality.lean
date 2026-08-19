import Mathlib

/-! # Shore switching from cardinality profiles

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3.

This composes the signed-row census with the symbolic bipartition switch.
Unlike the first `mu=-5` specialization, all four cardinality parameters are
symbolic, so every cell in the `mu=-1,-3,-5` switch tables can use it.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem signed_sum_eq_two_same_sub_card_local
    {X : Type*} [DecidableEq X]
    (F : Finset X) (s : X → ℤ) (x : X)
    (hx : s x = -1 ∨ s x = 1)
    (hF : ∀ y ∈ F, s y = -1 ∨ s y = 1) :
    ∑ y ∈ F, s y =
      (2 * ((F.filter fun y ↦ s y = s x).card : ℤ) - (F.card : ℤ)) * s x := by
  classical
  let P : X → Prop := fun y ↦ s y = s x
  have hsame : ∑ y ∈ F.filter P, s y =
      ((F.filter P).card : ℤ) * s x := by
    calc
      ∑ y ∈ F.filter P, s y = ∑ _y ∈ F.filter P, s x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (Finset.mem_filter.mp hy).2
      _ = ((F.filter P).card : ℤ) * s x := by simp
  have hopp : ∑ y ∈ F.filter (fun y ↦ ¬ P y), s y =
      -((F.filter (fun y ↦ ¬ P y)).card : ℤ) * s x := by
    calc
      ∑ y ∈ F.filter (fun y ↦ ¬ P y), s y =
          ∑ _y ∈ F.filter (fun y ↦ ¬ P y), -s x := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyF := (Finset.mem_filter.mp hy).1
        have hyne := (Finset.mem_filter.mp hy).2
        rcases hx with hx | hx <;> rcases hF y hyF with hsy | hsy
        all_goals simp only [P] at hyne
        all_goals omega
      _ = -((F.filter (fun y ↦ ¬ P y)).card : ℤ) * s x := by simp
  have hcard := Finset.card_filter_add_card_filter_not (s := F) P
  rw [← Finset.sum_filter_add_sum_filter_not F P, hsame]
  change _ + (∑ y ∈ F.filter (fun y ↦ ¬ P y), s y) = _
  rw [hopp]
  rw [show F.filter (fun y ↦ s y = s x) = F.filter P by rfl]
  ring_nf
  have hcardZ : ((F.filter P).card : ℤ) +
      ((F.filter (fun y ↦ ¬ P y)).card : ℤ) = (F.card : ℤ) := by
    exact_mod_cast hcard
  rw [← hcardZ]
  ring

private theorem bipartition_signSwitch_eigen_sub_local
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hcover : ∀ x, D.neighborFinset x ⊆ A ∪ B)
    (s : X → ℤ) (p q : ℤ)
    (hAA : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = p * s x)
    (hABsum : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = q * s x)
    (hBB : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = p * s x)
    (hBAsum : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = q * s x) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    ∀ x ∈ A ∪ B, ∑ y ∈ D.neighborFinset x, t y = (p - q) * t x := by
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
      rcases Finset.mem_union.mp (hcover x hy) with hyA | hyB
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
  · have hxnotB : x ∉ B := fun hxB ↦ Finset.disjoint_left.mp hAB hxA hxB
    rw [hsplit, Finset.sum_union hfilters]
    have hsumA : ∑ y ∈ (D.neighborFinset x).filter (· ∈ A),
        (if y ∈ B then -s y else s y) =
        ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyA := (Finset.mem_filter.mp hy).2
      simp [fun hyB ↦ Finset.disjoint_left.mp hAB hyA hyB]
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
      simp [fun hyB ↦ Finset.disjoint_left.mp hAB hyA hyB]
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

/-- Equal diagonal and cross cardinality profiles on two shores determine
the switched eigenvalue directly. -/
theorem bipartition_signSwitch_eigen_sub_of_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hcover : ∀ x, D.neighborFinset x ⊆ A ∪ B)
    (s : X → ℤ) (diagCard diagSame crossCard crossSame : ℕ)
    (hsign : ∀ x ∈ A ∪ B, s x = -1 ∨ s x = 1)
    (hAAcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ A)).card = diagCard)
    (hAAsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hABcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ B)).card = crossCard)
    (hABsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = crossSame)
    (hBBcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ B)).card = diagCard)
    (hBBsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hBAcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ A)).card = crossCard)
    (hBAsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = crossSame) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    ∀ x ∈ A ∪ B, ∑ y ∈ D.neighborFinset x, t y =
      ((2 * (diagSame : ℤ) - diagCard) -
        (2 * (crossSame : ℤ) - crossCard)) * t x := by
  apply bipartition_signSwitch_eigen_sub_local D A B hAB hcover s
  · intro x hx
    rw [signed_sum_eq_two_same_sub_card_local _ s x
      (hsign x (Finset.mem_union_left B hx))]
    · rw [hAAcard x hx, hAAsame x hx]
    · intro y hy
      exact hsign y (Finset.mem_union_left B (Finset.mem_filter.mp hy).2)
  · intro x hx
    rw [signed_sum_eq_two_same_sub_card_local _ s x
      (hsign x (Finset.mem_union_left B hx))]
    · rw [hABcard x hx, hABsame x hx]
    · intro y hy
      exact hsign y (Finset.mem_union_right A (Finset.mem_filter.mp hy).2)
  · intro x hx
    rw [signed_sum_eq_two_same_sub_card_local _ s x
      (hsign x (Finset.mem_union_right A hx))]
    · rw [hBBcard x hx, hBBsame x hx]
    · intro y hy
      exact hsign y (Finset.mem_union_right A (Finset.mem_filter.mp hy).2)
  · intro x hx
    rw [signed_sum_eq_two_same_sub_card_local _ s x
      (hsign x (Finset.mem_union_right A hx))]
    · rw [hBAcard x hx, hBAsame x hx]
    · intro y hy
      exact hsign y (Finset.mem_union_left B (Finset.mem_filter.mp hy).2)

end

end Erdos85

#print axioms Erdos85.bipartition_signSwitch_eigen_sub_of_card
