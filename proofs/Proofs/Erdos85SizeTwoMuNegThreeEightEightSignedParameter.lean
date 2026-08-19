import Proofs.Erdos85SizeTwoMuNegThreeEightEightSignedRegularity

/-! # A single signed parameter for the `mu=-3` eight-plus-eight split -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- For an equal bipartition, constant internal same-sign degrees together
with a common global same-sign degree force the two constants to agree.
Equivalently both cross blocks have the same complementary signed degree. -/
theorem equal_bipartition_internalSame_constants_eq
    {X : Type*} [Fintype X] [DecidableEq X]
    (K : SimpleGraph X) [DecidableRel K.Adj]
    (s : X → ℤ) (A B : Finset X)
    (hcover : A ∪ B = Finset.univ) (hdisj : Disjoint A B)
    (hcardA : A.card = B.card) (hpos : 0 < A.card) (q ka kb : ℕ)
    (hglobal : ∀ x ∈ A ∪ B,
      ((K.neighborFinset x).filter fun y ↦ s y = s x).card = q)
    (hA : ∀ x ∈ A,
      (A.filter fun y ↦ K.Adj x y ∧ s y = s x).card = ka)
    (hB : ∀ x ∈ B,
      (B.filter fun y ↦ K.Adj x y ∧ s y = s x).card = kb) :
    ka = kb ∧
    (∀ x ∈ A,
      (B.filter fun y ↦ K.Adj x y ∧ s y = s x).card = q - ka) ∧
    (∀ x ∈ B,
      (A.filter fun y ↦ K.Adj x y ∧ s y = s x).card = q - kb) := by
  classical
  have split (x : X) :
      ((K.neighborFinset x).filter fun y ↦ s y = s x) =
        (A.filter fun y ↦ K.Adj x y ∧ s y = s x) ∪
        (B.filter fun y ↦ K.Adj x y ∧ s y = s x) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_union]
    constructor
    · rintro ⟨hxy, hs⟩
      have hy : y ∈ A ∪ B := by rw [hcover]; simp
      rcases Finset.mem_union.mp hy with hyA | hyB
      · exact Or.inl ⟨hyA, hxy, hs⟩
      · exact Or.inr ⟨hyB, hxy, hs⟩
    · rintro (⟨-, hxy, hs⟩ | ⟨-, hxy, hs⟩) <;> exact ⟨hxy, hs⟩
  have splitDisjoint (x : X) : Disjoint
      (A.filter fun y ↦ K.Adj x y ∧ s y = s x)
      (B.filter fun y ↦ K.Adj x y ∧ s y = s x) :=
    Finset.disjoint_filter_filter hdisj
  have hAcross : ∀ x ∈ A,
      (B.filter fun y ↦ K.Adj x y ∧ s y = s x).card = q - ka := by
    intro x hx
    have hg := hglobal x (Finset.mem_union_left B hx)
    rw [split x, Finset.card_union_of_disjoint (splitDisjoint x), hA x hx] at hg
    omega
  have hBcross : ∀ x ∈ B,
      (A.filter fun y ↦ K.Adj x y ∧ s y = s x).card = q - kb := by
    intro x hx
    have hg := hglobal x (Finset.mem_union_right A hx)
    rw [split x, Finset.card_union_of_disjoint (splitDisjoint x), hB x hx] at hg
    omega
  let EAB := A.sigma fun x ↦
    B.filter fun y ↦ K.Adj x y ∧ s y = s x
  let EBA := B.sigma fun y ↦
    A.filter fun x ↦ K.Adj y x ∧ s x = s y
  have hswap : EAB.card = EBA.card := by
    simpa [EAB, EBA, eq_comm, and_assoc, and_left_comm, and_comm] using
      sigma_cross_symmetric_card K A B (fun x y ↦ s y = s x) (by
        intro x y
        simp [eq_comm])
  have hABcard : EAB.card = A.card * (q - ka) := by
    dsimp only [EAB]
    rw [Finset.card_sigma]
    calc
      _ = ∑ _x ∈ A, (q - ka) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hAcross x hx
      _ = A.card * (q - ka) := by simp [Nat.mul_comm]
  have hBAcard : EBA.card = B.card * (q - kb) := by
    dsimp only [EBA]
    rw [Finset.card_sigma]
    calc
      _ = ∑ _x ∈ B, (q - kb) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hBcross x hx
      _ = B.card * (q - kb) := by simp [Nat.mul_comm]
  have hdiff : q - ka = q - kb := by
    rw [hABcard, hBAcard, hcardA] at hswap
    have hposB : 0 < B.card := by omega
    exact Nat.eq_of_mul_eq_mul_left hposB hswap
  have hka : ka ≤ q := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hg := hglobal x (Finset.mem_union_left B hx)
    have hi := hA x hx
    rw [split x, Finset.card_union_of_disjoint (splitDisjoint x), hi] at hg
    omega
  have hkb : kb ≤ q := by
    have hposB : 0 < B.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hposB
    have hg := hglobal x (Finset.mem_union_right A hx)
    have hi := hB x hx
    rw [split x, Finset.card_union_of_disjoint (splitDisjoint x), hi] at hg
    omega
  exact ⟨by omega, hAcross, hBcross⟩

end

end Erdos85

#print axioms Erdos85.equal_bipartition_internalSame_constants_eq
