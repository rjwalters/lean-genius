import Proofs.Erdos85MuNegThreeZeroFiveProfileMultiplicityLedger

/-! # Turning pointwise h305 service profiles into the multiplicity ledger -/

namespace Erdos85

private theorem threeProfile_card_and_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (tag value : α → ℕ)
    (w0 w1 w2 : ℕ)
    (h : ∀ a ∈ s, (tag a = 0 ∧ value a = w0) ∨
      (tag a = 1 ∧ value a = w1) ∨
      (tag a = 2 ∧ value a = w2)) :
    (s.filter fun a ↦ tag a = 0).card +
        (s.filter fun a ↦ tag a = 1).card +
        (s.filter fun a ↦ tag a = 2).card = s.card ∧
      ∑ a ∈ s, value a =
        w0 * (s.filter fun a ↦ tag a = 0).card +
        w1 * (s.filter fun a ↦ tag a = 1).card +
        w2 * (s.filter fun a ↦ tag a = 2).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hi := ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb))
      rcases h a (Finset.mem_insert_self a s) with h0 | h1 | h2
      · constructor
        · simp [Finset.filter_insert, ha, h0.1]
          omega
        · rw [Finset.sum_insert ha, h0.2, hi.2]
          simp [Finset.filter_insert, ha, h0.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h1.1]
          omega
        · rw [Finset.sum_insert ha, h1.2, hi.2]
          simp [Finset.filter_insert, ha, h1.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h2.1]
          omega
        · rw [Finset.sum_insert ha, h2.2, hi.2]
          simp [Finset.filter_insert, ha, h2.1]
          ring

private theorem fourProfile_card_and_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (tag value : α → ℕ)
    (w0 w1 w2 w3 : ℕ)
    (h : ∀ a ∈ s, (tag a = 0 ∧ value a = w0) ∨
      (tag a = 1 ∧ value a = w1) ∨
      (tag a = 2 ∧ value a = w2) ∨
      (tag a = 3 ∧ value a = w3)) :
    (s.filter fun a ↦ tag a = 0).card +
        (s.filter fun a ↦ tag a = 1).card +
        (s.filter fun a ↦ tag a = 2).card +
        (s.filter fun a ↦ tag a = 3).card = s.card ∧
      ∑ a ∈ s, value a =
        w0 * (s.filter fun a ↦ tag a = 0).card +
        w1 * (s.filter fun a ↦ tag a = 1).card +
        w2 * (s.filter fun a ↦ tag a = 2).card +
        w3 * (s.filter fun a ↦ tag a = 3).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hi := ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb))
      rcases h a (Finset.mem_insert_self a s) with h0 | h1 | h2 | h3
      · constructor
        · simp [Finset.filter_insert, ha, h0.1]
          omega
        · rw [Finset.sum_insert ha, h0.2, hi.2]
          simp [Finset.filter_insert, ha, h0.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h1.1]
          omega
        · rw [Finset.sum_insert ha, h1.2, hi.2]
          simp [Finset.filter_insert, ha, h1.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h2.1]
          omega
        · rw [Finset.sum_insert ha, h2.2, hi.2]
          simp [Finset.filter_insert, ha, h2.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h3.1]
          omega
        · rw [Finset.sum_insert ha, h3.2, hi.2]
          simp [Finset.filter_insert, ha, h3.1]
          ring

/-- The generic assembly step behind the h305 profile ledger.  Its inputs
are exactly the three local profile classifications, the three undirected
transition handshakes, the `12/24/12` population census, and the two middle
profile parities. -/
noncomputable def h305_profileMultiplicityLedger_of_pointwise
    {α : Type*} [DecidableEq α]
    (E2 E1 E0 : Finset α) (c2 c1 c0 : α → ℕ)
    (hcard2 : E2.card = 12) (hcard1 : E1.card = 24)
    (hcard0 : E0.card = 12)
    (hp2 : ∀ a ∈ E2,
      (c2 a = 0 ∧ c1 a = 4 ∧ c0 a = 2) ∨
      (c2 a = 1 ∧ c1 a = 2 ∧ c0 a = 3) ∨
      (c2 a = 2 ∧ c1 a = 0 ∧ c0 a = 4))
    (hp1 : ∀ a ∈ E1,
      (c2 a = 0 ∧ c1 a = 6 ∧ c0 a = 0) ∨
      (c2 a = 1 ∧ c1 a = 4 ∧ c0 a = 1) ∨
      (c2 a = 2 ∧ c1 a = 2 ∧ c0 a = 2) ∨
      (c2 a = 3 ∧ c1 a = 0 ∧ c0 a = 3))
    (hp0 : ∀ a ∈ E0,
      (c0 a = 0 ∧ c1 a = 4 ∧ c2 a = 2) ∨
      (c0 a = 1 ∧ c1 a = 2 ∧ c2 a = 3) ∨
      (c0 a = 2 ∧ c1 a = 0 ∧ c2 a = 4))
    (h21 : (∑ a ∈ E2, c1 a) = ∑ a ∈ E1, c2 a)
    (h10 : (∑ a ∈ E1, c0 a) = ∑ a ∈ E0, c1 a)
    (h20 : (∑ a ∈ E2, c0 a) = ∑ a ∈ E0, c2 a)
    (heven2 : Even ((E2.filter fun a ↦ c2 a = 1).card : ℕ))
    (heven0 : Even ((E0.filter fun a ↦ c0 a = 1).card : ℕ)) :
    H305ProfileMultiplicityLedger := by
  let u0 := (E2.filter fun a ↦ c2 a = 0).card
  let u1 := (E2.filter fun a ↦ c2 a = 1).card
  let u2 := (E2.filter fun a ↦ c2 a = 2).card
  let y0 := (E1.filter fun a ↦ c2 a = 0).card
  let y1 := (E1.filter fun a ↦ c2 a = 1).card
  let y2 := (E1.filter fun a ↦ c2 a = 2).card
  let y3 := (E1.filter fun a ↦ c2 a = 3).card
  let v0 := (E0.filter fun a ↦ c0 a = 0).card
  let v1 := (E0.filter fun a ↦ c0 a = 1).card
  let v2 := (E0.filter fun a ↦ c0 a = 2).card
  have hu1 := threeProfile_card_and_sum E2 c2 c1 4 2 0 (by
    intro a ha
    rcases hp2 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.1⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩))
  have hu0 := threeProfile_card_and_sum E2 c2 c0 2 3 4 (by
    intro a ha
    rcases hp2 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.2⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.2⟩))
  have hy2 := fourProfile_card_and_sum E1 c2 c2 0 1 2 3 (by
    intro a ha
    rcases hp1 a ha with h | h | h | h
    · exact Or.inl ⟨h.1, h.1⟩
    · exact Or.inr (Or.inl ⟨h.1, h.1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.1⟩)))
  have hy0 := fourProfile_card_and_sum E1 c2 c0 0 1 2 3 (by
    intro a ha
    rcases hp1 a ha with h | h | h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.2⟩)))
  have hv1 := threeProfile_card_and_sum E0 c0 c1 4 2 0 (by
    intro a ha
    rcases hp0 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.1⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩))
  have hv2 := threeProfile_card_and_sum E0 c0 c2 2 3 4 (by
    intro a ha
    rcases hp0 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.2⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.2⟩))
  refine {
    u0 := u0, u1 := u1, u2 := u2,
    y0 := y0, y1 := y1, y2 := y2, y3 := y3,
    v0 := v0, v1 := v1, v2 := v2
    u_total := ?_, y_total := ?_, v_total := ?_
    handshake_u_y := ?_, handshake_y_v := ?_, handshake_u_v := ?_
    u1_even := ?_, v1_even := ?_ }
  · simpa [u0, u1, u2, hcard2] using hu1.1
  · simpa [y0, y1, y2, y3, hcard1] using hy2.1
  · simpa [v0, v1, v2, hcard0] using hv1.1
  · dsimp [u0, u1, y1, y2, y3]
    have hs := hu1.2.symm.trans (h21.trans hy2.2)
    omega
  · dsimp [v0, v1, y1, y2, y3]
    have hs := hy0.2.symm.trans (h10.trans hv1.2)
    omega
  · dsimp [u0, u1, u2, v0, v1, v2]
    rw [← hu0.2, h20, hv2.2]
  · simpa [u1] using heven2
  · simpa [v1] using heven0

end Erdos85
