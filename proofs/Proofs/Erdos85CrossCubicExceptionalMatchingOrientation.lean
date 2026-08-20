import Proofs.Erdos85CrossCubicExceptionalMatching

/-! # Orientation of the exceptional cross-shore matching -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
private theorem zmodEight_orientation_plusMinus_ne :
    ∀ i : ZMod 8, i - 1 ≠ i + 1 := by
  native_decide

/-- An edge meeting each of two displayed two-point shores once has one of
the four possible cross-shore supports. -/
theorem two_by_two_crossEdge_support_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u₀ u₁ v₀ v₁ : V)
    (hu : u₀ ≠ u₁) (hv : v₀ ≠ v₁)
    (huv : ∀ x ∈ ({u₀, u₁} : Finset V),
      ∀ y ∈ ({v₀, v₁} : Finset V), x ≠ y)
    (b : R.edgeFinset)
    (_hsub : b.1.toFinset ⊆ {u₀, u₁, v₀, v₁})
    (hU : (b.1.toFinset ∩ {u₀, u₁}).card = 1)
    (hV : (b.1.toFinset ∩ {v₀, v₁}).card = 1) :
    b.1.toFinset = {u₀, v₀} ∨ b.1.toFinset = {u₀, v₁} ∨
      b.1.toFinset = {u₁, v₀} ∨ b.1.toFinset = {u₁, v₁} := by
  classical
  have hux : (u₀ ∈ b.1.toFinset ∧ u₁ ∉ b.1.toFinset) ∨
      (u₀ ∉ b.1.toFinset ∧ u₁ ∈ b.1.toFinset) := by
    by_cases h₀ : u₀ ∈ b.1.toFinset <;>
      by_cases h₁ : u₁ ∈ b.1.toFinset
    · simp [h₀, h₁, hu] at hU
    · exact Or.inl ⟨h₀, h₁⟩
    · exact Or.inr ⟨h₀, h₁⟩
    · simp [h₀, h₁] at hU
  have hvx : (v₀ ∈ b.1.toFinset ∧ v₁ ∉ b.1.toFinset) ∨
      (v₀ ∉ b.1.toFinset ∧ v₁ ∈ b.1.toFinset) := by
    by_cases h₀ : v₀ ∈ b.1.toFinset <;>
      by_cases h₁ : v₁ ∈ b.1.toFinset
    · simp [h₀, h₁, hv] at hV
    · exact Or.inl ⟨h₀, h₁⟩
    · exact Or.inr ⟨h₀, h₁⟩
    · simp [h₀, h₁] at hV
  have support_eq (x y : V) (hx : x ∈ b.1.toFinset)
      (hy : y ∈ b.1.toFinset) (hxy : x ≠ y) :
      b.1.toFinset = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    · rw [R.card_toFinset_mem_edgeFinset b]
      simp [hxy]
  rcases hux with hu0 | hu1 <;> rcases hvx with hv0 | hv1
  · exact Or.inl (support_eq u₀ v₀ hu0.1 hv0.1
      (huv u₀ (by simp) v₀ (by simp)))
  · exact Or.inr (Or.inl (support_eq u₀ v₁ hu0.1 hv1.2
      (huv u₀ (by simp) v₁ (by simp))))
  · exact Or.inr (Or.inr (Or.inl (support_eq u₁ v₀ hu1.2 hv0.1
      (huv u₁ (by simp) v₀ (by simp)))))
  · exact Or.inr (Or.inr (Or.inr (support_eq u₁ v₁ hu1.2 hv1.2
      (huv u₁ (by simp) v₁ (by simp)))))

/-- The local value-five matching has one of exactly two orientations:
straight or crossed between the displayed shore pairs. -/
theorem h305_crossCubicExceptional_matching_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ k l, u k ≠ v l)
    (i j : ZMod 8) (M : Finset R.edgeFinset)
    (hcard : M.card = 2)
    (hinside : ∀ b ∈ M,
      b.1.toFinset ⊆ h305CrossCubicExceptionalCoordinates u v i j)
    (hsplit : ∀ b ∈ M,
      (b.1.toFinset ∩ {u (i - 1), u (i + 1)}).card = 1 ∧
      (b.1.toFinset ∩ {v (j - 1), v (j + 1)}).card = 1)
    (hunique : ∀ x ∈ h305CrossCubicExceptionalCoordinates u v i j,
      ∃! b : R.edgeFinset, b ∈ M ∧ x ∈ b.1.toFinset) :
    (∃ b₀ b₁, M = {b₀, b₁} ∧
      b₀.1.toFinset = {u (i - 1), v (j - 1)} ∧
      b₁.1.toFinset = {u (i + 1), v (j + 1)}) ∨
    (∃ b₀ b₁, M = {b₀, b₁} ∧
      b₀.1.toFinset = {u (i - 1), v (j + 1)} ∧
      b₁.1.toFinset = {u (i + 1), v (j - 1)}) := by
  classical
  let u₀ := u (i - 1); let u₁ := u (i + 1)
  let v₀ := v (j - 1); let v₁ := v (j + 1)
  have hu : u₀ ≠ u₁ := huinj.ne (zmodEight_orientation_plusMinus_ne i)
  have hv : v₀ ≠ v₁ := hvinj.ne (zmodEight_orientation_plusMinus_ne j)
  have huv : ∀ x ∈ ({u₀, u₁} : Finset V),
      ∀ y ∈ ({v₀, v₁} : Finset V), x ≠ y := by
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    all_goals intro hxy; exact hdisj _ _ (hx.symm.trans (hxy.trans hy))
  have hu0X : u₀ ∈ h305CrossCubicExceptionalCoordinates u v i j := by
    simp [u₀, h305CrossCubicExceptionalCoordinates]
  have hu1X : u₁ ∈ h305CrossCubicExceptionalCoordinates u v i j := by
    simp [u₁, h305CrossCubicExceptionalCoordinates]
  obtain ⟨b₀, hb₀, hb₀uniq⟩ := hunique u₀ hu0X
  obtain ⟨b₁, hb₁, hb₁uniq⟩ := hunique u₁ hu1X
  have hc₀ := two_by_two_crossEdge_support_cases R u₀ u₁ v₀ v₁
    hu hv huv b₀ (by simpa [u₀, u₁, v₀, v₁,
      h305CrossCubicExceptionalCoordinates] using hinside b₀ hb₀.1)
      (hsplit b₀ hb₀.1).1 (hsplit b₀ hb₀.1).2
  have hc₁ := two_by_two_crossEdge_support_cases R u₀ u₁ v₀ v₁
    hu hv huv b₁ (by simpa [u₀, u₁, v₀, v₁,
      h305CrossCubicExceptionalCoordinates] using hinside b₁ hb₁.1)
      (hsplit b₁ hb₁.1).1 (hsplit b₁ hb₁.1).2
  have huv00 : u₀ ≠ v₀ := huv u₀ (by simp) v₀ (by simp)
  have huv01 : u₀ ≠ v₁ := huv u₀ (by simp) v₁ (by simp)
  have huv10 : u₁ ≠ v₀ := huv u₁ (by simp) v₀ (by simp)
  have huv11 : u₁ ≠ v₁ := huv u₁ (by simp) v₁ (by simp)
  have hc₀' : b₀.1.toFinset = {u₀, v₀} ∨
      b₀.1.toFinset = {u₀, v₁} := by
    rcases hc₀ with h00 | h01 | h10 | h11
    · exact Or.inl h00
    · exact Or.inr h01
    · exfalso
      have hh := hb₀.2
      rw [h10] at hh
      simp [hu] at hh
      exact huv00 hh
    · exfalso
      have hh := hb₀.2
      rw [h11] at hh
      simp [hu] at hh
      exact huv01 hh
  have hc₁' : b₁.1.toFinset = {u₁, v₀} ∨
      b₁.1.toFinset = {u₁, v₁} := by
    rcases hc₁ with k00 | k01 | k10 | k11
    · exfalso
      have hh := hb₁.2
      rw [k00] at hh
      simp [hu.symm] at hh
      exact huv10 hh
    · exfalso
      have hh := hb₁.2
      rw [k01] at hh
      simp [hu.symm] at hh
      exact huv11 hh
    · exact Or.inl k10
    · exact Or.inr k11
  have hM : M = {b₀, b₁} := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      by_cases hbu : u₀ ∈ b.1.toFinset
      · simp [hb₀uniq b ⟨hb, hbu⟩]
      · have hs := (hsplit b hb).1
        have hbu1 : u₁ ∈ b.1.toFinset := by
          by_contra h
          simp [u₀, u₁, hbu, h] at hs
        simp [hb₁uniq b ⟨hb, hbu1⟩]
    · by_cases he : b₁ = b₀
      · rw [hcard]
        simp [he]
      · rw [hcard]
        rw [Finset.card_insert_of_notMem (by
          simpa using (fun h : b₀ = b₁ ↦ he h.symm))]
        simp
  have hbne : b₀ ≠ b₁ := by
    intro heq
    have hsingle : M.card = 1 := by simp [hM, heq]
    omega
  have hv0X : v₀ ∈ h305CrossCubicExceptionalCoordinates u v i j := by
    simp [v₀, h305CrossCubicExceptionalCoordinates]
  have hv1X : v₁ ∈ h305CrossCubicExceptionalCoordinates u v i j := by
    simp [v₁, h305CrossCubicExceptionalCoordinates]
  rcases hc₀' with h00 | h01 <;> rcases hc₁' with k10 | k11
  · obtain ⟨c, hc, hcuniq⟩ := hunique v₀ hv0X
    have e₀ : b₀ = c := hcuniq b₀ ⟨hb₀.1, by rw [h00]; simp⟩
    have e₁ : b₁ = c := hcuniq b₁ ⟨hb₁.1, by rw [k10]; simp⟩
    exact (hbne (e₀.trans e₁.symm)).elim
  · left
    exact ⟨b₀, b₁, hM, by simpa [u₀, v₀] using h00,
      by simpa [u₁, v₁] using k11⟩
  · right
    exact ⟨b₀, b₁, hM, by simpa [u₀, v₁] using h01,
      by simpa [u₁, v₀] using k10⟩
  · obtain ⟨c, hc, hcuniq⟩ := hunique v₁ hv1X
    have e₀ : b₀ = c := hcuniq b₀ ⟨hb₀.1, by rw [h01]; simp⟩
    have e₁ : b₁ = c := hcuniq b₁ ⟨hb₁.1, by rw [k11]; simp⟩
    exact (hbne (e₀.trans e₁.symm)).elim

end

end Erdos85

#print axioms Erdos85.two_by_two_crossEdge_support_cases
#print axioms Erdos85.h305_crossCubicExceptional_matching_orientation
