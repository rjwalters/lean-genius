import Proofs.Erdos85RootedTriangleCyclicCount

/-!
# A cyclic factor-three lemma for a unique distinguished sector

If a cyclically rotation-invariant triple census contains exactly one vertex
of a distinguished set in every triple, then one third of its ordered triples
have that vertex in the first position.
-/

namespace Erdos85

noncomputable section

/-- A rotation-invariant ordered triple census with exactly one `S`-vertex
has three times as many triples as its first-root fiber. -/
theorem card_eq_three_mul_card_filter_first_of_cyclic_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset (V × V × V)) (S : Set V) [DecidablePred (· ∈ S)]
    (hrotate : ∀ p : V × V × V,
      p ∈ T ↔ (p.2.2, p.1, p.2.1) ∈ T)
    (hunique : ∀ p ∈ T,
      (p.1 ∈ S ∧ p.2.2 ∉ S ∧ p.2.1 ∉ S) ∨
      (p.1 ∉ S ∧ p.2.2 ∈ S ∧ p.2.1 ∉ S) ∨
      (p.1 ∉ S ∧ p.2.2 ∉ S ∧ p.2.1 ∈ S)) :
    T.card = 3 * (T.filter fun p => p.1 ∈ S).card := by
  classical
  let F₀ := T.filter fun p => p.1 ∈ S
  let F₁ := T.filter fun p => p.2.2 ∈ S
  let F₂ := T.filter fun p => p.2.1 ∈ S
  have hcard₀₂ : F₀.card = F₂.card := by
    apply Finset.card_bij (fun p _ => (p.2.2, p.1, p.2.1))
    · intro p hp
      simp only [F₀, Finset.mem_filter] at hp
      simp only [F₂, Finset.mem_filter]
      exact ⟨(hrotate p).mp hp.1, hp.2⟩
    · intro p hp q hq hpq
      rcases p with ⟨x, z, y⟩
      rcases q with ⟨x', z', y'⟩
      simp only at hpq
      cases hpq
      rfl
    · intro q hq
      refine ⟨(q.2.1, q.2.2, q.1), ?_, ?_⟩
      · simp only [F₂, Finset.mem_filter] at hq
        simp only [F₀, Finset.mem_filter]
        have hmem : (q.2.1, q.2.2, q.1) ∈ T := by
          apply (hrotate (q.2.1, q.2.2, q.1)).mpr
          simpa using hq.1
        exact ⟨hmem, hq.2⟩
      · rcases q with ⟨x, z, y⟩
        rfl
  have hcard₀₁ : F₀.card = F₁.card := by
    apply Finset.card_bij (fun p _ => (p.2.1, p.2.2, p.1))
    · intro p hp
      simp only [F₀, Finset.mem_filter] at hp
      simp only [F₁, Finset.mem_filter]
      have hmem : (p.2.1, p.2.2, p.1) ∈ T := by
        apply (hrotate (p.2.1, p.2.2, p.1)).mpr
        simpa using hp.1
      exact ⟨hmem, hp.2⟩
    · intro p hp q hq hpq
      rcases p with ⟨x, z, y⟩
      rcases q with ⟨x', z', y'⟩
      simp only at hpq
      cases hpq
      rfl
    · intro q hq
      refine ⟨(q.2.2, q.1, q.2.1), ?_, ?_⟩
      · simp only [F₁, Finset.mem_filter] at hq
        simp only [F₀, Finset.mem_filter]
        exact ⟨(hrotate q).mp hq.1, hq.2⟩
      · rcases q with ⟨x, z, y⟩
        rfl
  have hpartition : T.card = F₀.card + F₁.card + F₂.card := by
    rw [Finset.card_eq_sum_ones]
    have h₀ : F₀.card = ∑ p ∈ T, if p.1 ∈ S then 1 else 0 := by
      simp [F₀]
    have h₁ : F₁.card = ∑ p ∈ T, if p.2.2 ∈ S then 1 else 0 := by
      simp [F₁]
    have h₂ : F₂.card = ∑ p ∈ T, if p.2.1 ∈ S then 1 else 0 := by
      simp [F₂]
    rw [h₀, h₁, h₂, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rcases hunique p hp with h | h | h <;> simp [h.1, h.2.1, h.2.2]
  have hcard₁₀ : F₁.card = F₀.card := hcard₀₁.symm
  have hcard₂₀ : F₂.card = F₀.card := hcard₀₂.symm
  change T.card = 3 * F₀.card
  omega

end

end Erdos85

#print axioms Erdos85.card_eq_three_mul_card_filter_first_of_cyclic_unique
