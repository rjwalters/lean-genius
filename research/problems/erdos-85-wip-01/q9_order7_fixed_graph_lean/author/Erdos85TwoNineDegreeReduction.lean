import Proofs.Erdos85GadgetDegreeSquares

/-!
# Degree-two-or-nine reduction for the order-seven fixed graph

The boundary inequality and the C₄-free degree moment bound restrict a
nonempty fixed graph to order 8 (ambient order 78), or order 3 or 10
(ambient order 80). Every vertex then has degree two. The hypotheses that
come from the automorphism action remain explicit in this counting lemma.
-/

namespace Erdos85

/-- The fixed-graph counting reduction used for order-seven automorphisms. -/
theorem two_nine_degrees_boundary_reduction
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {N : ℕ} (hN : N = 78 ∨ N = 80)
    (hhi : Fintype.card V ≤ 23)
    (hmod : Fintype.card V ≡ N [MOD 7])
    (hdegrees : ∀ v, G.degree v = 2 ∨ G.degree v = 9)
    (hboundary : 10 * Fintype.card V ≤ (∑ v : V, G.degree v) + N) :
    ((N = 78 ∧ Fintype.card V = 8) ∨
      (N = 80 ∧ (Fintype.card V = 3 ∨ Fintype.card V = 10))) ∧
    (∀ v, G.degree v = 2) := by
  classical
  have hlo : 3 ≤ Fintype.card V := by
    let v : V := Classical.choice inferInstance
    have hdeg := hdegrees v
    have hlt := G.degree_lt_card_verts v
    omega
  have hpoint : ∀ v : V, 10 * G.degree v ≤ 2 * (G.degree v).choose 2 + 18 := by
    intro v
    rcases hdegrees v with h | h <;> norm_num [h, Nat.choose]
  have hsum : 10 * (∑ v : V, G.degree v) ≤
      2 * (∑ v : V, (G.degree v).choose 2) + 18 * Fintype.card V := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using h
  have hcherry := sum_degree_choose_two_le_card_choose_two_of_not_containsC4 G hfree
  have hchoose := two_mul_choose_two (Fintype.card V)
  have hpred : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have hmoment : 83 * Fintype.card V ≤
      Fintype.card V * Fintype.card V + 10 * N := by
    nlinarith
  have hcases : (N = 78 ∧ Fintype.card V = 8) ∨
      (N = 80 ∧ (Fintype.card V = 3 ∨ Fintype.card V = 10)) := by
    change Fintype.card V % 7 = N % 7 at hmod
    rcases hN with rfl | rfl
    · have hc : Fintype.card V = 8 ∨ Fintype.card V = 15 ∨ Fintype.card V = 22 := by omega
      rcases hc with h | h | h
      · exact Or.inl ⟨rfl, h⟩
      · norm_num [h] at hmoment
      · norm_num [h] at hmoment
    · have hc : Fintype.card V = 3 ∨ Fintype.card V = 10 ∨ Fintype.card V = 17 := by omega
      rcases hc with h | h | h
      · exact Or.inr ⟨rfl, Or.inl h⟩
      · exact Or.inr ⟨rfl, Or.inr h⟩
      · norm_num [h] at hmoment
  refine ⟨hcases, ?_⟩
  intro v
  rcases hdegrees v with hv | hv
  · exact hv
  · have hlt := G.degree_lt_card_verts v
    have hcard : Fintype.card V = 10 := by
      rcases hcases with ⟨_, h⟩ | ⟨_, h | h⟩ <;> omega
    have hsum_lower : 27 ≤ ∑ w : V, G.degree w := by
      calc
        27 = ∑ w : V, (2 + if w = v then 7 else 0) := by
          simp [Finset.sum_add_distrib, hcard]
        _ ≤ ∑ w : V, G.degree w := by
          apply Finset.sum_le_sum
          intro w _
          by_cases hw : w = v
          · subst w
            simp [hv]
          · simp only [hw, if_false, add_zero]
            rcases hdegrees w with h | h <;> omega
    have hsum_upper : (∑ w : V, G.degree w) ≤ 27 := by
      norm_num [hcard, Nat.choose] at hcherry
      rw [hcard] at hsum
      omega
    have hhand := G.sum_degrees_eq_twice_card_edges
    omega

end Erdos85
