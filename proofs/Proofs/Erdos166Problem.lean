/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5be09360-5388-4bc1-acdf-9f921b5a91ae

The following was proved by Aristotle:

- theorem ramsey_symmetric (s t : ℕ) : R(s, t) = R(t, s)

- theorem ramsey_one_left (t : ℕ) (ht : t ≥ 1) : R(1, t) = 1

- theorem ramsey_two_left (t : ℕ) (ht : t ≥ 2) : R(2, t) = t
-/

/-
  Erdős Problem #166: Ramsey Number R(4,k) Lower Bound

  Source: https://erdosproblems.com/166
  Status: SOLVED (Mattheus-Verstraete 2023)
  Prize: $250

  Statement:
  Prove that R(4,k) >> k³/(log k)^O(1).

  History:
  - Spencer (1977): R(4,k) >> (k log k)^{5/2}
  - Ajtai-Komlós-Szemerédi (1980): R(4,k) << k³/(log k)²
  - Mattheus-Verstraete (2023): R(4,k) >> k³/(log k)⁴

  This resolved Erdős's problem, earning the $250 prize.

  Reference: Mattheus, Verstraete (2023) "The asymptotics of r(4,t)"
-/

import Mathlib


open Finset SimpleGraph

namespace Erdos166

/-! ## Ramsey Numbers -/

/-- The Ramsey number R(s,t) is the minimum N such that any 2-coloring
    of edges of K_N contains a red K_s or blue K_t. -/
noncomputable def RamseyNumber (s t : ℕ) : ℕ :=
  sInf { N : ℕ | ∀ (c : Sym2 (Fin N) → Bool),
    (∃ S : Finset (Fin N), S.card = s ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = true) ∨
    (∃ T : Finset (Fin N), T.card = t ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c s(x, y) = false) }

/-- Notation: R(s,t) -/
notation "R(" s "," t ")" => RamseyNumber s t

/-! ## Basic Properties -/

/-- R(s,t) is symmetric. -/
theorem ramsey_symmetric (s t : ℕ) : R(s, t) = R(t, s) := by
  -- By definition of $R$, we have that $R(s, t)$ is the least integer $N$ such that any 2-coloring of the edges of $K_N$ contains a red $K_s$ or a blue $K_t$.
  simp [RamseyNumber];
  congr! 3;
  constructor <;> intro h c <;> specialize h ( fun x => !c x ) <;> aesop

/-- R(1,t) = 1 for all t ≥ 1. -/
theorem ramsey_one_left (t : ℕ) (ht : t ≥ 1) : R(1, t) = 1 := by
  -- Any 2-coloring of the edges of K_1 will result in K_1 having a red K_1 or a blue K_1.
  have h1 : ∀ c : (Sym2 (Fin 1) → Bool), (∃ S : Finset (Fin 1), S.card = 1 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c (Sym2.mk (x, y)) = true) ∨ (∃ T : Finset (Fin 1), T.card = t ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c (Sym2.mk (x, y)) = false) := by
    exact fun c => Or.inl ⟨ { 0 }, by simp +decide ⟩;
  refine' le_antisymm ( Nat.sInf_le h1 ) _;
  refine' le_csInf _ _;
  · exact ⟨ 1, h1 ⟩;
  · rintro ( _ | _ | N ) <;> simp +arith +decide;
    exact fun x => ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by simpa ) )

/-- R(2,t) = t for all t ≥ 2. -/
theorem ramsey_two_left (t : ℕ) (ht : t ≥ 2) : R(2, t) = t := by
  refine' le_antisymm _ _;
  · refine' Nat.sInf_le _;
    by_contra! h;
    norm_num +zetaDelta at *;
    obtain ⟨ c, hc ⟩ := h;
    obtain ⟨ x, hx ⟩ := hc.2 Finset.univ ( by simpa );
    obtain ⟨ y, hy, hxy, hyx ⟩ := hx.2; specialize hc; have := hc.1 { x, y } ; simp_all +decide ;
    simp_all +decide [ Sym2.eq_swap ];
  · refine' le_csInf _ _;
    · refine' ⟨ t + 1, fun c => _ ⟩;
      by_contra! h;
      -- If no two vertices are connected by a red edge, then all edges must be blue.
      have h_blue : ∀ x y : Fin (t + 1), x ≠ y → c s(x, y) = false := by
        intros x y hxy;
        have := h.1 { x, y } ; simp_all +decide [ Finset.card_insert_of_notMem ];
        cases this <;> simp_all +decide [ Sym2.eq_swap ];
      obtain ⟨ x, hx, y, hy, hxy, h ⟩ := h.2 ( Finset.univ.erase 0 ) ( by simp +decide [ Finset.card_erase_of_mem ( Finset.mem_univ ( 0 : Fin ( t + 1 ) ) ) ] ) ; aesop;
    · simp +zetaDelta at *;
      intro b hb; contrapose! hb;
      use fun _ => Bool.false;
      norm_num +zetaDelta at *;
      exact ⟨ fun x hx => by obtain ⟨ y, hy, z, hz, hyz ⟩ := Finset.one_lt_card.1 ( by linarith ) ; exact ⟨ y, hy, z, hz, hyz ⟩, fun x hx => by linarith [ show x.card ≤ b by exact le_trans ( Finset.card_le_univ _ ) ( by simpa ) ] ⟩

/-! ## Known Values -/

/-- R(3,3) = 6: Famous result. -/
axiom ramsey_3_3 : R(3, 3) = 6

/-- R(4,4) = 18. -/
axiom ramsey_4_4 : R(4, 4) = 18

/-- R(4,5) = 25. -/
axiom ramsey_4_5 : R(4, 5) = 25

/-- R(3,k) grows like k²/(log k). -/
axiom ramsey_3_k_bounds (k : ℕ) (hk : k ≥ 3) :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * k^2 / Real.log k ≤ R(3, k) ∧
    (R(3, k) : ℝ) ≤ c₂ * k^2 / Real.log k

/-! ## The Main Result (Erdős Problem #166) -/

/-- **Spencer (1977)**: R(4,k) >> (k log k)^{5/2}. -/
axiom spencer_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≥ c * (k * Real.log k)^(5/2 : ℝ)

/-- **Ajtai-Komlós-Szemerédi (1980)**: R(4,k) << k³/(log k)². -/
axiom aks_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≤ C * k^3 / (Real.log k)^2

/-- **Mattheus-Verstraete (2023)**: R(4,k) >> k³/(log k)⁴.
    This SOLVED Erdős Problem #166. -/
axiom mattheus_verstraete :
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≥ c * k^3 / (Real.log k)^4

/-! ## Erdős's Conjecture (SOLVED) -/

/-- Erdős Problem #166: R(4,k) >> k³/(log k)^{O(1)}.
    This is now a theorem thanks to Mattheus-Verstraete. -/
def Erdos166Statement : Prop :=
  ∃ c : ℝ, ∃ A : ℝ, c > 0 ∧ A > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≥ c * k^3 / (Real.log k)^A

/-- Erdős Problem #166 is SOLVED. -/
theorem erdos_166_solved : Erdos166Statement := by
  obtain ⟨c, hc, hbound⟩ := mattheus_verstraete
  exact ⟨c, 4, hc, by norm_num, hbound⟩

/-! ## Summary

**Problem Status: SOLVED** ($250 prize)

Erdős asked whether R(4,k) >> k³/(log k)^{O(1)}.

**Answer: YES** (Mattheus-Verstraete 2023)

They proved R(4,k) >> k³/(log k)⁴, matching the upper bound of
k³/(log k)² up to the exponent on the logarithm.

**Current Knowledge:**
- Lower: c · k³/(log k)⁴ ≤ R(4,k)
- Upper: R(4,k) ≤ C · k³/(log k)²
- Gap: The exponent on log k (2 vs 4)

References:
- Mattheus, S., Verstraete, J. (2023): "The asymptotics of r(4,t)"
- Spencer, J. (1977): Previous best lower bound
- Ajtai, Komlós, Szemerédi (1980): Upper bound
-/

end Erdos166