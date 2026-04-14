/-
# OQ-01: R(Q_n) ≪ 2^n — Hypercube Ramsey Number Conjecture

**Open Question from Erdős #181:** Is R(Q_n) ≪ 2^n?

The Burr-Erdős conjecture states that the Ramsey number of Q_n (the n-dimensional
hypercube) is at most linear in the vertex count 2^n.

## Answer: OPEN

This file formalizes:
1. A corrected Ramsey definition using symmetric (undirected) colorings
2. **PROVED:** R_sym(Q_1) = 2 — exact Ramsey number for the 1-cube (0 sorries)
3. **PROVED:** R_sym(Q_n) ≥ 2^n — trivial lower bound (conditional on non-emptiness)
4. The main conjecture R_sym(Q_n) ≪ 2^n as an axiom (open problem)

## Note on Definitions

The parent proof uses directed colorings c : Fin N → Fin N → Fin 2. For undirected
Ramsey theory, we require c(i,j) = c(j,i). This file uses `ramseyNumberSymm` with
the symmetric coloring constraint to correctly model undirected Ramsey numbers.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Erdos181OQ01

/-!
## Part I: Hypercube Graph
-/

/-- Two vertices of Q_n are adjacent iff they differ in exactly one bit position. -/
def hypercubeAdj (n : ℕ) (x y : Fin (2 ^ n)) : Prop :=
  ∃! i : Fin n, (x.val / 2 ^ i.val) % 2 ≠ (y.val / 2 ^ i.val) % 2

/-- Hypercube adjacency is symmetric. -/
lemma hypercubeAdj_symm (n : ℕ) (x y : Fin (2 ^ n)) :
    hypercubeAdj n x y → hypercubeAdj n y x := by
  intro ⟨i, hi, huniq⟩
  exact ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩

/-- Hypercube adjacency is irreflexive. -/
lemma hypercubeAdj_irrefl (n : ℕ) (x : Fin (2 ^ n)) :
    ¬ hypercubeAdj n x x := by
  intro ⟨i, hi, _⟩; exact hi rfl

/-- For Q_1, adjacency of x and y is equivalent to x ≠ y. -/
lemma hypercubeAdj_one_iff (x y : Fin 2) :
    hypercubeAdj 1 x y ↔ x ≠ y := by
  constructor
  · intro h; exact fun heq => hypercubeAdj_irrefl 1 x (heq ▸ h)
  · intro hne
    fin_cases x <;> fin_cases y <;>
    first
    | exact absurd rfl hne
    | exact ⟨⟨0, by norm_num⟩, by decide,
             fun j _ => by ext; have := j.isLt; omega⟩

/-!
## Part II: Symmetric Ramsey Number (Correct Undirected Definition)
-/

/-- The symmetric Ramsey set: N satisfies the Ramsey property for Q_n
    under symmetric (undirected) colorings. -/
def symmRamseySet (n : ℕ) : Set ℕ :=
  {N : ℕ | ∀ c : Fin N → Fin N → Fin 2,
    (∀ i j : Fin N, c i j = c j i) →
    ∃ f : Fin (2 ^ n) → Fin N, Function.Injective f ∧
      ∃ color : Fin 2, ∀ x y : Fin (2 ^ n),
        hypercubeAdj n x y → c (f x) (f y) = color}

/-- The Ramsey number for Q_n using symmetric (undirected) colorings. -/
noncomputable def ramseyNumberSymm (n : ℕ) : ℕ := sInf (symmRamseySet n)

/-!
## Part III: Trivial Lower Bound
-/

/-- If N < 2^n, no injective map from Fin(2^n) to Fin N exists (pigeonhole). -/
lemma no_small_embedding (n N : ℕ) (hN : N < 2 ^ n)
    {f : Fin (2 ^ n) → Fin N} (hf : Function.Injective f) : False := by
  have h := Fintype.card_le_of_injective f hf
  simp [Fintype.card_fin] at h
  omega

/-- If the symmetric Ramsey set for Q_n is non-empty, R_sym(Q_n) ≥ 2^n. -/
theorem ramseyNumberSymm_ge (n : ℕ) (hne : (symmRamseySet n).Nonempty) :
    ramseyNumberSymm n ≥ 2 ^ n := by
  unfold ramseyNumberSymm
  apply le_csInf hne
  intro M hM
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf, _⟩ := hM (fun _ _ => 0) (fun _ _ => rfl)
  exact no_small_embedding n M hlt hf

/-!
## Part IV: R_sym(Q_1) = 2
-/

/-- 2 is in the symmetric Ramsey set for Q_1. -/
theorem two_in_symm_ramsey_set : (2 : ℕ) ∈ symmRamseySet 1 := by
  unfold symmRamseySet
  simp only [Set.mem_setOf_eq]
  intro c hsymm
  refine ⟨id, Function.injective_id, c ⟨0, by norm_num⟩ ⟨1, by norm_num⟩, ?_⟩
  intro x y hxy
  rw [hypercubeAdj_one_iff] at hxy
  fin_cases x <;> fin_cases y <;> simp_all [Function.id]

/-- R_sym(Q_1) ≤ 2 since 2 is in the symmetric Ramsey set. -/
theorem ramseyNumberSymm_one_le : ramseyNumberSymm 1 ≤ 2 := by
  unfold ramseyNumberSymm
  exact Nat.sInf_le two_in_symm_ramsey_set

/-- R_sym(Q_1) ≥ 2 since the symmetric Ramsey set is non-empty. -/
theorem ramseyNumberSymm_one_ge : ramseyNumberSymm 1 ≥ 2 :=
  ramseyNumberSymm_ge 1 ⟨2, two_in_symm_ramsey_set⟩

/-- **Main result: R_sym(Q_1) = 2.**
    The Ramsey number of the 1-cube (= K_2, a single edge) under symmetric
    colorings is exactly 2. This is the base case of the Burr-Erdős conjecture. -/
theorem ramseyNumberSymm_one : ramseyNumberSymm 1 = 2 :=
  le_antisymm ramseyNumberSymm_one_le ramseyNumberSymm_one_ge

/-!
## Part V: The Open Conjecture
-/

/-- **Tikhomirov (2022):** R_sym(Q_n) ≤ C · 2^{(2-c)n} for c ≈ 0.0366. (AXIOM) -/
axiom tikhomirov_2022_symm :
  ∃ (c : ℝ), 0 < c ∧ ∃ (C : ℝ), 0 < C ∧
    ∀ n : ℕ, (ramseyNumberSymm n : ℝ) ≤ C * (2 : ℝ) ^ ((2 - c) * n)

/-- **Burr-Erdős Conjecture (OQ-01):** R_sym(Q_n) ≪ 2^n. (OPEN) -/
axiom erdos_181_conjecture_symm :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (ramseyNumberSymm n : ℝ) ≤ C * (2 : ℝ) ^ n

/-- If the conjecture holds, R_sym(Q_n) / 2^n is bounded. -/
theorem conjecture_implies_bounded_ratio :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (ramseyNumberSymm n : ℝ) ≤ C * (2 : ℝ) ^ n) →
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, n ≥ 1 →
      (ramseyNumberSymm n : ℝ) / (2 : ℝ) ^ n ≤ B := by
  intro ⟨C, hC, hbound⟩
  refine ⟨C, hC, fun n _ => ?_⟩
  rw [div_le_iff (by positivity)]
  linarith [hbound n]

/-!
## Summary

**Proved (0 sorries):**
- `ramseyNumberSymm_one : ramseyNumberSymm 1 = 2`
- `ramseyNumberSymm_ge` — lower bound R_sym(Q_n) ≥ 2^n (conditional)

**Open:**
- `erdos_181_conjecture_symm` — main conjecture R_sym(Q_n) ≤ C · 2^n
- Exact values of R_sym(Q_2), R_sym(Q_3)
- Improving Tikhomirov exponent c ≈ 0.036 toward 1
-/
theorem erdos_181_oq01_summary :
    ramseyNumberSymm 1 = 2 ∧
    (symmRamseySet 1).Nonempty ∧
    ramseyNumberSymm 1 ≥ 2 ^ 1 :=
  ⟨ramseyNumberSymm_one, ⟨2, two_in_symm_ramsey_set⟩, ramseyNumberSymm_one_ge⟩

end Erdos181OQ01
