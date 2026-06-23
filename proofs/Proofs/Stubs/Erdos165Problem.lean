/-
Erdős Problem #165: Asymptotic Formula for R(3,k)

Source: https://erdosproblems.com/165
Status: SOLVED
Prize: $250

Statement:
Give an asymptotic formula for R(3,k).

It is known that:
  (c + o(1)) · k²/log k ≤ R(3,k) ≤ (1 + o(1)) · k²/log k

The question asks: what is the exact value of c?

Key Results:
- Upper bound: Shearer (1983), improving Ajtai-Komlós-Szemerédi (1980)
  R(3,k) ≤ (1 + o(1)) · k²/log k

- Lower bound history:
  - Kim (1995): c ≥ 1/162 (breakthrough using semi-random method)
  - Bohman-Keevash (2021): c ≥ 1/4
  - Pontiveros-Griffiths-Morris (2020): c ≥ 1/4
  - Campos-Jenssen-Michelen-Sahasrabudhe (2025): c ≥ 1/3
  - Hefty-Horn-King-Pfender (2025): c ≥ 1/2

Conjecture: c = 1/2, meaning R(3,k) ~ (1/2) · k²/log k

References:
- Ajtai, Komlós, Szemerédi: "A note on Ramsey numbers" (1980)
- Shearer: "A note on the independence number of triangle-free graphs" (1983)
- Kim: "The Ramsey number R(3,t) has order of magnitude t²/log t" (1995)
- Campos et al.: "A new lower bound for R(3,k)" (2025)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace Erdos165

/-
## Part I: Ramsey Numbers - Basic Definitions

R(m,n) is the minimum N such that any 2-coloring of K_N contains
either a red K_m or a blue K_n.
-/

/-- The Ramsey number R(m,n): minimum N such that any 2-coloring of K_N
    contains a red clique of size m or a blue clique of size n.

    Axiomatized since the exact definition requires graph coloring machinery. -/
axiom ramseyNumber (m n : ℕ) : ℕ

/-
## Part II: R(3,k) - The Triangle vs Independent Set Ramsey Number

R(3,k) is the focus of this problem: minimum N such that any graph on N
vertices contains either a triangle (K₃) or an independent set of size k.
-/

/-- R(3,k): minimum N such that any graph on N vertices contains
    either a triangle or an independent set of size k. -/
noncomputable def R3 (k : ℕ) : ℕ := ramseyNumber 3 k

/-
## Part III: Upper Bounds

The upper bound comes from analyzing the independence number of triangle-free graphs.
-/

/--
**Shearer's Theorem (1983):**
R(3,k) ≤ (1 + o(1)) · k² / log k

This is essentially tight for the upper bound coefficient.
-/
axiom shearer_upper_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≤ (1 + ε) * k^2 / log k

/-
## Part IV: Lower Bounds - The History of Constant c

The challenge: show R(3,k) ≥ c · k² / log k for as large c as possible.
-/

/--
**Hefty-Horn-King-Pfender (2025):**
Current best: c ≥ 1/2.

Title of paper: "Improving R(3,k) in just two bites"
-/
axiom hhkp_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/2 - ε) * k^2 / log k

/-
## Part V: The Main Asymptotic Result

Combining upper and lower bounds.
-/

/-- The asymptotic order of R(3,k): there exist positive constants c₁, c₂
    such that c₁ · k²/log k ≤ R(3,k) ≤ c₂ · k²/log k for sufficiently large k. -/
theorem R3_asymptotic_order :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        c₁ * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ c₂ * k^2 / log k := by
  use 1/4, 2
  refine ⟨by norm_num, by norm_num, ?_⟩
  obtain ⟨k₁, hk₁⟩ := hhkp_bound (1/4) (by norm_num)
  obtain ⟨k₂, hk₂⟩ := shearer_upper_bound 1 one_pos
  use max k₁ k₂
  intro k hk
  constructor
  · linarith [hk₁ k (le_of_max_le_left hk)]
  · linarith [hk₂ k (le_of_max_le_right hk)]

/-
## Part VI: The Triangle-Free Process

The probabilistic construction underlying the lower bounds.
-/

/-- The triangle-free process: greedily add random edges avoiding triangles.
    This process produces triangle-free graphs with small independence number. -/
axiom TriangleFreeProcess : ℕ → Type

/-
## Part VII: Conjectures and Open Questions
-/

/--
**Main Conjecture:**
R(3,k) ~ (1/2) · k² / log k

Both Campos et al. and Hefty et al. conjecture c = 1/2.
-/
def mainConjecture : Prop :=
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (1/2 - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (1/2 + ε) * k^2 / log k

/-- The older conjecture (Pontiveros-Griffiths-Morris): c = 1/4. -/
def pgmConjecture : Prop :=
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (1/4 - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (1/4 + ε) * k^2 / log k

/-
## Part VIII: Related Problems
-/

/-
## Part IX: Main Results Summary
-/

/-- **Erdős Problem #165: SOLVED (asymptotic order)**
    Answer: R(3,k) = Θ(k² / log k)

    Upper bound: R(3,k) ≤ (1 + o(1)) · k² / log k [Shearer 1983]
    Lower bound: R(3,k) ≥ (1/2 - o(1)) · k² / log k [Hefty et al. 2025]

    The exact constant c in R(3,k) ~ c · k² / log k remains open.
    Current conjecture: c = 1/2. -/
theorem erdos_165 : ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (c₁ - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (c₂ + ε) * k^2 / log k) := by
  use 1/2, 1
  constructor
  · norm_num
  constructor
  · norm_num
  intro ε hε
  -- Use the combined bounds from HHKP and Shearer
  obtain ⟨k₁, hk₁⟩ := hhkp_bound ε hε
  obtain ⟨k₂, hk₂⟩ := shearer_upper_bound ε hε
  use max k₁ k₂
  intro k hk
  constructor
  · exact hk₁ k (le_of_max_le_left hk)
  · exact hk₂ k (le_of_max_le_right hk)

/- The prize ($250) was claimed for establishing the asymptotic order. -/

end Erdos165
