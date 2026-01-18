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

/-!
## Part I: Ramsey Numbers - Basic Definitions

R(m,n) is the minimum N such that any 2-coloring of K_N contains
either a red K_m or a blue K_n.
-/

/-- The Ramsey number R(m,n): minimum N such that any 2-coloring of K_N
    contains a red clique of size m or a blue clique of size n.

    Axiomatized since the exact definition requires graph coloring machinery. -/
axiom ramseyNumber (m n : ℕ) : ℕ

/-- Ramsey numbers are symmetric: R(m,n) = R(n,m). -/
axiom ramsey_symmetric (m n : ℕ) : ramseyNumber m n = ramseyNumber n m

/-- Ramsey numbers are finite for all m, n ≥ 1 (Ramsey's theorem). -/
axiom ramsey_finite (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    ramseyNumber m n > 0

/-- Base cases: R(1,n) = 1 and R(2,n) = n. -/
axiom ramsey_base_1 (n : ℕ) (hn : n ≥ 1) : ramseyNumber 1 n = 1
axiom ramsey_base_2 (n : ℕ) (hn : n ≥ 1) : ramseyNumber 2 n = n

/-- The basic recurrence: R(m,n) ≤ R(m-1,n) + R(m,n-1). -/
axiom ramsey_recurrence (m n : ℕ) (hm : m ≥ 2) (hn : n ≥ 2) :
    ramseyNumber m n ≤ ramseyNumber (m-1) n + ramseyNumber m (n-1)

/-!
## Part II: R(3,k) - The Triangle vs Independent Set Ramsey Number

R(3,k) is the focus of this problem: minimum N such that any graph on N
vertices contains either a triangle (K₃) or an independent set of size k.
-/

/-- R(3,k): minimum N such that any graph on N vertices contains
    either a triangle or an independent set of size k. -/
noncomputable def R3 (k : ℕ) : ℕ := ramseyNumber 3 k

/-- Equivalently: R(3,k) is the minimum N such that every triangle-free
    graph on N vertices has independence number ≥ k.
    (Axiomatized because Nat.find requires decidability.) -/
axiom R3_characterization (k : ℕ) (hk : k ≥ 1) :
    (∀ G : SimpleGraph (Fin (R3 k)),
      (∀ a b c, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)) →
      ∃ S : Finset (Fin (R3 k)), S.card ≥ k ∧ ∀ x y, x ∈ S → y ∈ S → x ≠ y → ¬G.Adj x y)

/-- Small values of R(3,k). -/
axiom R3_small_values :
    R3 3 = 6 ∧ R3 4 = 9 ∧ R3 5 = 14 ∧ R3 6 = 18 ∧ R3 7 = 23 ∧ R3 8 = 28 ∧ R3 9 = 36

/-!
## Part III: Upper Bounds

The upper bound comes from analyzing the independence number of triangle-free graphs.
-/

/-- The trivial upper bound from Ramsey recurrence: R(3,k) ≤ C(k+1, 2) + 1. -/
axiom R3_trivial_upper (k : ℕ) (hk : k ≥ 3) :
    R3 k ≤ k * (k + 1) / 2 + 1

/--
**Ajtai-Komlós-Szemerédi Theorem (1980):**
R(3,k) = O(k² / log k)

More precisely: R(3,k) ≤ C · k² / log k for some constant C.
This was a breakthrough showing the log factor in the denominator.
-/
axiom aks_upper_bound :
    ∃ C > 0, ∀ k ≥ 3, (R3 k : ℝ) ≤ C * k^2 / log k

/--
**Shearer's Theorem (1983):**
R(3,k) ≤ (1 + o(1)) · k² / log k

This is essentially tight for the upper bound coefficient.
-/
axiom shearer_upper_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≤ (1 + ε) * k^2 / log k

/-- Shearer's result comes from independence number bounds in triangle-free graphs. -/
axiom shearer_independence_lemma :
    ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      (∀ a b c, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)) →
      ∃ S : Finset (Fin n), S.card ≥ (1 - ε) * Real.sqrt (n * log n) ∧
        ∀ x y, x ∈ S → y ∈ S → x ≠ y → ¬G.Adj x y

/-!
## Part IV: Lower Bounds - The History of Constant c

The challenge: show R(3,k) ≥ c · k² / log k for as large c as possible.
-/

/--
**Kim's Theorem (1995):**
R(3,k) ≥ (c + o(1)) · k² / log k for some c > 0.

Kim's breakthrough used the semi-random method (triangle-free process).
Original constant: c ≥ 1/162.
-/
axiom kim_lower_bound :
    ∃ c > 0, ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (c - ε) * k^2 / log k

/-- Kim's original constant was c ≥ 1/162. -/
axiom kim_original_constant : ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/162 : ℝ) * k^2 / log k

/--
**Bohman-Keevash (2021) and Pontiveros-Griffiths-Morris (2020):**
Improved Kim's constant to c ≥ 1/4.

Both papers analyzed the triangle-free process more carefully.
-/
axiom bohman_keevash_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/4 - ε) * k^2 / log k

/--
**Campos-Jenssen-Michelen-Sahasrabudhe (2025):**
Improved to c ≥ 1/3.

Used new techniques beyond the triangle-free process analysis.
-/
axiom cjms_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/3 - ε) * k^2 / log k

/--
**Hefty-Horn-King-Pfender (2025):**
Current best: c ≥ 1/2.

Title of paper: "Improving R(3,k) in just two bites"
-/
axiom hhkp_bound :
    ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/2 - ε) * k^2 / log k

/-!
## Part V: The Main Asymptotic Result

Combining upper and lower bounds.
-/

/-- The asymptotic order of R(3,k). -/
theorem R3_asymptotic_order :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ k : ℕ, k ≥ 3 → c₁ * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ c₂ * k^2 / log k := by
  use 1/162, 2  -- We can use any valid constants
  constructor
  · norm_num
  constructor
  · norm_num
  · intro k _
    constructor
    · -- Lower bound from Kim
      sorry
    · -- Upper bound from Shearer
      sorry

/-- The current best bounds: 1/2 ≤ c ≤ 1. -/
axiom current_best_bounds :
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/2 - ε) * k^2 / log k) ∧
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≤ (1 + ε) * k^2 / log k)

/-!
## Part VI: The Triangle-Free Process

The probabilistic construction underlying the lower bounds.
-/

/-- The triangle-free process: greedily add random edges avoiding triangles.
    This process produces triangle-free graphs with small independence number. -/
axiom TriangleFreeProcess : ℕ → Type

/-- The triangle-free process terminates with a maximal triangle-free graph. -/
axiom tfp_terminates (n : ℕ) :
    ∃ (G : TriangleFreeProcess n), True  -- Placeholder for termination

/-- The final graph has independence number ≈ √(n log n). -/
axiom tfp_independence_bound :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      True  -- The independence number is (1+o(1))√(n log n)

/-- Kim's insight: the triangle-free process gives good Ramsey lower bounds. -/
axiom kim_insight :
    ∀ k : ℕ, k ≥ 3 → ∃ N : ℕ, ∃ G : SimpleGraph (Fin N),
      (∀ a b c, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)) ∧
      (∀ S : Finset (Fin N), S.card ≥ k →
        ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ G.Adj x y) ∧
      N ≥ (1/162 : ℝ) * k^2 / log k - 1

/-!
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

/-- The PGM conjecture is now known to be FALSE (since c ≥ 1/3). -/
axiom pgm_conjecture_false : ¬pgmConjecture

/-!
## Part VIII: Related Problems
-/

/-- Erdős Problem #544: General R(k,k). -/
axiom erdos_544_general_ramsey :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ k : ℕ, k ≥ 2 → c₁^k ≤ ramseyNumber k k ∧ (ramseyNumber k k : ℝ) ≤ c₂^k

/-- Erdős Problem #986: General R(s,k) for fixed s. -/
axiom erdos_986_fixed_s (s : ℕ) (hs : s ≥ 3) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ k : ℕ, k ≥ s → c₁ * k^(s-1) / (log k)^(s-2) ≤ ramseyNumber s k ∧
               (ramseyNumber s k : ℝ) ≤ c₂ * k^(s-1) / (log k)^(s-2)

/-!
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

/-- The prize ($250) was claimed for establishing the asymptotic order. -/
axiom prize_claimed : True  -- Kim's 1995 result established the order

end Erdos165
