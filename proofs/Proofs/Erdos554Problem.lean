/-
Erdős Problem #554: Odd Cycle vs Triangle Ramsey Numbers

Erdős and Graham (1981) conjectured that for any n >= 2,
  lim (k -> infinity) R(C_{2n+1}; k) / R(K_3; k) = 0
where R(G; k) denotes the k-color Ramsey number of G (the least m
such that every k-coloring of E(K_m) contains a monochromatic G).

This says odd cycles are "much easier" to find monochromatically
than triangles as the number of colors grows. The conjecture is
OPEN even for the simplest case n = 2 (the pentagon C_5).

**Status**: OPEN (Erdős-Graham, 1981)
Reference: https://erdosproblems.com/554
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace Erdos554

/- ## Part I: Ramsey Number Framework -/

/-- The k-color Ramsey number R(G; k) for a graph characterized by its
    clique/cycle size parameter. This is the least m such that every
    k-coloring of E(K_m) contains a monochromatic copy of G.

    We axiomatize this as a function ℕ → ℕ → ℕ, since the full
    definition requires graph theory infrastructure beyond our scope. -/
axiom ramseyNumber (graphSize : ℕ) (k : ℕ) : ℕ

/-- R(K_3; k): the k-color Ramsey number of the triangle. -/
def triangleRamsey (k : ℕ) : ℕ := ramseyNumber 3 k

/-- R(C_{2n+1}; k): the k-color Ramsey number of the odd (2n+1)-cycle. -/
def oddCycleRamsey (n k : ℕ) : ℕ := ramseyNumber (2 * n + 1) k

/- ## Part II: The Conjecture -/

/-- **Erdős Problem #554 (Erdős-Graham, 1981):**
    For any n >= 2,
      lim (k -> infinity) R(C_{2n+1}; k) / R(K_3; k) = 0.

    Stated in rational arithmetic: for every rational epsilon > 0,
    there exists K_0 such that for all k >= K_0,
      R(C_{2n+1}; k) * epsilon_den < epsilon_num * R(K_3; k).

    This is OPEN even for n = 2 (the pentagon C_5). -/
def erdosConjecture554 : Prop :=
  ∀ n : ℕ, n ≥ 2 →
    ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        oddCycleRamsey n k * εDen < εNum * triangleRamsey k

/- ## Part III: Known Bounds -/

/-- **Triangle Ramsey lower bound (exponential):**
    R(K_3; k) >= 2^k for k >= 2. -/

/-- **Odd cycle Ramsey upper bound:**
    R(C_{2n+1}; k) <= (2n+1)^k for n >= 2, k >= 2. -/

/-- **Odd cycle Ramsey lower bound:**
    R(C_{2n+1}; k) >= k * (2n) + 1 for k >= 1, n >= 1. -/

/- ## Part IV: Classical 2-Color Results -/

/-- **2-color odd cycle Ramsey (Bondy-Erdős, 1973):**
    R(C_{2n+1}; 2) = 4n + 1 for n >= 2.

    This completely determines the 2-color case. The proof uses
    a Hamiltonian cycle argument in the Ramsey graph. -/
axiom two_color_odd_cycle :
  ∀ n : ℕ, n ≥ 2 → oddCycleRamsey n 2 = 4 * n + 1

/-- **2-color triangle Ramsey:**
    R(K_3; 2) = 6, the classical Ramsey number. -/
axiom two_color_triangle : triangleRamsey 2 = 6

/-- **Verification: the 2-color ratio is already small.**
    R(C_5; 2) / R(K_3; 2) = 9/6 = 1.5, while
    R(C_7; 2) / R(K_3; 2) = 13/6 ≈ 2.17.

    The conjecture says this ratio -> 0 as k -> infinity. -/
theorem two_color_pentagon_ratio :
  oddCycleRamsey 2 2 = 9 ∧ triangleRamsey 2 = 6 := by
  constructor
  · -- R(C_5; 2) = 4*2 + 1 = 9
    exact two_color_odd_cycle 2 (by norm_num)
  · exact two_color_triangle

/- ## Part V: The Pentagon Case -/

/-- **The simplest open case:** n = 2, i.e., the pentagon C_5.
    Even R(C_5; k) / R(K_3; k) -> 0 is unknown.

    This is the most natural test case for the conjecture. -/
def erdosConjecture554_Pentagon : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      oddCycleRamsey 2 k * εDen < εNum * triangleRamsey k

/-- The pentagon case implies the full conjecture for n = 2. -/
theorem pentagon_is_special_case :
  erdosConjecture554 → erdosConjecture554_Pentagon := by
  intro h εNum εDen hεN hεD
  exact h 2 (by norm_num) εNum εDen hεN hεD

/- ## Part VI: Relation to Graph Chromatic Number -/

/-- **General question (Erdős):**
    Is there a graph G with χ(G) = 3 such that
    R(G; k) / R(K_3; k) does NOT tend to 0?

    Problem #554 is a special case: it conjectures that
    odd cycles are NOT such counterexamples. -/
def erdos_question_chromatic_3 : Prop :=
  ∀ graphSize : ℕ, graphSize ≥ 5 →
    -- For "3-chromatic" graphs (represented by odd cycle size)
    ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ramseyNumber graphSize k * εDen < εNum * triangleRamsey k

/- ## Part VII: Summary -/

end Erdos554
