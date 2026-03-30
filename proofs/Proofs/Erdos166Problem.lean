/-
Erdős Problem #166: Ramsey Number R(4,k) Lower Bound

Source: https://erdosproblems.com/166
Status: SOLVED (Mattheus-Verstraete 2023)
Prize: $250

Statement:
Prove that R(4,k) >> k³/(log k)^O(1).

Resolution:
Mattheus and Verstraete [MaVe23] proved R(4,k) >> k³/(log k)⁴,
resolving the conjecture and earning the $250 Erdős prize.

Historical Timeline:
- Spencer (1977): R(4,k) >> (k log k)^{5/2}
- Ajtai-Komlós-Szemerédi (1980): R(4,k) << k³/(log k)²
- Mattheus-Verstraete (2023): R(4,k) >> k³/(log k)⁴ [SOLVED]

References:
- Erdős [Er90b], [Er91], [Er93 p.339], [Er97c]: Original problem
- Spencer [Sp77]: Early lower bound
- Ajtai-Komlós-Szemerédi [AKS80]: Upper bound
- Mattheus-Verstraete [MaVe23]: Solution
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2

open Finset

namespace Erdos166

/- ## Part I: Ramsey Number Definitions -/

-- ramsey_3_3: unused axiom removed (never referenced by any theorem)
**R(4,4) = 18:**
Any 2-coloring of K_18 contains a monochromatic K_4.
Finding the exact value required extensive computation.
-/
-- ramsey_4_4: unused axiom removed (never referenced by any theorem)
**R(4,5) = 25:**
The largest exactly known off-diagonal Ramsey number with s = 4.
-/
-- ramsey_4_5: unused axiom removed (never referenced by any theorem)
**R(3,k) Bounds:**
The best known bounds for R(3,k) are
c₁ · k²/log k ≤ R(3,k) ≤ c₂ · k²/log k.
-/
-- ramsey_3_k_bounds: unused axiom removed (never referenced by any theorem)
**Spencer (1977):**
R(4,k) ≥ c · (k log k)^{5/2} for some constant c > 0.

This was the best lower bound for over 40 years, using
probabilistic constructions with dependent random choices.
-/
-- spencer_lower_bound: unused axiom removed (never referenced by any theorem)
**Ajtai-Komlós-Szemerédi (1980):**
R(4,k) ≤ C · k³/(log k)² for some constant C > 0.

This established that R(4,k) grows like k³ up to polylogarithmic factors.
The proof uses a clever greedy coloring algorithm.
-/
axiom aks_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≤ C * k^3 / (Real.log k)^2


/- ## Part VI: The Solution (Mattheus-Verstraete 2023) -/

/--
**Mattheus-Verstraete (2023):**
R(4,k) ≥ c · k³/(log k)⁴ for some constant c > 0.

This SOLVED Erdős Problem #166, earning the $250 prize.
The proof uses algebraic constructions from finite geometry.
-/
axiom mattheus_verstraete :
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≥ c * k^3 / (Real.log k)^4


/- ## Part VII: Erdős's Conjecture (SOLVED) -/

/--
**Erdős Problem #166 Statement:**
There exist constants c > 0 and A > 0 such that for all sufficiently large k,
R(4,k) ≥ c · k³/(log k)^A.

This asks for the lower bound to match the upper bound up to
polylogarithmic factors.
-/
def Erdos166Statement : Prop :=
  ∃ c : ℝ, ∃ A : ℝ, c > 0 ∧ A > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≥ c * k^3 / (Real.log k)^A

/--
**Erdős Problem #166 is SOLVED:**
Mattheus-Verstraete proves the statement with A = 4.
-/
theorem erdos_166_solved : Erdos166Statement := by
  obtain ⟨c, hc, hbound⟩ := mattheus_verstraete
  exact ⟨c, 4, hc, by norm_num, hbound⟩

/--
**Current Best Bounds for R(4,k):**
c · k³/(log k)⁴ ≤ R(4,k) ≤ C · k³/(log k)²

The gap is only in the exponent of log k (4 vs 2).
-/
theorem current_bounds :
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    c * k^3 / (Real.log k)^4 ≤ R(4, k) ∧
    (R(4, k) : ℝ) ≤ C * k^3 / (Real.log k)^2 := by
  obtain ⟨c, hc, hc_bound⟩ := mattheus_verstraete
  obtain ⟨C, hC, hC_bound⟩ := aks_upper_bound
  exact ⟨c, C, hc, hC, fun k hk => ⟨hc_bound k hk, hC_bound k hk⟩⟩

/- ## Part VIII: Summary -/

/--
**Summary of Erdős Problem #166:**

PROBLEM: Prove R(4,k) >> k³/(log k)^{O(1)}.

STATUS: SOLVED (Mattheus-Verstraete 2023)

PRIZE: $250 (collected)

ANSWER: YES. R(4,k) ≥ c · k³/(log k)⁴ for some c > 0.

KEY INSIGHT: Algebraic graph constructions from finite geometry
achieve bounds that probabilistic methods could not reach.

CURRENT BOUNDS:
- Lower: c · k³/(log k)⁴ ≤ R(4,k) [Mattheus-Verstraete 2023]
- Upper: R(4,k) ≤ C · k³/(log k)² [Ajtai-Komlós-Szemerédi 1980]
- Remaining gap: only the exponent of log k

HISTORICAL TIMELINE:
- 1977: Spencer proves R(4,k) >> (k log k)^{5/2}
- 1980: AKS proves R(4,k) << k³/(log k)²
- 2023: Mattheus-Verstraete proves R(4,k) >> k³/(log k)⁴ [SOLVED]

A breakthrough result bridging 43 years of effort in Ramsey theory.
-/
theorem erdos_166_status :
    -- Erdős Problem #166 is solved
    Erdos166Statement := erdos_166_solved

/--
**The bounds match up to logarithmic factors:**
Both lower and upper bounds are Θ(k³/(log k)^α) for some α.
-/
theorem logarithmic_gap :
    ∃ α β : ℝ, 2 ≤ α ∧ β ≤ 4 ∧
    ∀ k : ℕ, k ≥ 3 → ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      c * k^3 / (Real.log k)^β ≤ R(4, k) ∧
      (R(4, k) : ℝ) ≤ C * k^3 / (Real.log k)^α := by
  use 2, 4
  constructor
  · norm_num
  constructor
  · norm_num
  intro k hk
  obtain ⟨c, hc, hc_bound⟩ := mattheus_verstraete
  obtain ⟨C, hC, hC_bound⟩ := aks_upper_bound
  exact ⟨c, C, hc, hC, hc_bound k hk, hC_bound k hk⟩

end Erdos166
