/-
  Open Question: Growth Rate of Average Collatz Stopping Time

  The stopping time σ(n) of n is the number of Collatz steps until reaching 1.
  Define the average stopping time: S(N) = (1/N) Σ_{n=1}^{N} σ(n).

  Question: What is the growth rate of S(N)?

  Known:
  - Heuristic: σ(n) ≈ (6.95212...) · log₂ n (from probabilistic model)
  - Terras (1976): σ(n) < ∞ for almost all n (density 1 result)
  - Krasikov-Lagarias (2003): {n ≤ N : σ(n) < ∞} ≥ N^{0.84}

  Conjectured: S(N) ~ c · log N for some constant c.

  Tags: number-theory, collatz, stopping-time, average, growth-rate
-/

import Mathlib

open Nat Finset

namespace CollatzStoppingTime

/-
## Part I: Collatz Function and Stopping Time
-/

/-- The Collatz function -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iterate Collatz k times -/
def collatzIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatzIter k (collatz n)

/-- n reaches 1 within k steps -/
def reachesOneIn (n k : ℕ) : Prop :=
  collatzIter k n = 1

/-- n eventually reaches 1 -/
def reachesOne (n : ℕ) : Prop :=
  ∃ k, reachesOneIn n k

/-- The stopping time: minimum steps to reach 1 (if it does) -/
noncomputable def stoppingTime (n : ℕ) : ℕ :=
  if h : reachesOne n then Nat.find h else 0

/-- Stopping time of 1 is 0 -/
theorem stoppingTime_one : stoppingTime 1 = 0 := by
  unfold stoppingTime
  simp [reachesOne, reachesOneIn, collatzIter]
  split
  · exact Nat.find_eq_zero.mpr rfl
  · rfl

/-- Stopping time of 2 is 1 -/
theorem stoppingTime_two : stoppingTime 2 = 1 := by
  unfold stoppingTime
  have h : reachesOne 2 := ⟨1, by unfold reachesOneIn collatzIter collatz; norm_num⟩
  simp [h]
  exact Nat.find_eq_iff.mpr ⟨by unfold reachesOneIn collatzIter collatz; norm_num,
    fun k hk => by interval_cases k; unfold reachesOneIn collatzIter; norm_num⟩

/-
## Part II: Average Stopping Time
-/

/-- Sum of stopping times up to N (conditional on reaching 1) -/
noncomputable def totalStoppingTime (N : ℕ) : ℕ :=
  ∑ n in range N, stoppingTime (n + 1)

/-- Average stopping time up to N -/
noncomputable def avgStoppingTime (N : ℕ) : ℝ :=
  if N = 0 then 0 else (totalStoppingTime N : ℝ) / (N : ℝ)

/-
## Part III: Heuristic Growth Rate

The probabilistic heuristic: each Collatz step either halves (p=1/2)
or multiplies by 3/2 (p=1/2). Net multiplicative change per step:
(1/2 · 3/2)^{1/2} = √(3/4) < 1.

Expected steps to reach 1 from n: log₂ n / log₂(4/3) ≈ 6.95 · log₂ n.
-/

/-- The heuristic constant: 1 / log₂(4/3) -/
noncomputable def heuristicConstant : ℝ :=
  1 / (Real.log (4/3) / Real.log 2)

/-- The heuristic average: σ(n) ≈ c · log₂ n -/
def heuristicGrowthRate : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |avgStoppingTime N / Real.log N - heuristicConstant / Real.log 2| < ε

/-
## Part IV: Known Density Results
-/

/-- The Collatz conjecture: every n ≥ 1 reaches 1 -/
def collatzConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → reachesOne n

/-- Terras (1976): almost all n reach 1 (density 1) -/
axiom terras_density :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((range N).filter (fun n => reachesOne (n + 1))).card ≥
        ((1 - ε) * N : ℝ).toNat

/-
## Part V: The Open Question

What is the growth rate of S(N)?
-/

/-- The average stopping time grows at most logarithmically (if conjecture holds) -/
def logarithmicGrowth : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ N : ℕ, N ≥ 2 → c * Real.log N ≤ avgStoppingTime N ∧
      avgStoppingTime N ≤ C * Real.log N

/-- The open question: is S(N) ~ c · log N? -/
def avgStoppingTimeAsymptotic : Prop :=
  ∃ c : ℝ, c > 0 ∧ Filter.Tendsto
    (fun N => avgStoppingTime N / Real.log N)
    Filter.atTop (nhds c)

/-- If the average is logarithmic, the constant should be heuristicConstant -/
def exactConstant : Prop :=
  Filter.Tendsto
    (fun N => avgStoppingTime N / Real.log N)
    Filter.atTop (nhds (heuristicConstant / Real.log 2))

/-
## Part VI: Concrete Values
-/

/-- σ(1) = 0, σ(2) = 1, σ(3) = 7, σ(4) = 2, σ(5) = 5, σ(6) = 8 -/
-- These can be verified by computation

/-- The average for small N grows roughly logarithmically -/
-- S(1) = 0, S(2) = 0.5, S(3) = 2.67, S(4) = 2.5, S(5) = 3.0, S(6) = 3.83

#check avgStoppingTimeAsymptotic
#check logarithmicGrowth
#check exactConstant

end CollatzStoppingTime
