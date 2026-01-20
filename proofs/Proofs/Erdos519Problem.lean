/-
Erdős Problem #519: Power Sums of Complex Numbers

Source: https://erdosproblems.com/519
Status: SOLVED

Statement:
Let z₁, ..., zₙ ∈ ℂ with z₁ = 1. Must there exist an absolute constant c > 0
such that max_{1 ≤ k ≤ n} |∑ᵢ zᵢᵏ| > c?

Background:
This is Turán's power sum problem. The question asks whether there's always
some power k where the power sum is bounded away from 0, regardless of n
and the choice of zᵢ (subject to z₁ = 1).

Key Results:
- Turán: Proved the max is ≫ 1/n (not an absolute constant)
- Atkinson (1961): SOLVED - proved c = 1/6 suffices
- Biró (1994): Improved to c = 1/2
- Biró (2000): Further improved to c > 1/2

The optimal value is believed to be approximately 0.7 based on computation.

References:
- [At61b] Atkinson, "On sums of powers of complex numbers", 1961
- [Bi94] Biró, "On a problem of Turán concerning sums of powers...", 1994
- [Bi00] Biró, "An improved estimate in a power sum problem of Turán", 2000

Tags: complex-analysis, power-sums, turán
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

open Complex Finset

namespace Erdos519

/-!
## Part I: Basic Definitions
-/

/--
**Power Sum:**
The k-th power sum of complex numbers z₁, ..., zₙ is ∑ᵢ zᵢᵏ.
-/
noncomputable def powerSum (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ i, (z i) ^ k

/--
**Power Sum Magnitude:**
The absolute value of the k-th power sum.
-/
noncomputable def powerSumMagnitude (z : Fin n → ℂ) (k : ℕ) : ℝ :=
  Complex.abs (powerSum z k)

/--
**Maximum Power Sum:**
max_{1 ≤ k ≤ n} |∑ᵢ zᵢᵏ|
-/
noncomputable def maxPowerSum (n : ℕ) (z : Fin n → ℂ) : ℝ :=
  (Finset.range n).sup' (by simp) (fun k => powerSumMagnitude z (k + 1))

/--
**First Coordinate is 1:**
The constraint z₁ = 1.
-/
def hasFirstOne {n : ℕ} (z : Fin n → ℂ) (hn : n > 0) : Prop :=
  z ⟨0, hn⟩ = 1

/-!
## Part II: Turán's Original Result
-/

/--
**Turán's Lower Bound:**
The maximum power sum is at least c/n for some c > 0.
This was the original result, showing the max doesn't go to 0.
-/
axiom turan_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
    maxPowerSum n z ≥ c / n

/--
**The Question:**
Can we get an ABSOLUTE constant c, independent of n?
-/
def turanQuestion : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
    maxPowerSum n z > c

/-!
## Part III: Atkinson's Theorem (1961)
-/

/--
**Atkinson's Theorem:**
c = 1/6 suffices. This was the first proof of an absolute constant.
-/
axiom atkinson_theorem :
  ∀ n : ℕ, n ≥ 1 →
    ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
    maxPowerSum n z > 1/6

/--
**Corollary: Turán's Question is Answered YES:**
-/
theorem turan_question_yes : turanQuestion := by
  use 1/6
  constructor
  · norm_num
  · intro n hn z hz
    exact atkinson_theorem n hn z hz

/-!
## Part IV: Biró's Improvements
-/

/--
**Biró (1994):**
Improved the constant to c = 1/2.
-/
axiom biro_1994 :
  ∀ n : ℕ, n ≥ 1 →
    ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
    maxPowerSum n z > 1/2

/--
**Biró (2000):**
Further improved to some c > 1/2.
-/
axiom biro_2000 :
  ∃ c : ℝ, c > 1/2 ∧ ∀ n : ℕ, n ≥ 1 →
    ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
    maxPowerSum n z > c

/--
**Best Known Constant:**
Based on computation, the optimal c is approximately 0.7.
-/
axiom optimal_constant_conjecture :
  -- The optimal c is approximately 0.7
  -- This is based on computational evidence
  True

/-!
## Part V: Key Observations
-/

/--
**Trivial Case n = 1:**
When n = 1 and z₁ = 1, the power sum is always 1.
-/
theorem trivial_case_n1 : ∀ k : ℕ, k ≥ 1 →
    powerSum (fun _ : Fin 1 => (1 : ℂ)) k = 1 := by
  intro k hk
  simp [powerSum]
  ring

/--
**Why z₁ = 1 Matters:**
Without this constraint, one could take all zᵢ = 0, making all power sums 0.
The constraint z₁ = 1 ensures at least one term contributes 1ᵏ = 1.
-/
theorem why_first_one_matters :
  -- If z₁ = 1, then ∑zᵢᵏ includes the term 1ᵏ = 1
  ∀ n : ℕ, n ≥ 1 → ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
    ∀ k : ℕ, powerSum z k = 1 + ∑ i : {j : Fin n | j.val > 0}, (z i)^k := by
  sorry

/--
**Cancellation Challenge:**
The other terms can cancel the 1, but not too much if we choose k wisely.
-/
axiom cancellation_bounds : True

/-!
## Part VI: Special Cases
-/

/--
**Roots of Unity:**
If zᵢ are n-th roots of unity, the power sums exhibit periodic behavior.
-/
def nthRootsOfUnity (n : ℕ) : Fin n → ℂ :=
  fun k => Complex.exp (2 * Real.pi * Complex.I * k / n)

/--
**Power Sums of Roots of Unity:**
∑ ω^k where ω ranges over n-th roots of unity equals 0 unless n | k.
-/
axiom roots_of_unity_sum (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
  powerSum (nthRootsOfUnity n) k = if n ∣ k then n else 0

/--
**Implication for the Problem:**
Roots of unity don't satisfy z₁ = 1 in general (unless n-th root = 1).
The problem is more about arbitrary configurations.
-/
axiom roots_of_unity_note : True

/-!
## Part VII: Related Problem
-/

/--
**Problem #973:**
Related question about power sums with different constraints.
-/
def relatedProblem973 : Prop :=
  -- See Problem #973 for related questions
  True

/--
**Connection:**
Both problems explore how power sums of complex numbers behave
under various constraints.
-/
axiom problem_connection : True

/-!
## Part VIII: The Optimal Constant
-/

/--
**Lower Bound on Optimal c:**
We know c > 1/2 is achievable.
-/
theorem optimal_lower_bound :
    ∃ c : ℝ, c > 1/2 ∧ ∀ n : ℕ, n ≥ 1 →
      ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
      maxPowerSum n z > c :=
  biro_2000

/--
**Computational Evidence:**
Numerical experiments suggest c ≈ 0.7 is the optimal value.
-/
axiom computational_evidence :
  -- Experiments suggest the true optimal c ≈ 0.7
  True

/--
**Gap:**
The gap between c > 1/2 (proved) and c ≈ 0.7 (conjectured) remains.
-/
axiom gap_note : True

/-!
## Part IX: Summary
-/

/--
**Erdős Problem #519: SOLVED**

QUESTION: For z₁, ..., zₙ ∈ ℂ with z₁ = 1, is there an absolute c > 0
such that max_{k} |∑zᵢᵏ| > c?

ANSWER: YES

HISTORY:
- Turán: Proved max ≫ 1/n
- Atkinson (1961): Proved c = 1/6 works
- Biró (1994): Improved to c = 1/2
- Biró (2000): Improved to c > 1/2

OPTIMAL: Conjectured to be c ≈ 0.7 based on computation.
-/
theorem erdos_519 : turanQuestion := turan_question_yes

/--
**Summary theorem:**
-/
theorem erdos_519_summary :
    -- Atkinson's bound
    (∀ n : ℕ, n ≥ 1 → ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
      maxPowerSum n z > 1/6) ∧
    -- Biró's improved bound
    (∃ c : ℝ, c > 1/2 ∧ ∀ n : ℕ, n ≥ 1 →
      ∀ z : Fin n → ℂ, hasFirstOne z (by omega) →
      maxPowerSum n z > c) := by
  exact ⟨atkinson_theorem, biro_2000⟩

/--
**Historical note:**
This problem, originally posed by Turán, connects complex analysis
to combinatorial questions about power sums.
-/
theorem historical_note : True := trivial

end Erdos519
