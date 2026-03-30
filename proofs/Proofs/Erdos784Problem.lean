/-
Erdős Problem #784: Sieving Sets with Bounded Reciprocal Sums

Source: https://erdosproblems.com/784
Status: SOLVED

Statement:
Let C > 0. Does there exist c > 0 (depending on C) such that, for all sufficiently
large x, if A ⊆ [1,x] has Σ_{n∈A} 1/n ≤ C then
  #{m ≤ x : a ∤ m for all a ∈ A} ≫ x/(log x)^c ?

Answer: YES for 0 < C ≤ 1, NO for C > 1.
- For C = 1: H₁(x) ≍ x/log x (Ruzsa 1982, Saias 1998)
- For C > 1: H_C(x) ≍ x^{e^{1-C}}/log x (Ruzsa, Weingartner 2025)

Known Results:
- Schinzel-Szekeres (1959): Shows polynomial bound is best possible
- Ruzsa (1982): Lower bound for C = 1 and negative answer for C > 1
- Saias (1998): Upper bound H₁(x) ≪ x/log x
- Weingartner (2025): Precise asymptotics for all C

Related: #542

Tags: sieve, divisibility, reciprocal-sums, number-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.SmoothNumbers

namespace Erdos784

open Nat Finset Real

/-
## Part 1: Basic Definitions

Reciprocal sums and the sieving function H_C(x).
-/

/-- The reciprocal sum of a set A -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (1 : ℝ) / n

/-- Elements of [1,x] not divisible by any element of A -/
def sievedSet (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (fun m => m ≥ 1 ∧ ∀ a ∈ A, ¬(a ∣ m))

/-- The count of elements not divisible by any element of A -/
def sievedCount (A : Finset ℕ) (x : ℕ) : ℕ :=
  (sievedSet A x).card

/-- H_C(x) = minimum sieved count over sets A ⊆ {2,...,x} with reciprocal sum ≤ C -/
noncomputable def H_C (C : ℝ) (x : ℕ) : ℕ :=
  -- Note: We exclude 1 from A to avoid trivial cases
  Finset.inf'
    ((Finset.range (x + 1)).powerset.filter
      (fun A => (∀ a ∈ A, 2 ≤ a) ∧ reciprocalSum A ≤ C))
    ⟨∅, by simp [reciprocalSum]⟩
    (fun A => sievedCount A x)

/-
## Part 2: The Question

Does x/(log x)^c lower bound exist?
-/

/-- The main question: Is H_C(x) ≫ x/(log x)^c for some c? -/
def HasPolynomialLogBound (C : ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ K : ℝ, K > 0 ∧
    ∀ x : ℕ, x ≥ 2 → (H_C C x : ℝ) ≥ K * x / (Real.log x) ^ c

/-
## Part 3: The Case C = 1

H₁(x) ≍ x/log x.
-/

/-- Ruzsa (1982): Lower bound for C = 1 -/
axiom ruzsa_1982_lower_bound :
    ∃ K : ℝ, K > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      (H_C 1 x : ℝ) ≥ K * x / Real.log x

/-- Saias (1998): Upper bound for C = 1 -/
axiom saias_1998_upper_bound :
    ∃ K : ℝ, K > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      (H_C 1 x : ℝ) ≤ K * x / Real.log x

/-- Combined: H₁(x) ≍ x/log x -/
theorem H_one_asymptotic :
    ∃ K₁ K₂ : ℝ, K₁ > 0 ∧ K₂ > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      K₁ * x / Real.log x ≤ (H_C 1 x : ℝ) ∧
      (H_C 1 x : ℝ) ≤ K₂ * x / Real.log x := by
  obtain ⟨K₁, hK₁, hlow⟩ := ruzsa_1982_lower_bound
  obtain ⟨K₂, hK₂, hup⟩ := saias_1998_upper_bound
  exact ⟨K₁, K₂, hK₁, hK₂, fun x hx => ⟨hlow x hx, hup x hx⟩⟩

/-- Weingartner's precise asymptotic: H₁(x) ~ c · x/log x where c ≈ 0.878 -/
/-
## Part 4: The Case 0 < C < 1

Trivial lower bound by union bound.
-/

/-- For C < 1, the union bound gives (1-C)x survivors.
    The sum of x/a over a ∈ A is at most x · Σ 1/a ≤ Cx,
    so at least (1-C)x elements survive (minus rounding). -/
/-- For 0 < C < 1, the answer is YES (trivially): any c works since the
    bound is actually linear, which dominates x/(log x)^c for any c > 0. -/
axiom positive_answer_small_C (C : ℝ) (hC : 0 < C) (hC2 : C < 1) :
    HasPolynomialLogBound C

/-
## Part 5: The Case C > 1

Ruzsa's negative answer: H_C(x) = x^{e^{1-C}+o(1)}.
-/

/-- For C > 1, the exponent α = e^{1-C} < 1 -/
noncomputable def alpha (C : ℝ) : ℝ := Real.exp (1 - C)

/-- For C > 1, α < 1 -/
theorem alpha_lt_one (C : ℝ) (hC : C > 1) : alpha C < 1 := by
  unfold alpha
  rw [Real.exp_lt_one_iff]
  linarith

/-- Ruzsa: For C > 1, H_C(x) = x^{α+o(1)} where α = e^{1-C} -/
/-- Weingartner (2025): Precise asymptotics for C > 1 -/
axiom weingartner_2025 (C : ℝ) (hC : C > 1) :
    ∃ K₁ K₂ : ℝ, K₁ > 0 ∧ K₂ > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      K₁ * (x : ℝ) ^ (alpha C) / Real.log x ≤ (H_C C x : ℝ) ∧
      (H_C C x : ℝ) ≤ K₂ * (x : ℝ) ^ (alpha C) / Real.log x

/-- For C > 1, the answer is NO: H_C(x) grows like x^α (α < 1),
    which is dominated by x/(log x)^c for any c > 0. -/
axiom negative_answer_large_C (C : ℝ) (hC : C > 1) :
    ¬HasPolynomialLogBound C

/-
## Part 6: Schinzel-Szekeres Example

Shows the polynomial bound is best possible.
-/

/-- The Schinzel-Szekeres construction (1959):
    For any c > 0, there exist sets A with reciprocal sum ≤ 1
    achieving sievedCount ≤ 2x/(log x)^c. This shows x/(log x)^c
    is the correct scale for the C = 1 lower bound. -/
/-
## Part 7: The Trivial Cases

When 1 ∈ A, everything is divisible.
-/

/-- If 1 ∈ A, then all elements are divisible by something in A -/
theorem one_in_A_trivial (A : Finset ℕ) (x : ℕ) (h1 : 1 ∈ A) :
    sievedCount A x = 0 := by
  unfold sievedCount sievedSet
  simp only [Finset.filter_eq_empty_iff, Finset.mem_range]
  intro m _
  push_neg
  intro _
  exact ⟨1, h1, one_dvd m⟩

/-- Hence we must assume 1 ∉ A for the problem to be interesting -/
def validSet (A : Finset ℕ) : Prop := ∀ a ∈ A, 2 ≤ a

/-
## Part 8: Connection to Dense Divisors

Related to other sieving problems.
-/

/-- Connection to Problem #542: the problem of dense divisors.
    Both problems study how the structure of a set of divisors
    (measured by reciprocal sums) controls sieving outcomes. -/
/-- The general principle: the reciprocal sum Σ 1/n of A controls
    how effectively A sieves [1,x]. The phase transition at C = 1
    separates linear-like behavior from sublinear behavior. -/
/-
## Part 9: Complete Answer
-/

/-- The complete characterization -/
theorem erdos_784_complete_answer (C : ℝ) (hC : C > 0) :
    (C ≤ 1 → HasPolynomialLogBound C) ∧
    (C > 1 → ¬HasPolynomialLogBound C) := by
  constructor
  · intro hC_le
    by_cases hC_eq : C = 1
    · -- C = 1 case
      rw [hC_eq]
      unfold HasPolynomialLogBound
      use 1
      constructor
      · norm_num
      · obtain ⟨K, hK, hbound⟩ := ruzsa_1982_lower_bound
        exact ⟨K, hK, hbound⟩
    · -- 0 < C < 1 case
      have hC_lt : C < 1 := lt_of_le_of_ne hC_le hC_eq
      exact positive_answer_small_C C hC hC_lt
  · exact negative_answer_large_C C

/-
## Part 10: Main Problem Statement
-/

/-- Erdős Problem #784: Complete statement -/
theorem erdos_784_statement :
    -- For C = 1: H₁(x) ≍ x/log x
    (∃ K₁ K₂ : ℝ, K₁ > 0 ∧ K₂ > 0 ∧ ∀ x : ℕ, x ≥ 2 →
      K₁ * x / Real.log x ≤ (H_C 1 x : ℝ) ∧
      (H_C 1 x : ℝ) ≤ K₂ * x / Real.log x) ∧
    -- For C > 1: H_C(x) ≍ x^{e^{1-C}}/log x
    (∀ C : ℝ, C > 1 →
      ∃ K₁ K₂ : ℝ, K₁ > 0 ∧ K₂ > 0 ∧ ∀ x : ℕ, x ≥ 2 →
        K₁ * (x : ℝ) ^ (alpha C) / Real.log x ≤ (H_C C x : ℝ) ∧
        (H_C C x : ℝ) ≤ K₂ * (x : ℝ) ^ (alpha C) / Real.log x) ∧
    -- The answer to the original question
    (∀ C : ℝ, C > 0 → C ≤ 1 → HasPolynomialLogBound C) ∧
    (∀ C : ℝ, C > 1 → ¬HasPolynomialLogBound C) := by
  constructor
  · exact H_one_asymptotic
  constructor
  · exact weingartner_2025
  constructor
  · intro C hC hC_le
    exact (erdos_784_complete_answer C hC).1 hC_le
  · intro C hC
    exact (erdos_784_complete_answer C hC).2 hC

/-- Summary of Erdős Problem #784 -/
theorem erdos_784_summary :
    -- The transition happens at C = 1
    -- YES for C ≤ 1, NO for C > 1
    (HasPolynomialLogBound 1) ∧
    (∀ C : ℝ, C > 1 → ¬HasPolynomialLogBound C) := by
  constructor
  · -- C = 1 has polynomial log bound
    unfold HasPolynomialLogBound
    use 1
    constructor
    · norm_num
    · obtain ⟨K, hK, hbound⟩ := ruzsa_1982_lower_bound
      exact ⟨K, hK, hbound⟩
  · exact negative_answer_large_C

end Erdos784
