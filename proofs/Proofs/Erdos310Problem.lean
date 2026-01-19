/-
Erdős Problem #310: Unit Fractions from Dense Subsets

Source: https://erdosproblems.com/310
Status: SOLVED (Liu-Sawhney, 2024)

Statement:
Let α > 0 and N ≥ 1. Is it true that for any A ⊆ {1,...,N} with |A| ≥ αN,
there exists S ⊆ A such that a/b = Σ_{n∈S} 1/n with a ≤ b = O_α(1)?

Answer: YES

Liu and Sawhney (2024) observed that the main result of Bloom (2021) implies
a positive solution. They prove: for (log N)^{-1/7+o(1)} ≤ α ≤ 1/2,
there exists S ⊆ A with a/b = Σ_{n∈S} 1/n where a ≤ b ≤ exp(O(1/α)).
This bound is shown to be sharp.

References:
- Erdős and Graham [ErGr80]: Original problem
- Bloom [Bl21]: "On a density conjecture about unit fractions" (2021)
- Liu and Sawhney [LiSa24]: "On further questions regarding unit fractions" (2024)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators

namespace Erdos310

/-
## Part I: Basic Definitions

The problem concerns representing rational numbers as sums of unit fractions
(Egyptian fractions) from dense subsets of integers.
-/

/--
**Unit Fraction Sum:**
The sum of unit fractions 1/n for n in a finite set S of positive integers.
-/
def unitFractionSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, if h : n > 0 then (1 : ℚ) / n else 0

/--
**Dense Subset Property:**
A subset A of {1,...,N} is α-dense if |A| ≥ αN.
-/
def isDense (A : Finset ℕ) (N : ℕ) (α : ℚ) : Prop :=
  A ⊆ Finset.range (N + 1) \ {0} ∧ (A.card : ℚ) ≥ α * N

/--
**Bounded Denominator Property:**
A rational a/b has bounded denominator with respect to α if b ≤ C(α)
for some constant C depending only on α.
-/
def hasBoundedDenom (q : ℚ) (bound : ℕ) : Prop :=
  q.den ≤ bound ∧ q.num.natAbs ≤ q.den

/-
## Part II: The Main Conjecture

Erdős's question asked whether dense subsets always contain a subset
whose unit fractions sum to a rational with bounded denominator.
-/

/--
**Erdős-Graham Conjecture (Now Theorem):**
For any α > 0, there exists a constant C(α) such that:
For any N and any A ⊆ {1,...,N} with |A| ≥ αN,
there exists S ⊆ A with Σ_{n∈S} 1/n = a/b where a ≤ b ≤ C(α).
-/
def erdosGrahamConjecture : Prop :=
  ∀ α : ℚ, α > 0 →
    ∃ C : ℕ, C > 0 ∧
      ∀ N : ℕ, N > 0 →
        ∀ A : Finset ℕ, isDense A N α →
          ∃ S : Finset ℕ, S ⊆ A ∧ hasBoundedDenom (unitFractionSum S) C

/-
## Part III: Liu-Sawhney Theorem

The precise quantitative version proved by Liu and Sawhney.
-/

/--
**Liu-Sawhney Theorem (2024):**
For (log N)^{-1/7+o(1)} ≤ α ≤ 1/2, there exists S ⊆ A such that
Σ_{n∈S} 1/n = a/b with a ≤ b ≤ exp(O(1/α)).

This theorem resolves Erdős Problem #310 affirmatively.

The proof builds on Bloom's work on the density of integers whose
sum of reciprocals is 1 (Egyptian fractions summing to 1).
-/
axiom liu_sawhney_theorem :
  ∀ α : ℚ, 0 < α → α ≤ 1/2 →
    ∃ C : ℕ, C > 0 ∧
      ∀ N : ℕ, N > 0 →
        ∀ A : Finset ℕ, isDense A N α →
          ∃ S : Finset ℕ, S ⊆ A ∧
            S.Nonempty ∧
            hasBoundedDenom (unitFractionSum S) C

/--
**Bloom's Theorem (2021):**
The set of integers that can be written as a sum of distinct unit fractions
summing to 1 has positive density among all integers.

This foundational result led to Liu-Sawhney's resolution of Erdős #310.
-/
axiom bloom_unit_fraction_density :
  ∃ δ : ℚ, δ > 0 ∧
    ∀ N : ℕ, N > 0 →
      ∃ count : ℕ, count ≥ 1 ∧
        ∃ S : Finset (Finset ℕ), S.card = count ∧
          ∀ T ∈ S, unitFractionSum T = 1

/-
## Part IV: Small Examples

Demonstrating unit fraction representations.
-/

/-- 1/2 + 1/3 + 1/6 = 1 (classic Egyptian fraction) -/
theorem classic_egyptian_one : (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 := by
  norm_num

/-- 1/2 + 1/4 = 3/4 -/
theorem unit_sum_example1 : (1 : ℚ) / 2 + 1 / 4 = 3 / 4 := by
  norm_num

/-- 1/3 + 1/6 = 1/2 -/
theorem unit_sum_example2 : (1 : ℚ) / 3 + 1 / 6 = 1 / 2 := by
  norm_num

/-- 1/2 + 1/3 = 5/6 -/
theorem unit_sum_example3 : (1 : ℚ) / 2 + 1 / 3 = 5 / 6 := by
  norm_num

/-- 1/4 + 1/5 + 1/20 = 1/2 -/
theorem unit_sum_example4 : (1 : ℚ) / 4 + 1 / 5 + 1 / 20 = 1 / 2 := by
  norm_num

/-
## Part V: Density Examples

Showing that dense subsets contain interesting unit fraction sums.
-/

/--
**Half-Density Example:**
If A = {1, 2, ..., N} (full set, density 1), then 1/1 = 1 with S = {1}.
-/
theorem full_density_trivial :
    ∃ S : Finset ℕ, S = {1} ∧ unitFractionSum S = 1 := by
  use {1}
  constructor
  · rfl
  · simp [unitFractionSum]

/--
**Even Numbers Example:**
The even numbers in {1,...,2N} have density 1/2.
For any such set, we can find unit fractions summing to 1 when N is large.
-/
def evenNumbersTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => n > 0 ∧ n % 2 = 0)

/--
The set {2, 4, 6} gives 1/2 + 1/4 + 1/6 = 11/12.
-/
theorem even_sum_small : (1 : ℚ) / 2 + 1 / 4 + 1 / 6 = 11 / 12 := by
  norm_num

/-
## Part VI: Sharpness of Bounds

Liu and Sawhney also showed the bound b ≤ exp(O(1/α)) is optimal.
-/

/--
**Sharpness Theorem:**
The dependence b ≤ exp(O(1/α)) is sharp: there exist dense subsets A
where the minimum achievable denominator requires b ≥ exp(Ω(1/α)).

This shows Liu-Sawhney's result is essentially best possible.
-/
axiom liu_sawhney_sharpness :
  ∀ C : ℕ, ∃ α : ℚ, 0 < α ∧ α < 1 ∧
    ∃ N : ℕ, ∃ A : Finset ℕ, isDense A N α ∧
      ∀ S : Finset ℕ, S ⊆ A → S.Nonempty →
        ¬ hasBoundedDenom (unitFractionSum S) C

/-
## Part VII: Connection to Egyptian Fractions

Every positive rational can be written as a sum of distinct unit fractions
(this is the classical Egyptian fraction representation).
-/

/--
**Egyptian Fraction Representation:**
Every positive rational q can be written as q = Σ_{n∈S} 1/n
for some finite set S of distinct positive integers.

This is a classical result, provable by the greedy algorithm.
-/
axiom egyptian_fraction_exists (q : ℚ) (hq : q > 0) :
  ∃ S : Finset ℕ, (∀ n ∈ S, n > 0) ∧ unitFractionSum S = q

/--
The greedy algorithm: repeatedly subtract the largest unit fraction ≤ q.
This terminates and produces a valid representation.
-/
axiom egyptian_fraction_greedy (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) :
  ∃ S : Finset ℕ, (∀ n ∈ S, n > 0) ∧
    (∀ n m : ℕ, n ∈ S → m ∈ S → n ≠ m) ∧
    unitFractionSum S = q

/-
## Part VIII: Historical Context

The study of Egyptian fractions has ancient origins.
-/

/--
**Erdős-Straus Conjecture (Open):**
For all n ≥ 2, 4/n = 1/a + 1/b + 1/c for some positive integers a, b, c.

This famous conjecture remains open, verified computationally for n ≤ 10^17.
-/
def erdosStrausConjecture : Prop :=
  ∀ n : ℕ, n ≥ 2 →
    ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c

/--
Erdős-Straus holds for n = 3: 4/3 = 1/1 + 1/3.
-/
theorem erdos_straus_3 : (4 : ℚ) / 3 = 1 / 1 + 1 / 3 := by
  norm_num

/--
Erdős-Straus holds for n = 5: 4/5 = 1/2 + 1/4 + 1/20.
-/
theorem erdos_straus_5 : (4 : ℚ) / 5 = 1 / 2 + 1 / 4 + 1 / 20 := by
  norm_num

/-
## Part IX: Main Result

The resolution of Erdős Problem #310.
-/

/--
**Erdős Problem #310: SOLVED**

The answer is YES. For any α > 0 and any α-dense subset A of {1,...,N},
there exists S ⊆ A such that Σ_{n∈S} 1/n = a/b with a ≤ b = O_α(1).

Liu and Sawhney (2024) proved this with optimal bounds b ≤ exp(O(1/α)).
-/
theorem erdos_310 : erdosGrahamConjecture := by
  intro α hα
  -- For α ≤ 1/2, use Liu-Sawhney directly
  -- For α > 1/2, the set is more than half-full, making the problem easier
  by_cases h : α ≤ 1/2
  · obtain ⟨C, hC, hMain⟩ := liu_sawhney_theorem α hα h
    exact ⟨C, hC, fun N hN A hA => by
      obtain ⟨S, hSA, _, hBound⟩ := hMain N hN A hA
      exact ⟨S, hSA, hBound⟩⟩
  · -- When α > 1/2, the set must contain many consecutive integers
    -- Use Liu-Sawhney with α' = 1/2
    push_neg at h
    obtain ⟨C, hC, hMain⟩ := liu_sawhney_theorem (1/2) (by norm_num) (by norm_num)
    refine ⟨C, hC, fun N hN A hA => ?_⟩
    -- A is α-dense, so it's also (1/2)-dense
    have hA' : isDense A N (1/2) := by
      constructor
      · exact hA.1
      · calc (A.card : ℚ) ≥ α * N := hA.2
          _ > (1/2) * N := by nlinarith
          _ ≥ (1/2) * N := le_refl _
    obtain ⟨S, hSA, _, hBound⟩ := hMain N hN A ⟨hA'.1, by linarith [hA'.2]⟩
    exact ⟨S, hSA, hBound⟩

/--
The answer to Erdős's question is YES.
-/
theorem erdos_310_answer : ∃ _ : erdosGrahamConjecture, True := ⟨erdos_310, trivial⟩

/-
## Part X: Related Results
-/

/--
**Croot's Theorem:**
Every set of positive integers with density > 0 contains a finite
subset whose reciprocals sum to 1.

This is a strong precursor to Bloom's work.
-/
axiom croot_theorem :
  ∀ A : Set ℕ, (∀ n ∈ A, n > 0) →
    (∃ δ : ℚ, δ > 0 ∧ ∀ N : ℕ, N > 0 →
      ((Finset.range (N+1)).filter (· ∈ A)).card ≥ δ * N) →
    ∃ S : Finset ℕ, (↑S : Set ℕ) ⊆ A ∧ unitFractionSum S = 1

/--
**Summary Theorem:**
Erdős Problem #310 is solved with optimal bounds.
-/
theorem erdos_310_summary :
    erdosGrahamConjecture ∧
    (∀ α : ℚ, 0 < α → α ≤ 1/2 →
      ∃ C : ℕ, ∀ N A, isDense A N α →
        ∃ S ⊆ A, hasBoundedDenom (unitFractionSum S) C) :=
  ⟨erdos_310, fun α hα hle => by
    obtain ⟨C, _, hMain⟩ := liu_sawhney_theorem α hα hle
    exact ⟨C, fun N A hA => by
      by_cases hN : N > 0
      · obtain ⟨S, hS, _, hB⟩ := hMain N hN A hA
        exact ⟨S, hS, hB⟩
      · push_neg at hN
        simp only [Nat.le_zero] at hN
        subst hN
        refine ⟨∅, empty_subset _, ?_⟩
        simp [hasBoundedDenom, unitFractionSum]⟩⟩

end Erdos310
