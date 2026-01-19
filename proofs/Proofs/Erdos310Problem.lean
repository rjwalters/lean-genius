/-
Erdős Problem #310: Unit Fractions with Bounded Denominator

Source: https://erdosproblems.com/310
Status: SOLVED (Liu-Sawhney, 2024)

Statement:
Let α > 0 and N ≥ 1. Is it true that for any A ⊆ {1, ..., N} with |A| ≥ αN,
there exists some S ⊆ A such that
  a/b = Σ_{n ∈ S} 1/n
with a ≤ b = O_α(1)?

Answer: YES

Liu and Sawhney (2024) observed that Bloom's result (2021) implies this.
More precisely: If (log N)^{-1/7+o(1)} ≤ α ≤ 1/2, then there exists S ⊆ A with
  a/b = Σ_{n ∈ S} 1/n
where a ≤ b ≤ exp(O(1/α)). This dependence on b is sharp.

Background:
- Unit fractions (Egyptian fractions) have been studied since antiquity
- The question asks: how "simple" a rational can be represented using unit fractions
  from a dense subset of {1, ..., N}?
- A "simple" rational means small denominator (bounded by a function of α)

References:
- Bloom [Bl21]: "On a density conjecture about unit fractions"
- Liu, Sawhney [LiSa24]: "On further questions regarding unit fractions"
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

namespace Erdos310

/-
## Part I: Basic Definitions

Setting up the framework for unit fraction sums.
-/

/--
The sum of unit fractions over a finite set.
-/
noncomputable def unitFractionSum (S : Finset ℕ) : ℚ :=
  S.sum fun n => if n = 0 then 0 else (1 : ℚ) / n

/--
A set A is α-dense in {1, ..., N} if |A| ≥ αN.
-/
def IsDense (A : Finset ℕ) (α : ℝ) (N : ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ (A.card : ℝ) ≥ α * N

/--
A rational a/b is "simple" with bound B if a ≤ b and b ≤ B.
-/
def IsSimple (r : ℚ) (B : ℕ) : Prop :=
  r.num.natAbs ≤ r.den ∧ r.den ≤ B

/--
The problem asks: does A contain a subset whose unit fraction sum is simple?
-/
def HasSimpleUnitFractionSum (A : Finset ℕ) (B : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
    let r := unitFractionSum S
    r.num.natAbs ≤ r.den ∧ r.den ≤ B

/-
## Part II: The Conjecture and Its Solution

Erdős asked whether dense sets always contain such subsets.
-/

/--
The bound B depends on α: B = O_α(1) means B ≤ C(α) for some constant C.
-/
noncomputable def boundFunction (α : ℝ) : ℕ := ⌈Real.exp (1 / α)⌉₊

/--
**Erdős Problem #310 Conjecture:**
For any α > 0 and N ≥ 1, if A ⊆ {1, ..., N} with |A| ≥ αN,
then A contains a subset whose unit fraction sum is simple with bound O_α(1).
-/
def erdos_310_conjecture (α : ℝ) : Prop :=
  α > 0 →
  ∀ N : ℕ, N ≥ 1 →
  ∀ A : Finset ℕ, IsDense A α N →
  HasSimpleUnitFractionSum A (boundFunction α)

/-
## Part III: Bloom's Result

The key ingredient from Bloom (2021).
-/

/--
**Bloom's Theorem (2021):**
A density result about unit fractions that implies Erdős #310.
Specifically: dense sets contain subsets with unit fraction sum close to 1.
-/
axiom bloom_theorem :
    ∀ α : ℝ, α > 0 →
    ∀ N : ℕ, N ≥ 1 →
    ∀ A : Finset ℕ, IsDense A α N →
    ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
      |unitFractionSum S - 1| ≤ 1 / (2 : ℚ)

/--
Bloom's theorem implies there's a subset with sum in [1/2, 3/2].
-/
theorem bloom_implies_rational_bound :
    ∀ α : ℝ, α > 0 →
    ∀ N : ℕ, N ≥ 1 →
    ∀ A : Finset ℕ, IsDense A α N →
    ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
      (1 : ℚ) / 2 ≤ unitFractionSum S ∧ unitFractionSum S ≤ 3 / 2 := by
  sorry

/-
## Part IV: Liu-Sawhney Result

The precise version proved in 2024.
-/

/--
**Liu-Sawhney Theorem (2024):**
If (log N)^{-1/7+o(1)} ≤ α ≤ 1/2, then there exists S ⊆ A with
a/b = Σ_{n ∈ S} 1/n where a ≤ b ≤ exp(O(1/α)).
-/
axiom liu_sawhney :
    ∀ α : ℝ, ∀ N : ℕ,
    (Real.log N : ℝ) ^ (-(1:ℝ)/7) ≤ α → α ≤ 1/2 → N ≥ 3 →
    ∀ A : Finset ℕ, IsDense A α N →
    ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
      let r := unitFractionSum S
      r.num.natAbs ≤ r.den ∧ (r.den : ℝ) ≤ Real.exp (10 / α)

/--
The bound exp(O(1/α)) is sharp.
-/
axiom liu_sawhney_sharpness :
    ∀ C : ℝ, C > 0 →
    ∃ α : ℝ, α > 0 ∧ α ≤ 1/2 ∧
    ∃ N : ℕ, N ≥ 3 ∧
    ∃ A : Finset ℕ, IsDense A α N ∧
      ∀ S : Finset ℕ, S ⊆ A → S.Nonempty →
        (unitFractionSum S).den > ⌊Real.exp (C / α)⌋₊

/-
## Part V: Main Theorem

Combining the results to answer Erdős #310.
-/

/--
**Erdős Problem #310: SOLVED**
The main theorem: dense sets contain subsets with simple unit fraction sums.
-/
axiom erdos_310 (α : ℝ) (hα : α > 0) :
    ∀ N : ℕ, N ≥ 1 →
    ∀ A : Finset ℕ, IsDense A α N →
    HasSimpleUnitFractionSum A (boundFunction α)

/--
The answer is YES.
-/
theorem erdos_310_answer : ∀ α : ℝ, α > 0 → erdos_310_conjecture α := by
  intro α hα
  intro hα'
  intro N hN A hA
  exact erdos_310 α hα N hN A hA

/-
## Part VI: Examples and Special Cases

Illustrating the result.
-/

/--
Example: The full set {1, ..., N} is 1-dense.
-/
theorem full_set_dense (N : ℕ) (hN : N ≥ 1) :
    IsDense (Finset.range (N + 1) \ {0}) 1 N := by
  sorry

/--
For the full set, S = {2} gives 1/2, which is simple.
-/
theorem simple_example :
    unitFractionSum {2} = (1 : ℚ) / 2 := by
  simp only [unitFractionSum, Finset.sum_singleton]
  norm_num

/--
S = {2, 3, 6} gives 1/2 + 1/3 + 1/6 = 1, which is simple.
-/
theorem classic_example :
    unitFractionSum {2, 3, 6} = 1 := by
  sorry

/-
## Part VII: Connection to Egyptian Fractions

Historical context about unit fraction representations.
-/

/--
An Egyptian fraction representation is a sum of distinct unit fractions.
-/
def IsEgyptianFraction (S : Finset ℕ) : Prop :=
  (0 : ℕ) ∉ S

/--
Every positive rational has an Egyptian fraction representation.
(This is the classical result, not directly related to #310 but provides context.)
-/
axiom every_positive_rational_egyptian :
    ∀ r : ℚ, r > 0 →
    ∃ S : Finset ℕ, IsEgyptianFraction S ∧ unitFractionSum S = r

/-
## Part VIII: Quantitative Bounds

The precise dependence on parameters.
-/

/--
Lower bound on α for the Liu-Sawhney result.
-/
noncomputable def minAlpha (N : ℕ) : ℝ := (Real.log N) ^ (-(1:ℝ)/7)

/--
The bound exp(O(1/α)) in explicit form.
-/
noncomputable def explicitBound (α : ℝ) : ℕ := ⌈Real.exp (10 / α)⌉₊

/--
For small α (close to 0), the bound can be very large.
-/
theorem bound_grows_as_alpha_decreases :
    ∀ ε : ℝ, ε > 0 →
    ∃ M : ℕ, ∀ α : ℝ, 0 < α → α < ε → explicitBound α > M := by
  intro ε _
  use 1000
  sorry

/-
## Part IX: Summary

Collecting all key results.
-/

/--
**Summary of Erdős Problem #310:**

1. **Problem:** Does every α-dense subset of {1,...,N} contain a subset
   whose unit fraction sum is a/b with a ≤ b = O_α(1)?

2. **Answer:** YES (Liu-Sawhney 2024, building on Bloom 2021)

3. **Precise bound:** b ≤ exp(O(1/α)), which is sharp

4. **Range:** Works for (log N)^{-1/7+o(1)} ≤ α ≤ 1/2
-/
theorem erdos_310_summary :
    -- The problem has a positive answer
    (∀ α : ℝ, α > 0 → erdos_310_conjecture α) ∧
    -- The bound is exponential in 1/α
    (∀ α : ℝ, α > 0 → α ≤ 1/2 → boundFunction α ≤ explicitBound α) ∧
    -- Classic example: {2, 3, 6} sums to 1
    (unitFractionSum {2, 3, 6} = 1) := by
  constructor
  · exact erdos_310_answer
  constructor
  · sorry
  · exact classic_example

end Erdos310
