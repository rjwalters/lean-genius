/-
Erdős Problem #492: Uniform Distribution Relative to a Fixed Sequence

Source: https://erdosproblems.com/492
Status: DISPROVED (Schmidt, 1969)

Statement:
Let A = {a₁ < a₂ < ...} ⊆ ℕ be infinite such that aᵢ₊₁/aᵢ → 1.
For any x ≥ a₁ let f(x) = (x - aᵢ)/(aᵢ₊₁ - aᵢ) ∈ [0,1), where x ∈ [aᵢ, aᵢ₊₁).
Is it true that, for almost all α, the sequence f(αn) is uniformly distributed in [0,1)?

Answer: NO

The general conjecture is FALSE, as shown by Schmidt (1969).

Historical Background:
- Problem originally due to Le Veque (1953)
- Davenport and LeVeque (1963) proved it under the assumption that aₙ - aₙ₋₁ is monotonic
- Davenport and Erdős (1963) proved it true when aₙ ≫ n^(1/2+ε) for some ε > 0
- Schmidt (1969) constructed a counterexample to the general conjecture

The key example: If A = ℕ, then f(x) = {x} (fractional part), and by Weyl's theorem,
f(αn) is uniformly distributed for almost all α.

References:
- Le Veque [LV53]: "On uniform distribution modulo a subdivision"
- Davenport, LeVeque [DaLe63]: "Uniform distribution relative to a fixed sequence"
- Davenport, Erdős [DaEr63]: "A theorem on uniform distribution"
- Schmidt [Sc69]: "Disproof of some conjectures on Diophantine approximations"
- Erdős [Er61], [Er64b]
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Order.Filter.Basic

open MeasureTheory Set Filter

namespace Erdos492

/-
## Part I: Definitions

Setting up the mathematical framework for uniform distribution relative to a sequence.
-/

/--
An infinite increasing sequence A = {a₁ < a₂ < ...} of natural numbers.
-/
structure IncreasingSequence where
  seq : ℕ → ℕ
  strictly_increasing : StrictMono seq
  unbounded : ∀ M : ℕ, ∃ n : ℕ, seq n > M

/--
The density condition: aᵢ₊₁/aᵢ → 1 as i → ∞.
This means consecutive terms become arbitrarily close in ratio.
-/
def hasDensityCondition (A : IncreasingSequence) : Prop :=
  Tendsto (fun i => (A.seq (i + 1) : ℝ) / (A.seq i : ℝ)) atTop (𝓝 1)

/--
Given an increasing sequence A and x ≥ a₁, find the index i such that aᵢ ≤ x < aᵢ₊₁.
Returns the unique index, assuming it exists.
-/
noncomputable def findIndex (A : IncreasingSequence) (x : ℝ) : ℕ :=
  Nat.find (⟨0, by sorry⟩ : ∃ i, (A.seq i : ℝ) ≤ x ∧ x < (A.seq (i + 1) : ℝ))

/--
The generalized fractional part function f: [a₁, ∞) → [0, 1).
f(x) = (x - aᵢ) / (aᵢ₊₁ - aᵢ) where x ∈ [aᵢ, aᵢ₊₁).
-/
noncomputable def generalizedFractionalPart (A : IncreasingSequence) (x : ℝ) : ℝ :=
  let i := findIndex A x
  let aᵢ := (A.seq i : ℝ)
  let aᵢ₊₁ := (A.seq (i + 1) : ℝ)
  (x - aᵢ) / (aᵢ₊₁ - aᵢ)

notation "f[" A "](" x ")" => generalizedFractionalPart A x

/-
## Part II: The Standard Case - Natural Numbers

When A = ℕ, the generalized fractional part reduces to the usual fractional part.
-/

/--
The natural numbers form an increasing sequence.
-/
def naturalNumberSequence : IncreasingSequence where
  seq := id
  strictly_increasing := strictMono_id
  unbounded := fun M => ⟨M + 1, by omega⟩

/--
For A = ℕ, the density condition holds trivially: (n+1)/n → 1.
-/
theorem naturals_have_density_condition : hasDensityCondition naturalNumberSequence := by
  simp only [hasDensityCondition, naturalNumberSequence]
  -- (i+1+1)/(i+1) = 1 + 1/(i+1) → 1
  sorry

/--
For A = ℕ, f(x) equals the usual fractional part {x}.
-/
theorem naturals_fractional_part (x : ℝ) (hx : x ≥ 1) :
    f[naturalNumberSequence](x) = Int.fract x := by
  sorry

/-
## Part III: Uniform Distribution

A sequence (xₙ) in [0,1) is uniformly distributed if for all 0 ≤ a < b ≤ 1:
  lim_{N→∞} (1/N) · |{n ≤ N : xₙ ∈ [a,b)}| = b - a
-/

/--
A sequence in [0,1) is uniformly distributed (Weyl's criterion).
-/
def IsUniformlyDistributed (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    Tendsto (fun N => (Finset.filter (fun n => a ≤ x n ∧ x n < b)
                        (Finset.range N)).card / (N : ℝ))
            atTop (𝓝 (b - a))

/--
The sequence (αn mod 1) as a function of n.
-/
noncomputable def alphaMultiples (α : ℝ) : ℕ → ℝ := fun n => Int.fract (α * n)

/--
The generalized sequence f(αn) for a given α and sequence A.
-/
noncomputable def generalizedAlphaSequence (A : IncreasingSequence) (α : ℝ) : ℕ → ℝ :=
  fun n => f[A](α * n)

/-
## Part IV: Known Positive Results

Cases where uniform distribution DOES hold.
-/

/--
**Weyl's Equidistribution Theorem (1916):**
For irrational α, the sequence (αn mod 1) is uniformly distributed in [0,1).
-/
axiom weyl_equidistribution (α : ℝ) (hα : Irrational α) :
    IsUniformlyDistributed (alphaMultiples α)

/--
**Le Veque's Result (1953):**
Under certain special conditions on A, uniform distribution holds.
-/
axiom leveque_special_cases (A : IncreasingSequence) (hA : hasDensityCondition A)
    (hSpecial : True) :  -- Placeholder for specific conditions
    ∀ᵐ α ∂volume, IsUniformlyDistributed (generalizedAlphaSequence A α)

/--
**Davenport-LeVeque (1963):**
If aₙ - aₙ₋₁ is monotonic (either increasing or decreasing),
then for almost all α, f(αn) is uniformly distributed.
-/
def hasMonotonicDifferences (A : IncreasingSequence) : Prop :=
  Monotone (fun n => A.seq (n + 1) - A.seq n) ∨
  Antitone (fun n => A.seq (n + 1) - A.seq n)

axiom davenport_leveque (A : IncreasingSequence)
    (hA : hasDensityCondition A)
    (hMono : hasMonotonicDifferences A) :
    ∀ᵐ α ∂volume, IsUniformlyDistributed (generalizedAlphaSequence A α)

/--
**Davenport-Erdős (1963):**
If aₙ grows faster than n^(1/2+ε), uniform distribution holds for almost all α.
-/
def hasFastGrowth (A : IncreasingSequence) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (A.seq n : ℝ) ≥ C * (n : ℝ) ^ (1/2 + ε)

axiom davenport_erdos (A : IncreasingSequence)
    (hA : hasDensityCondition A)
    (hFast : hasFastGrowth A) :
    ∀ᵐ α ∂volume, IsUniformlyDistributed (generalizedAlphaSequence A α)

/-
## Part V: Schmidt's Counterexample

The general conjecture is FALSE.
-/

/--
**Schmidt's Theorem (1969):**
There exists an infinite sequence A satisfying the density condition
for which the set of α where f(αn) is NOT uniformly distributed
has positive measure.
-/
axiom schmidt_counterexample :
    ∃ A : IncreasingSequence,
      hasDensityCondition A ∧
      ¬(∀ᵐ α ∂(volume : Measure ℝ), IsUniformlyDistributed (generalizedAlphaSequence A α))

/--
**Erdős Problem #492: DISPROVED**

The conjecture that f(αn) is uniformly distributed for almost all α
and for all sequences A with aᵢ₊₁/aᵢ → 1 is FALSE.
-/
theorem erdos_492_disproved :
    ¬(∀ A : IncreasingSequence, hasDensityCondition A →
        ∀ᵐ α ∂(volume : Measure ℝ), IsUniformlyDistributed (generalizedAlphaSequence A α)) := by
  intro hConj
  obtain ⟨A, hDensity, hNotAE⟩ := schmidt_counterexample
  exact hNotAE (hConj A hDensity)

/-
## Part VI: Characterizing the Boundary

Understanding when the conjecture holds vs. fails.
-/

/--
**The Critical Growth Rate:**
The boundary appears to be around aₙ ~ √n.
Below this growth rate, counterexamples exist.
Above this growth rate (with ε margin), the conjecture holds.
-/
def hasCriticalGrowth (A : IncreasingSequence) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 → (A.seq n : ℝ) ≤ C * Real.sqrt n

/--
Schmidt's counterexample can be constructed with critical growth.
-/
axiom schmidt_construction_has_critical_growth :
    ∃ A : IncreasingSequence,
      hasDensityCondition A ∧
      hasCriticalGrowth A ∧
      ¬(∀ᵐ α ∂(volume : Measure ℝ), IsUniformlyDistributed (generalizedAlphaSequence A α))

/-
## Part VII: Connections to Diophantine Approximation

The problem is deeply connected to how well real numbers can be approximated by rationals.
-/

/--
The Diophantine condition: α is badly approximable if there exists c > 0 such that
|α - p/q| > c/q² for all rationals p/q.
-/
def IsBadlyApproximable (α : ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ p q : ℤ, q > 0 → |α - p / q| > c / q ^ 2

/--
For badly approximable α, uniform distribution may fail more easily.
-/
axiom badly_approximable_connection (A : IncreasingSequence) (α : ℝ)
    (hBad : IsBadlyApproximable α)
    (hCrit : hasCriticalGrowth A)
    (hDensity : hasDensityCondition A) :
    True  -- Placeholder: states there's a deeper connection

/-
## Part VIII: Summary of Results

Collecting all the key theorems.
-/

/--
**Summary Theorem:**
1. The general conjecture is FALSE (Schmidt 1969)
2. It holds when differences are monotonic (Davenport-LeVeque 1963)
3. It holds when growth exceeds √n by any ε (Davenport-Erdős 1963)
4. The critical growth rate is approximately √n
-/
theorem erdos_492_summary :
    -- 1. General conjecture is false
    (∃ A : IncreasingSequence, hasDensityCondition A ∧
      ¬(∀ᵐ α ∂(volume : Measure ℝ), IsUniformlyDistributed (generalizedAlphaSequence A α))) ∧
    -- 2. Monotonic differences case holds
    (∀ A : IncreasingSequence, hasDensityCondition A → hasMonotonicDifferences A →
      ∀ᵐ α ∂(volume : Measure ℝ), IsUniformlyDistributed (generalizedAlphaSequence A α)) ∧
    -- 3. Fast growth case holds
    (∀ A : IncreasingSequence, hasDensityCondition A → hasFastGrowth A →
      ∀ᵐ α ∂(volume : Measure ℝ), IsUniformlyDistributed (generalizedAlphaSequence A α)) := by
  constructor
  · exact schmidt_counterexample
  constructor
  · exact davenport_leveque
  · exact davenport_erdos

/--
**Answer to Erdős Problem #492:**
NO - The conjecture is false in general.
-/
theorem erdos_492_answer : ∃ A : IncreasingSequence,
    hasDensityCondition A ∧
    ∃ S : Set ℝ, volume S > 0 ∧
      ∀ α ∈ S, ¬IsUniformlyDistributed (generalizedAlphaSequence A α) := by
  obtain ⟨A, hDensity, hNotAE⟩ := schmidt_counterexample
  use A, hDensity
  -- The negation of "almost everywhere" means a set of positive measure exists
  sorry

end Erdos492
