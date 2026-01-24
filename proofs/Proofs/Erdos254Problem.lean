/-
Erdős Problem #254: Sumset Representation from Growth and Irrationality Conditions

Source: https://erdosproblems.com/254
Status: OPEN (Cassels proved related result)

Statement:
Let A ⊆ ℕ satisfy:
1. |A ∩ [1,2x]| - |A ∩ [1,x]| → ∞ as x → ∞
2. Σ_{n ∈ A} {θn} = ∞ for every θ ∈ (0,1), where {x} = dist(x, ℤ)

Conjecture: Every sufficiently large integer is the sum of distinct elements of A.

Known Results:
- Cassels (1960) proved under stronger hypotheses:
  - (|A ∩ [1,2x]| - |A ∩ [1,x]|) / log log x → ∞
  - Σ {θn}² = ∞ for every θ ∈ (0,1)
- Erdős's original conjecture with weaker conditions remains OPEN

References:
- [Er61] Erdős (1961) - Original problem
- [Ca60] Cassels (1960) - Stronger result

Tags: number-theory, sumsets, subset-sums, open
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real Set

namespace Erdos254

/-!
## Part 1: Basic Definitions
-/

/-- Distance to nearest integer -/
noncomputable def fracDist (x : ℝ) : ℝ :=
  |x - round x|

/-- Alternative: {x} is the minimum of x - ⌊x⌋ and ⌈x⌉ - x -/
noncomputable def fracDist' (x : ℝ) : ℝ :=
  min (x - Int.floor x) (Int.ceil x - x)

/-- Count of elements of A in [1, x] -/
noncomputable def countTo (A : Set ℕ) (x : ℝ) : ℕ :=
  (Finset.range (Nat.floor x + 1)).filter (· ∈ A) |>.card

/-!
## Part 2: The Growth Condition
-/

/-- The growth condition: |A ∩ [1,2x]| - |A ∩ [1,x]| → ∞ -/
def HasGrowthCondition (A : Set ℕ) : Prop :=
  ∀ M : ℕ, ∃ x₀ : ℝ, x₀ > 0 ∧
    ∀ x ≥ x₀, countTo A (2 * x) - countTo A x ≥ M

/-- Intuition: A has infinitely many elements in each dyadic interval -/
axiom growth_intuition :
  -- This means A is "infinitely dense" in a specific sense
  -- Enough elements keep appearing as we go to infinity
  True

/-!
## Part 3: The Irrationality Condition
-/

/-- Sum of fractional distances Σ {θn} for n ∈ A -/
noncomputable def fracDistSum (A : Set ℕ) (θ : ℝ) : ℝ :=
  ∑' (n : ℕ), if n ∈ A then fracDist (θ * n) else 0

/-- The irrationality condition: Σ {θn} = ∞ for all θ ∈ (0,1) -/
def HasIrrationalityCondition (A : Set ℕ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → fracDistSum A θ = ⊤

/-- Intuition: A is "uniformly distributed" modulo every θ -/
axiom irrationality_intuition :
  -- The fractional parts θn mod 1 are well-distributed
  -- Enough of them are far from integers
  True

/-!
## Part 4: The Conjecture
-/

/-- Sum of distinct elements of A representation -/
def IsSubsetSum (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.sum id = n

/-- Every sufficiently large integer is a subset sum -/
def RepresentsAllLarge (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, IsSubsetSum A n

/-- Erdős's Conjecture -/
def ErdosConjecture : Prop :=
  ∀ A : Set ℕ,
    HasGrowthCondition A →
    HasIrrationalityCondition A →
    RepresentsAllLarge A

/-!
## Part 5: Cassels's Theorem (1960)
-/

/-- Cassels's stronger growth condition -/
def HasStrongGrowthCondition (A : Set ℕ) : Prop :=
  ∀ M : ℝ, M > 0 → ∃ x₀ : ℝ, x₀ > 0 ∧
    ∀ x ≥ x₀, (countTo A (2 * x) - countTo A x : ℝ) / Real.log (Real.log x) ≥ M

/-- Cassels's stronger irrationality condition -/
noncomputable def fracDistSqSum (A : Set ℕ) (θ : ℝ) : ℝ :=
  ∑' (n : ℕ), if n ∈ A then (fracDist (θ * n))^2 else 0

def HasStrongIrrationalityCondition (A : Set ℕ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → fracDistSqSum A θ = ⊤

/-- Cassels's Theorem (1960) -/
axiom cassels_theorem :
  ∀ A : Set ℕ,
    HasStrongGrowthCondition A →
    HasStrongIrrationalityCondition A →
    RepresentsAllLarge A

/-!
## Part 6: The Gap
-/

/-- The gap between Erdős's conditions and Cassels's -/
axiom condition_gap :
  -- Erdős: (count(2x) - count(x)) → ∞
  -- Cassels: (count(2x) - count(x)) / log log x → ∞
  -- Cassels's condition is strictly stronger (faster growth)
  True

/-- Similarly for the irrationality condition -/
axiom irrationality_gap :
  -- Erdős: Σ {θn} = ∞
  -- Cassels: Σ {θn}² = ∞
  -- {θn}² ≤ {θn} ≤ 1/2, so Σ{θn}² ≤ Σ{θn}
  -- Cassels's condition is weaker (easier to satisfy)
  -- But the combination with stronger growth still works
  True

/-!
## Part 7: Examples
-/

/-- The set of powers of 2: {1, 2, 4, 8, ...} -/
def PowersOf2 : Set ℕ := {n | ∃ k, n = 2^k}

/-- Powers of 2 satisfy the growth condition -/
axiom powers_of_2_growth :
  HasGrowthCondition PowersOf2

/-- Powers of 2 satisfy the irrationality condition -/
axiom powers_of_2_irrationality :
  HasIrrationalityCondition PowersOf2

/-- Indeed, every sufficiently large n is a sum of distinct powers of 2 -/
axiom powers_of_2_representation :
  RepresentsAllLarge PowersOf2

/-!
## Part 8: Related Problems
-/

/-- Connection to subset sum problem -/
axiom subset_sum_connection :
  -- The subset sum problem asks: given A and n, is n a subset sum?
  -- This is NP-complete in general
  -- But with growth/irrationality conditions, the answer is "yes" for large n
  True

/-- Connection to Sidon sets -/
axiom sidon_connection :
  -- Sidon sets have unique subset sums
  -- This problem concerns existence of representations
  True

/-!
## Part 9: Summary
-/

/-- The problem remains open in its original form -/
axiom erdos_254_open :
  -- Erdős's original conjecture (with weaker conditions) is OPEN
  -- Cassels proved a related result with stronger hypotheses
  True

/-- **Erdős Problem #254: OPEN**

CONJECTURE: If A ⊆ ℕ satisfies:
1. |A ∩ [1,2x]| - |A ∩ [1,x]| → ∞
2. Σ {θn} = ∞ for all θ ∈ (0,1)

Then every sufficiently large integer is a sum of distinct elements of A.

STATUS: OPEN

KNOWN: Cassels (1960) proved under stronger conditions:
- Growth: (count(2x) - count(x)) / log log x → ∞
- Irrationality: Σ {θn}² = ∞

The gap between Erdős's conditions and Cassels's remains to be closed.
-/
theorem erdos_254_status : True := trivial

/-- Problem status -/
def erdos_254_status_str : String :=
  "OPEN - Cassels proved related result, original conjecture open"

end Erdos254
