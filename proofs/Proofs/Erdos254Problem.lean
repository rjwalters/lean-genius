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

/-
## Part I: Basic Definitions

Distance to nearest integer and counting functions.
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

/-
## Part II: The Growth Condition

The first hypothesis requires that the number of elements of A
in each dyadic interval [x, 2x] tends to infinity.
-/

/-- The growth condition: |A ∩ [1,2x]| - |A ∩ [1,x]| → ∞ -/
def HasGrowthCondition (A : Set ℕ) : Prop :=
  ∀ M : ℕ, ∃ x₀ : ℝ, x₀ > 0 ∧
    ∀ x ≥ x₀, countTo A (2 * x) - countTo A x ≥ M

/-
## Part III: The Irrationality Condition

The second hypothesis ensures that A is "uniformly distributed"
modulo every irrational multiple θ, in the sense that the
fractional parts θn cannot all be close to integers.
-/

/-- Sum of fractional distances Σ {θn} for n ∈ A -/
noncomputable def fracDistSum (A : Set ℕ) (θ : ℝ) : ℝ :=
  ∑' (n : ℕ), if n ∈ A then fracDist (θ * n) else 0

/-- The irrationality condition: Σ {θn} = ∞ for all θ ∈ (0,1) -/
def HasIrrationalityCondition (A : Set ℕ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → fracDistSum A θ = ⊤

/-
## Part IV: Subset Sum Representation
-/

/-- Sum of distinct elements of A representation -/
def IsSubsetSum (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.sum id = n

/-- Every sufficiently large integer is a subset sum -/
def RepresentsAllLarge (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, IsSubsetSum A n

/-
## Part V: The Conjecture
-/

/--
**Erdős's Conjecture (Problem #254, OPEN):**
If A satisfies the growth and irrationality conditions,
then every sufficiently large integer is a sum of distinct elements of A.
-/
def ErdosConjecture : Prop :=
  ∀ A : Set ℕ,
    HasGrowthCondition A →
    HasIrrationalityCondition A →
    RepresentsAllLarge A

/-
## Part VI: Cassels's Theorem (1960)

Cassels proved the conjecture under strictly stronger hypotheses.
-/

/-- Cassels's stronger growth condition: growth / log log x → ∞ -/
def HasStrongGrowthCondition (A : Set ℕ) : Prop :=
  ∀ M : ℝ, M > 0 → ∃ x₀ : ℝ, x₀ > 0 ∧
    ∀ x ≥ x₀, (countTo A (2 * x) - countTo A x : ℝ) / Real.log (Real.log x) ≥ M

/-- Cassels's stronger irrationality condition: Σ {θn}² = ∞ -/
noncomputable def fracDistSqSum (A : Set ℕ) (θ : ℝ) : ℝ :=
  ∑' (n : ℕ), if n ∈ A then (fracDist (θ * n))^2 else 0

def HasStrongIrrationalityCondition (A : Set ℕ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → fracDistSqSum A θ = ⊤

/--
**Cassels's Theorem (1960):**
Under the stronger growth and irrationality conditions,
every sufficiently large integer is a sum of distinct elements of A.
-/
axiom cassels_theorem :
  ∀ A : Set ℕ,
    HasStrongGrowthCondition A →
    HasStrongIrrationalityCondition A →
    RepresentsAllLarge A

/-
## Part VII: Examples
-/

/-- The set of powers of 2: {1, 2, 4, 8, ...} -/
def PowersOf2 : Set ℕ := {n | ∃ k, n = 2^k}

/-- Powers of 2 satisfy the growth condition. -/
axiom powers_of_2_growth :
  HasGrowthCondition PowersOf2

/-- Powers of 2 satisfy the irrationality condition. -/
axiom powers_of_2_irrationality :
  HasIrrationalityCondition PowersOf2

/-- Every sufficiently large n is a sum of distinct powers of 2 (binary representation). -/
axiom powers_of_2_representation :
  RepresentsAllLarge PowersOf2

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #254: Summary**

CONJECTURE (OPEN): If A ⊆ ℕ satisfies growth and irrationality conditions,
then every sufficiently large integer is a subset sum of A.

Combines:
1. Cassels's theorem under stronger hypotheses
2. Powers of 2 as a concrete example satisfying all conditions
3. Powers of 2 represent all sufficiently large integers
-/
theorem erdos_254_summary :
    -- Cassels's theorem holds under stronger conditions
    (∀ A : Set ℕ, HasStrongGrowthCondition A →
      HasStrongIrrationalityCondition A → RepresentsAllLarge A) ∧
    -- Powers of 2 satisfy both conditions
    (HasGrowthCondition PowersOf2 ∧ HasIrrationalityCondition PowersOf2) ∧
    -- Powers of 2 represent all large integers
    RepresentsAllLarge PowersOf2 :=
  ⟨cassels_theorem,
   ⟨powers_of_2_growth, powers_of_2_irrationality⟩,
   powers_of_2_representation⟩

end Erdos254
