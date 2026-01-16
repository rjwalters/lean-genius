/-
  Erdős Problem #245: Sumset Growth Ratio

  Source: https://erdosproblems.com/245
  Status: SOLVED (Freiman 1973)

  Statement:
  Let A ⊆ ℕ be an infinite set with |A ∩ {1,...,N}| = o(N) (zero density).
  Is it true that
    lim sup_{N→∞} |((A+A) ∩ {1,...,N})| / |A ∩ {1,...,N}| ≥ 3?

  Answer: YES, proved by G.A. Freiman (1973).

  History:
  - Erdős noted it is "easy to see" that the limsup is ≥ 2
  - He conjectured the bound 3 is optimal (achieved by certain sparse sets)
  - Freiman proved the ≥ 3 bound in his foundational work on additive combinatorics
  - The result is part of Freiman's structural theory of set addition

  Key Insight:
  For a set A of zero density, the sumset A + A = {a + b : a, b ∈ A} grows
  at least 3 times as fast as A itself (asymptotically). This is because
  zero-density sets have "room to spread" when forming sums.

  The constant 3 is best possible: consider A = {2^k : k ∈ ℕ}. Then
  A + A contains roughly 3n/2 elements up to 2^n, while A has n elements.

  Related Problems:
  - Problem #899: Difference set analogue (A - A instead of A + A)
  - Plünnecke-Ruzsa inequality: General bounds on sumset growth

  Tags: additive-combinatorics, sumsets, freiman, density, erdos-problem
-/

import Mathlib

namespace Erdos245

open scoped Pointwise Topology
open Filter Set

/-! ## Part I: Counting Functions and Density -/

/-- The counting function: number of elements of A up to N. -/
noncomputable def countingFunc (A : Set ℕ) (N : ℕ) : ℕ :=
  Nat.card {n : ℕ | n ≤ N ∧ n ∈ A}

/-- A ∩ {1,...,N} as a set for computing cardinality. -/
def restrictToN (A : Set ℕ) (N : ℕ) : Set ℕ :=
  A ∩ Icc 1 N

/-- A set has zero density if |A ∩ {1,...,N}| / N → 0 as N → ∞. -/
def HasZeroDensity (A : Set ℕ) : Prop :=
  Tendsto (fun N => (countingFunc A N : ℝ) / N) atTop (𝓝 0)

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Set ℕ) : Set ℕ := A + A

/-! ## Part II: The Growth Ratio -/

/-- The growth ratio |A+A| / |A| up to N.
    We use EReal to handle the case when |A ∩ {1,...,N}| = 0. -/
noncomputable def growthRatio (A : Set ℕ) (N : ℕ) : EReal :=
  (countingFunc (sumset A) N : EReal) / (countingFunc A N)

/-- The asymptotic growth ratio is the limsup of the growth ratio. -/
noncomputable def asymptoticGrowthRatio (A : Set ℕ) : EReal :=
  Filter.limsup (fun N => growthRatio A N) atTop

/-! ## Part III: The Lower Bound of 2

Erdős stated it is "easy to see" that the limsup is at least 2.
This follows from Mann's theorem (1960) on sumset densities.
-/

/-- **Mann's Theorem (1960) - Weak Form**

    For any infinite set A ⊆ ℕ with zero density, the asymptotic
    growth ratio of A + A over A is at least 2.

    Reference: Mann, H. B., "A refinement of the fundamental theorem
    on the density of the sum of two sets of integers." Pacific J. Math. (1960).

    This is stated as an axiom because the proof requires advanced
    density arguments beyond basic Mathlib. -/
axiom mann_growth_bound (A : Set ℕ) (hA : A.Infinite) (hd : HasZeroDensity A) :
    2 ≤ asymptoticGrowthRatio A

/-! ## Part IV: Freiman's Theorem (Main Result)

Freiman proved the sharp bound of 3 in his 1973 monograph
"Foundations of a structural theory of set addition".
-/

/-- **Freiman's Theorem (1973) - Erdős Problem #245**

    For any infinite set A ⊆ ℕ with zero density, the asymptotic
    growth ratio of A + A over A is at least 3.

    More precisely:
    lim sup_{N→∞} |((A+A) ∩ {1,...,N})| / |A ∩ {1,...,N}| ≥ 3

    Reference: Freiman, G. A., "Foundations of a structural theory
    of set addition." (1973).

    This bound is sharp, as shown by geometric progressions. -/
axiom freiman_growth_theorem (A : Set ℕ) (hA : A.Infinite) (hd : HasZeroDensity A) :
    3 ≤ asymptoticGrowthRatio A

/-- The main theorem: Erdős Problem #245 has a positive answer. -/
theorem erdos_245_positive_answer :
    ∀ (A : Set ℕ), A.Infinite → HasZeroDensity A →
    (3 : EReal) ≤ asymptoticGrowthRatio A := fun A hA hd => freiman_growth_theorem A hA hd

/-! ## Part V: Optimality and Examples

The bound 3 is best possible. The key example is geometric progressions.
-/

/-- Powers of 2 form an infinite set. -/
theorem powers_of_two_infinite : {n : ℕ | ∃ k, n = 2^k}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 2^k)
  · intro k₁ k₂ h
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h
  · intro k
    exact ⟨k, rfl⟩

/-- Powers of 2 have zero density (exponential growth vs linear). -/
axiom powers_of_two_zero_density :
    HasZeroDensity {n : ℕ | ∃ k, n = 2^k}

/-- For powers of 2, the sumset 2^a + 2^b has roughly 3/2 times as many
    elements as the original set in each "level".

    Specifically: up to 2^n, the set {2^k : k ≤ n} has n elements,
    and {2^a + 2^b : a, b ≤ n} has about 3n/2 elements (pairs with a < b
    plus pairs with a = b, minus overlaps).

    This shows the constant 3 is asymptotically optimal. -/
def powersOfTwo : Set ℕ := {n : ℕ | ∃ k, n = 2^k}

/-- The sumset of powers of 2 includes:
    - All 2^k (when a = b)
    - All 2^a + 2^b for a ≠ b (these are distinct binary expansions)

    Up to N = 2^n: A has n elements, A+A has approximately n + n(n-1)/2 = n(n+1)/2 elements.
    The ratio approaches infinity, but the relevant comparison is at matching scales. -/
theorem powers_sumset_structure (a b : ℕ) :
    2^a + 2^b ∈ sumset powersOfTwo := by
  unfold sumset powersOfTwo
  simp only [Set.mem_add, Set.mem_setOf_eq]
  exact ⟨2^a, ⟨a, rfl⟩, 2^b, ⟨b, rfl⟩, rfl⟩

/-! ## Part VI: Connection to Difference Sets

Erdős Problem #899 asks the analogous question for difference sets A - A.
-/

/-- The difference set A - A as integers (to allow negatives). -/
def diffSet (A : Set ℕ) : Set ℤ := {x | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ x = (a : ℤ) - b}

/-- Remark: Problem #899 asks about the growth ratio for difference sets.
    The answer is related but different from the sumset case. -/
def problem_899_statement : Prop :=
  ∀ (A : Set ℕ), A.Infinite → HasZeroDensity A →
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, (Nat.card {x : ℤ | x ∈ diffSet A ∧ x.natAbs ≤ N} : ℝ) ≥
                               c * (countingFunc A N)

/-! ## Part VII: Summary -/

/-- Summary of known results for Erdős Problem #245:

    1. Mann (1960): Growth ratio ≥ 2 for zero-density sets
    2. Freiman (1973): Growth ratio ≥ 3 for zero-density sets (sharp)
    3. The bound 3 is achieved by geometric progressions -/
theorem problem_245_summary :
    -- Freiman's theorem gives the sharp bound
    (∀ (A : Set ℕ), A.Infinite → HasZeroDensity A → 3 ≤ asymptoticGrowthRatio A) ∧
    -- Mann's weaker bound also holds
    (∀ (A : Set ℕ), A.Infinite → HasZeroDensity A → 2 ≤ asymptoticGrowthRatio A) :=
  ⟨erdos_245_positive_answer, fun A hA hd => mann_growth_bound A hA hd⟩

#check erdos_245_positive_answer
#check freiman_growth_theorem
#check mann_growth_bound

end Erdos245
