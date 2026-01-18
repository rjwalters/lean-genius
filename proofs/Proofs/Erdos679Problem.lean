/-
  Erdős Problem #679: Small ω(n-k) for All k < n

  Source: https://erdosproblems.com/679
  Status: OPEN (first part), DISPROVEN (stronger version)

  Statement:
  Let ε > 0 and ω(n) count the number of distinct prime factors of n.
  Are there infinitely many n such that ω(n-k) < (1+ε) log k / log log k
  for all sufficiently large k < n?

  Known Results:
  - The stronger version with O(1) error is FALSE
  - For all large n, ∃ k < n: ω(n-k) ≥ log k/log log k + c(log k)/(log log k)²

  Related: Similar questions for Ω (prime factors with multiplicity)

  Tags: number-theory, prime-factors, omega-function
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos679

open Nat ArithmeticFunction Real Filter

/- ## Part I: The ω Function -/

/-- ω(n) = number of distinct prime divisors of n. -/
noncomputable def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- ω(1) = 0. -/
theorem omega_one : omega 1 = 0 := by
  simp [omega]

/-- ω(p) = 1 for prime p. -/
theorem omega_prime (p : ℕ) (hp : p.Prime) : omega p = 1 := by
  sorry

/-- ω(p^k) = 1 for prime p and k ≥ 1. -/
theorem omega_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    omega (p ^ k) = 1 := by
  sorry

/-- ω is additive on coprime arguments. -/
theorem omega_mul_coprime (m n : ℕ) (hmn : m.Coprime n) :
    omega (m * n) = omega m + omega n := by
  sorry

/- ## Part II: The Hardy-Ramanujan Bound -/

/-- The normal order of ω(n) is log log n. -/
def NormalOrderOmega : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop,
    (1 - ε) * Real.log (Real.log n) < omega n ∧
    (omega n : ℝ) < (1 + ε) * Real.log (Real.log n)

/-- Hardy-Ramanujan (1917): ω(n) ~ log log n for almost all n. -/
theorem hardy_ramanujan : NormalOrderOmega := by
  sorry

/-- The maximum value of ω(n) for n ≤ x. -/
noncomputable def maxOmega (x : ℕ) : ℕ :=
  Finset.sup' (Finset.range (x + 1)) (by simp) omega

/-- max ω(n) for n ≤ x is ~ log x / log log x. -/
theorem max_omega_bound (x : ℕ) (hx : x ≥ 3) :
    (maxOmega x : ℝ) ≤ 2 * Real.log x / Real.log (Real.log x) := by
  sorry

/- ## Part III: The Main Question -/

/-- The threshold function: (1+ε) log k / log log k. -/
noncomputable def threshold (ε : ℝ) (k : ℕ) : ℝ :=
  (1 + ε) * Real.log k / Real.log (Real.log k)

/-- n satisfies the property if ω(n-k) < threshold(ε, k) for large k. -/
def SatisfiesProperty (ε : ℝ) (n : ℕ) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k → k < n →
    (omega (n - k) : ℝ) < threshold ε k

/-- The main conjecture: Infinitely many n satisfy the property. -/
def MainConjecture : Prop :=
  ∀ ε > 0, Set.Infinite {n : ℕ | SatisfiesProperty ε n}

/-- The problem is OPEN. -/
axiom main_conjecture_open : MainConjecture ∨ ¬MainConjecture

/- ## Part IV: The Stronger Version (Disproven) -/

/-- The stronger version: ω(n-k) < log k / log log k + O(1). -/
def StrongerVersion : Prop :=
  ∃ C : ℝ, Set.Infinite {n : ℕ |
    ∀ k : ℕ, 3 ≤ k → k < n →
      (omega (n - k) : ℝ) < Real.log k / Real.log (Real.log k) + C}

/-- The stronger version is FALSE. -/
theorem stronger_version_false : ¬StrongerVersion := by
  sorry

/-- For all large n, there exists k with ω(n-k) exceeding the threshold. -/
theorem dottedcalculator_result :
    ∃ c > 0, ∀ᶠ n in atTop, ∃ k : ℕ, k < n ∧
      (omega (n - k) : ℝ) ≥ Real.log k / Real.log (Real.log k) +
        c * Real.log k / (Real.log (Real.log k)) ^ 2 := by
  sorry

/- ## Part V: The Ω Function Variant -/

/-- Ω(n) = number of prime divisors counted with multiplicity. -/
noncomputable def bigOmega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- Ω(n) ≥ ω(n) always. -/
theorem bigOmega_ge_omega (n : ℕ) : bigOmega n ≥ omega n := by
  sorry

/-- For Ω, the threshold is log₂ k. -/
noncomputable def thresholdOmega (k : ℕ) : ℝ :=
  Real.log k / Real.log 2

/-- The analogous question for Ω. -/
def OmegaVariant : Prop :=
  ∀ ε > 0, Set.Infinite {n : ℕ |
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → k < n →
      (bigOmega (n - k) : ℝ) < (1 + ε) * thresholdOmega k}

/- ## Part VI: Special Cases -/

/-- For n = 2^m, what is max ω(n-k)? -/
theorem power_of_two_case (m : ℕ) (hm : m ≥ 10) :
    ∃ k : ℕ, k < 2^m ∧
      (omega (2^m - k) : ℝ) ≥ Real.log k / Real.log (Real.log k) := by
  sorry

/-- For primorial n = p₁ · p₂ · ... · p_r, analyze ω(n-k). -/
def primorial (r : ℕ) : ℕ := (Finset.range r).prod (fun i => (Nat.nth Nat.Prime i))

/-- Primorials have high ω. -/
theorem omega_primorial (r : ℕ) : omega (primorial r) = r := by
  sorry

/- ## Part VII: Lower Bounds -/

/-- For any n, there exists k with ω(n-k) reasonably large. -/
theorem existence_of_large_omega (n : ℕ) (hn : n ≥ 10) :
    ∃ k : ℕ, 2 ≤ k ∧ k < n ∧
      (omega (n - k) : ℝ) ≥ Real.log (Real.log n) / 2 := by
  sorry

/-- The set of k with small ω(n-k) has density < 1. -/
theorem small_omega_density (n : ℕ) (hn : n ≥ 100) :
    ∃ δ > 0, (Finset.filter (fun k => omega (n - k) ≤ 2) (Finset.range n)).card
      < (1 - δ) * n := by
  sorry

/- ## Part VIII: Related Problems -/

/-- Connection to Problem #248. -/
def Problem248Connection : Prop :=
  True  -- Placeholder for relationship

/-- Connection to Problem #413. -/
def Problem413Connection : Prop :=
  True  -- Placeholder for relationship

/- ## Part IX: Probabilistic Heuristics -/

/-- Heuristic: Random n should NOT satisfy the property. -/
def ProbabilisticHeuristic : Prop :=
  -- For random n, some k < n will have n - k with many prime factors
  True

/-- The expected number of n ≤ x satisfying the property. -/
noncomputable def expectedCount (ε : ℝ) (x : ℕ) : ℝ :=
  x / Real.log x  -- Heuristic estimate

/- ## Part X: Computational Evidence -/

/-- Computational search: Few n satisfy the property for small ε. -/
def ComputationalEvidence : Prop :=
  ∀ n ≤ 10^6, ¬SatisfiesProperty 0.1 n

/-- The smallest n (if any) satisfying the property for ε = 0.5. -/
noncomputable def smallestExample : Option ℕ :=
  none  -- Unknown if any exist

/- ## Part XI: The Key Dichotomy -/

/-- Either infinitely many special n exist, or there's a uniform lower bound. -/
theorem dichotomy :
    MainConjecture ∨
    (∃ c > 0, ∀ᶠ n in atTop, ∃ k < n,
      (omega (n - k) : ℝ) ≥ (1 + c) * Real.log k / Real.log (Real.log k)) := by
  sorry

/- ## Part XII: Density Considerations -/

/-- If special n exist, how dense are they? -/
def DensityQuestion : Prop :=
  MainConjecture →
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ᶠ x in atTop,
        ({n : ℕ | n ≤ x ∧ SatisfiesProperty 0.1 n}.ncard : ℝ) ≤ x^α

/-- Upper bound on density of special n. -/
theorem density_upper_bound :
    ∀ ε > 0, ∀ᶠ x in atTop,
      ({n : ℕ | n ≤ x ∧ SatisfiesProperty ε n}.ncard : ℝ) ≤ x / Real.log x := by
  sorry

end Erdos679

/-
  ## Summary

  This file formalizes Erdős Problem #679 on small ω(n-k) values.

  **Status**: OPEN (main question), DISPROVEN (stronger version)

  **The Question**: Are there infinitely many n such that ω(n-k) < (1+ε)log k/log log k
  for all sufficiently large k < n?

  **Known Results**:
  - Stronger version (O(1) error) is FALSE
  - For all large n, ∃ k: ω(n-k) ≥ log k/log log k + c(log k)/(log log k)²
  - Hardy-Ramanujan: ω(n) ~ log log n for almost all n

  **What we formalize**:
  1. ω function and properties
  2. Hardy-Ramanujan normal order
  3. Main conjecture
  4. Stronger version (disproven)
  5. Ω function variant
  6. Special cases (powers of 2, primorials)
  7. Lower bounds
  8. Probabilistic heuristics
  9. Density considerations

  **Key sorries**:
  - `stronger_version_false`: Main disproven result
  - `dottedcalculator_result`: Explicit lower bound
  - `hardy_ramanujan`: Classical theorem

  **Note**: Cannot be resolved by finite computation alone
-/
