/-
Erdős Problem #789: Sum-Length-Free Subsets

Source: https://erdosproblems.com/789
Status: OPEN (gap between bounds)

Statement:
Let h(n) be maximal such that if A ⊆ ℤ with |A| = n then there is B ⊆ A
with |B| ≥ h(n) such that if a₁+⋯+aᵣ = b₁+⋯+bₛ with aᵢ,bᵢ ∈ B then r = s.

Estimate h(n).

Known Bounds:
- Erdős (1962): h(n) ≪ n^{5/6}
- Straus (1966): h(n) ≪ n^{1/2} (best upper bound)
- Erdős (1962): h(n) ≫ n^{1/3}
- Erdős-Choi (1974): h(n) ≫ (n log n)^{1/3} (best lower bound)

The gap between (n log n)^{1/3} and n^{1/2} remains open.

Related: Problems 186 and 874

References:
- [Er62c] Erdős: Some remarks on number theory III
- [St66] Straus: On a problem in combinatorial number theory
- [Ch74b] Choi: On an extremal problem in number theory

Tags: additive-combinatorics, sum-free-sets, extremal-combinatorics
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos789

open Finset BigOperators

/-
## Part I: Basic Definitions

The sum-length-free property: equal sums must have equal number of terms.
-/

/-- A multiset sum representation: sum of elements with their count -/
structure SumRep (B : Finset ℤ) where
  terms : Multiset ℤ
  allInB : ∀ x ∈ terms, x ∈ B

/-- The length of a sum representation -/
def SumRep.length {B : Finset ℤ} (r : SumRep B) : ℕ := r.terms.card

/-- The value of a sum representation -/
def SumRep.value {B : Finset ℤ} (r : SumRep B) : ℤ := r.terms.sum

/-- Sum-length-free property: equal sums have equal lengths -/
def SumLengthFree (B : Finset ℤ) : Prop :=
  ∀ r s : SumRep B, r.value = s.value → r.length = s.length

/-
## Part II: The Function h(n)

h(n) = max size of sum-length-free subset B of any n-element set A.
-/

/-- For any A of size n, there exists B ⊆ A with |B| ≥ h(n) and SumLengthFree B -/
def h_exists (n : ℕ) : Prop :=
  ∃ h : ℕ, h > 0 ∧
    ∀ A : Finset ℤ, A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ B.card ≥ h ∧ SumLengthFree B

/-- The function h(n) (axiomatized) -/
axiom h (n : ℕ) : ℕ
/-
## Part III: Upper Bounds
-/

/-- Erdős (1962): h(n) ≪ n^{5/6} -/
/-- Straus (1966): h(n) ≪ n^{1/2} (best known upper bound) -/
axiom straus_1966_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * Real.sqrt n

/-- Current best upper bound theorem -/
theorem best_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * Real.sqrt n := straus_1966_upper

/-
## Part IV: Lower Bounds
-/

/-- Erdős (1962): h(n) ≫ n^{1/3} via probabilistic construction -/
/-- Erdős-Choi (1974): h(n) ≫ (n log n)^{1/3} (best known lower bound) -/
axiom erdos_choi_1974_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ)

/-- Current best lower bound theorem -/
theorem best_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ) := erdos_choi_1974_lower

/-
## Part V: The Gap
-/

/-- Combined bounds: (n log n)^{1/3} ≪ h(n) ≪ n^{1/2} -/
theorem combined_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ)) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * Real.sqrt n) := by
  exact ⟨erdos_choi_1974_lower, straus_1966_upper⟩

/- The gap between bounds: exponents 1/3 and 1/2 -/

/-
## Part VI: Erdős's Construction
-/

/- Erdős's probabilistic construction for lower bound:
    For random α ∈ [0,1], take
    B = {a ∈ A : {αa} ∈ n^{-1/3} + ½(-n^{-2/3}, n^{-2/3})}
    Expected |B| ≈ n^{1/3} and likely sum-length-free -/

/- Choi's improvement using more careful analysis -/

/-
## Part VII: Connection to Sidon Sets
-/

/-- A Sidon set (B₂ sequence) has distinct pairwise sums -/
def IsSidonSet (B : Finset ℤ) : Prop :=
  ∀ a b c d : ℤ, a ∈ B → b ∈ B → c ∈ B → d ∈ B →
    a + b = c + d → ({a, b} : Finset ℤ) = {c, d}

/-- Sidon sets are sum-length-free (length 2 sums are unique) -/
/-- Maximum Sidon subset has size ≈ √n (Erdős-Turán) -/
/-
## Part VIII: Related Problems
-/

/- Connection to Problem 186 (sum-free sets) -/

/- Connection to Problem 874 -/

/-
## Part IX: Special Cases
-/

/-- For n = 1: h(1) = 1 trivially -/
/- For small sets, explicit bounds can be computed -/

/-
## Part X: Examples
-/

/- Example: {1, 2, 3} - is {1, 3} sum-length-free?
    1 + 1 = 2 (length 2), but 2 ∉ B
    1 + 3 = 4 (length 2), 3 + 1 = 4 (length 2) ✓
    So {1, 3} is sum-length-free -/

/-- Numerical bounds:
    At n = 1000:
    - Lower: (1000 · 6.9)^{1/3} ≈ 19.1
    - Upper: √1000 ≈ 31.6
    Gap is meaningful even for moderate n -/
example : (1000 : ℕ).sqrt = 31 := by native_decide  -- √1000 ≈ 31

/-- At n = 1000000:
    - Lower: (10^6 · 13.8)^{1/3} ≈ 239
    - Upper: √10^6 = 1000
    Gap grows significantly -/
example : (1000000 : ℕ).sqrt = 1000 := by native_decide

/-
## Part XI: Conjectures
-/

/-- **Conjectured growth rates for h(n):**
    Three plausible scenarios for the true asymptotic behavior:
    1. h(n) ~ n^{1/2} (Straus bound is tight)
    2. h(n) ~ n^α for some 1/3 < α < 1/2
    3. h(n) grows slower than any power of n -/
def possible_growth_rates : Prop :=
  (∃ c > 0, ∀ n : ℕ, n ≥ 2 → (h n : ℝ) ≥ c * (n : ℝ)^(1/2 : ℝ)) ∨
  (∃ α : ℝ, 1/3 < α ∧ α < 1/2 ∧
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 2 → c₁ * (n : ℝ)^α ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ c₂ * (n : ℝ)^α) ∨
  (∀ α > 0, ∃ N : ℕ, ∀ n ≥ N, (h n : ℝ) ≤ (n : ℝ)^α)

/- The problem is to determine the correct exponent -/

/-
## Part XII: Proof Techniques
-/

/- Upper bound uses counting argument on sum representations -/

/- Lower bound uses probabilistic method with fractional parts -/

/- Diophantine approximation is key to construction -/

/-
## Part XIII: Summary
-/

/--
**Erdős Problem #789: Summary**

**Definition:** h(n) = max |B| such that B ⊆ A, |A| = n,
and equal sums in B must have equal length.

**Known Bounds:**
- Upper: h(n) ≪ √n (Straus 1966)
- Lower: h(n) ≫ (n log n)^{1/3} (Erdős-Choi 1974)

**Status:** OPEN
The gap between exponents 1/3 and 1/2 is significant.

**Key Insight:** The sum-length-free property is weaker than Sidon
(only requires length equality, not term equality), so h(n) could
be larger than maximum Sidon subset. But Straus showed h(n) ≪ √n.

**Construction:** Erdős used fractional parts {αa} for random α
to find sum-length-free subsets of size ≈ n^{1/3}.

**Related:** Problems 186 (sum-free) and 874.
-/
theorem erdos_789_statement :
    -- Lower bound
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ)) ∧
    -- Upper bound
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * Real.sqrt n) ∧
    -- Problem is open
    True := by
  exact ⟨erdos_choi_1974_lower, straus_1966_upper, trivial⟩

end Erdos789
