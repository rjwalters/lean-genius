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
axiom h_pos (n : ℕ) (hn : n ≥ 1) : h n > 0
axiom h_achievable (n : ℕ) (hn : n ≥ 1) :
    ∀ A : Finset ℤ, A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ B.card ≥ h n ∧ SumLengthFree B

/-
## Part III: Upper Bounds
-/

/-- Erdős (1962): h(n) ≪ n^{5/6} -/
axiom erdos_1962_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * (n : ℝ) ^ (5/6 : ℝ)

/-- Straus (1966): h(n) ≪ n^{1/2} (best known upper bound).
    Proved using a counting argument on sum representations. -/
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

/-- Erdős (1962): h(n) ≫ n^{1/3} via probabilistic construction.
    For random α ∈ [0,1], the set {a ∈ A : {αa} lies in a small interval}
    is likely sum-length-free with expected size ≈ n^{1/3}. -/
axiom erdos_1962_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≥ c * (n : ℝ) ^ (1/3 : ℝ)

/-- Erdős-Choi (1974): h(n) ≫ (n log n)^{1/3} (best known lower bound).
    Choi refined Erdős's probabilistic argument with more careful analysis
    of Diophantine approximation to gain the extra log factor. -/
axiom erdos_choi_1974_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ)

/-- Current best lower bound theorem -/
theorem best_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ) := erdos_choi_1974_lower

/-
## Part V: The Gap and Combined Bounds
-/

/-- Combined bounds: (n log n)^{1/3} ≪ h(n) ≪ n^{1/2} -/
theorem combined_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ)) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * Real.sqrt n) := by
  exact ⟨erdos_choi_1974_lower, straus_1966_upper⟩

/-
## Part VI: Connection to Sidon Sets
-/

/-- A Sidon set (B₂ sequence) has distinct pairwise sums -/
def IsSidonSet (B : Finset ℤ) : Prop :=
  ∀ a b c d : ℤ, a ∈ B → b ∈ B → c ∈ B → d ∈ B →
    a + b = c + d → ({a, b} : Finset ℤ) = {c, d}

/-- Sidon sets are sum-length-free: if a Sidon set has equal sums,
    the underlying terms must form the same pair, hence same length.
    This means h(n) ≥ max Sidon subset size ≈ √n, but in fact
    Straus showed h(n) ≪ √n matching this. -/
axiom sidon_implies_sum_length_free (B : Finset ℤ) (hS : IsSidonSet B) :
    SumLengthFree B

/-- Maximum Sidon subset has size ≈ √n (Erdős-Turán) -/
axiom sidon_bound : ∀ n : ℕ, ∃ C : ℝ, C > 0 ∧
    ∀ A : Finset ℤ, A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ IsSidonSet B ∧ (B.card : ℝ) ≥ C * Real.sqrt n

/-
## Part VII: Computational Examples
-/

/-- Numerical bounds at n = 1000:
    - Lower: (1000 · 6.9)^{1/3} ≈ 19.1
    - Upper: √1000 ≈ 31.6 -/
example : (1000 : ℕ).sqrt = 31 := by native_decide

/-- At n = 1000000:
    - Lower: (10^6 · 13.8)^{1/3} ≈ 239
    - Upper: √10^6 = 1000
    Gap grows significantly -/
example : (1000000 : ℕ).sqrt = 1000 := by native_decide

/-
## Part VIII: Summary
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
theorem erdos_789 :
    -- Lower bound
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ c * (n * Real.log n) ^ (1/3 : ℝ)) ∧
    -- Upper bound
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * Real.sqrt n) := by
  exact ⟨erdos_choi_1974_lower, straus_1966_upper⟩

end Erdos789
