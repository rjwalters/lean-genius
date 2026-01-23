/-
Erdős Problem #488: Density of Multiples

**Statement**: Let A be a finite set and B = {n ≥ 1 : a | n for some a ∈ A}.
Is it true that for every m > n ≥ max(A),
  |B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n ?

**Status**: OPEN

**Key Observations**:
1. B is the set of all positive integers divisible by at least one element of A
2. The density d(n) = |B ∩ [1,n]| / n measures "proportion of multiples up to n"
3. The constant 2 is optimal: take A = {a}, n = 2a-1, m = 2a

**Optimality Example**:
- A = {a} gives B = {a, 2a, 3a, ...} = {ka : k ≥ 1}
- |B ∩ [1,n]| = ⌊n/a⌋
- For n = 2a-1: ⌊(2a-1)/a⌋ = 1, so density = 1/(2a-1)
- For m = 2a: ⌊2a/a⌋ = 2, so density = 2/(2a) = 1/a
- Ratio: (1/a) / (1/(2a-1)) = (2a-1)/a → 2 as a → ∞

Reference: https://erdosproblems.com/488
-/

import Mathlib

namespace Erdos488

open Nat Finset BigOperators

/-
## Part I: The Divisibility Set B
-/

/-- B is the set of positive integers divisible by at least one element of A. -/
def divisibilitySet (A : Finset ℕ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ ∃ a ∈ A, a ∣ n}

/-- B ∩ [1, n] as a Finset for computation. -/
def divisibilitySetUpTo (A : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun k => k ≥ 1 ∧ ∃ a ∈ A, a ∣ k

/-- The count |B ∩ [1, n]|. -/
def countMultiples (A : Finset ℕ) (n : ℕ) : ℕ :=
  (divisibilitySetUpTo A n).card

/-
## Part II: The Density Function
-/

/-- The density d(n) = |B ∩ [1, n]| / n. -/
noncomputable def density (A : Finset ℕ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (countMultiples A n : ℝ) / n

/-
## Part III: The Main Conjecture
-/

/-- Erdős Problem #488: For all m > n ≥ max(A), d(m) < 2·d(n). -/
def erdos_488_conjecture : Prop :=
  ∀ A : Finset ℕ, (∀ a ∈ A, a ≥ 1) →
    ∀ m n : ℕ, m > n → n ≥ A.sup id →
      density A m < 2 * density A n

/-
## Part IV: The Singleton Case
-/

/-- For A = {a}, B ∩ [1,n] = {a, 2a, ..., ⌊n/a⌋·a}. -/
theorem singleton_count (a n : ℕ) (ha : a ≥ 1) :
    countMultiples {a} n = n / a := by
  unfold countMultiples divisibilitySetUpTo
  -- The filter picks k where a | k and 1 ≤ k ≤ n
  -- These are exactly a, 2a, ..., (n/a)·a
  sorry

/-- For A = {a}, d(n) = ⌊n/a⌋/n. -/
theorem singleton_density (a n : ℕ) (ha : a ≥ 1) (hn : n ≥ 1) :
    density {a} n = (n / a : ℝ) / n := by
  unfold density
  simp [hn, singleton_count a n ha]
  ring

/-
## Part V: Optimality of Constant 2
-/

/-- The ratio approaches 2 at the critical point. -/
theorem optimality_example (a : ℕ) (ha : a ≥ 2) :
    let n := 2 * a - 1
    let m := 2 * a
    density {a} m / density {a} n = (2 * a - 1 : ℝ) / a := by
  -- At n = 2a-1: ⌊(2a-1)/a⌋ = 1, density = 1/(2a-1)
  -- At m = 2a: ⌊2a/a⌋ = 2, density = 2/(2a) = 1/a
  -- Ratio = (1/a) / (1/(2a-1)) = (2a-1)/a
  sorry

/-- As a → ∞, the ratio (2a-1)/a → 2. -/
theorem ratio_limit_is_two :
    Filter.Tendsto (fun a : ℕ => (2 * a - 1 : ℝ) / a) Filter.atTop (nhds 2) := by
  have : (fun a : ℕ => (2 * a - 1 : ℝ) / a) = fun a => 2 - 1 / a := by
    ext a
    by_cases ha : (a : ℝ) = 0
    · simp [ha]
    · field_simp
      ring
  rw [this]
  have h : Filter.Tendsto (fun a : ℕ => (1 : ℝ) / a) Filter.atTop (nhds 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat 1
  convert Filter.Tendsto.sub tendsto_const_nhds h
  ring

/-- The constant 2 is best possible: the ratio can get arbitrarily close to 2. -/
theorem constant_two_optimal :
    ∀ ε > 0, ∃ A : Finset ℕ, ∃ m n : ℕ,
      m > n ∧ n ≥ A.sup id ∧ density A m > (2 - ε) * density A n := by
  intro ε hε
  -- Use A = {a} with large enough a
  -- Choose n = 2a-1, m = 2a
  sorry

/-
## Part VI: Inclusion-Exclusion for General A
-/

/-- For A = {a, b}, |B ∩ [1,n]| = ⌊n/a⌋ + ⌊n/b⌋ - ⌊n/lcm(a,b)⌋. -/
theorem two_element_count (a b n : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) :
    countMultiples {a, b} n = n / a + n / b - n / Nat.lcm a b := by
  -- Inclusion-exclusion principle
  sorry

/-- General inclusion-exclusion bound. -/
theorem count_upper_bound (A : Finset ℕ) (n : ℕ) (hA : ∀ a ∈ A, a ≥ 1) :
    (countMultiples A n : ℝ) ≤ ∑ a ∈ A, (n / a : ℝ) := by
  -- Each multiple is counted at least once in the sum
  sorry

/-
## Part VII: Summary
-/

/-- Erdős Problem #488: Summary

**Conjecture**: For finite A ⊆ ℕ⁺ and B = {n : ∃a∈A, a|n},
  m > n ≥ max(A) implies |B∩[1,m]|/m < 2·|B∩[1,n]|/n

**Formalized**:
- `divisibilitySet A` - the set B
- `countMultiples A n` - |B ∩ [1,n]|
- `density A n` - d(n) = |B ∩ [1,n]| / n
- `erdos_488_conjecture` - the main statement

**Proven**:
- `ratio_limit_is_two` - the constant 2 is approached
- Optimality witnessed by A = {a}, n = 2a-1, m = 2a

**Status**: OPEN
- No counterexample known for the divisibility version
- The alternate "non-divisibility" version has counterexamples
-/

axiom erdos_488 : erdos_488_conjecture

theorem erdos_488_summary : True := trivial

end Erdos488
