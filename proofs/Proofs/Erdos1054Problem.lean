/-
Erdős Problem #1054: Sum of Smallest Divisors

Let f(n) be the minimal integer m such that n is the sum of the k smallest
divisors of m for some k ≥ 1.

Is it true that f(n) = o(n)? Or is this true only for almost all n,
and limsup f(n)/n = ∞?

**Status**: OPEN (the "almost all" version remains unresolved)

**Background**:
- The function f(n) is undefined for n = 2 and n = 5 (no such m exists)
- For most n, there exists an m whose smallest divisors sum to n
- Terry Tao disproved the strong claim that f(n) = o(n) unconditionally

Reference: https://erdosproblems.com/1054
Sources: [Gu04] Guy, Unsolved Problems in Number Theory, Problem B2
-/

import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Nat Finset

namespace Erdos1054

/-
## Constructive Definitions

We define the divisor sum infrastructure constructively using Mathlib's
Nat.divisors and Finset.sort, enabling concrete proofs about small cases.
-/

/-- The divisors of n sorted in increasing order. -/
noncomputable def sortedDivisors (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- The sum of the k smallest divisors of n (k is 1-indexed). -/
noncomputable def sumSmallestDivisors (n k : ℕ) : ℕ :=
  ((sortedDivisors n).take k).sum

/-- The set of all achievable partial sums of divisors of m.
    This is {sum of first 1 divisors, sum of first 2 divisors, ...}. -/
noncomputable def partialSumSet (m : ℕ) : Finset ℕ :=
  (List.range (sortedDivisors m).length).map
    (fun k => sumSmallestDivisors m (k + 1)) |>.toFinset

/-- n is representable as a sum of smallest divisors of some m. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ n ∈ partialSumSet m

/-- n is representable via a specific m ≤ bound. -/
def IsRepresentableBounded (n bound : ℕ) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ m ≤ bound ∧ n ∈ partialSumSet m

/-- The set of all witnesses m ≥ 1 for which n appears in partialSumSet m. -/
noncomputable def witnesses (n : ℕ) : Set ℕ :=
  { m : ℕ | m ≥ 1 ∧ n ∈ partialSumSet m }

/-- f(n) = the minimal m ≥ 1 such that n ∈ partialSumSet m.
    Returns 0 if n is not representable. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (witnesses n)

/-
## Basic Properties
-/

/-- The sum of the first 0 divisors is 0. -/
theorem sumSmallestDivisors_zero (n : ℕ) : sumSmallestDivisors n 0 = 0 := by
  simp [sumSmallestDivisors, List.take]

/-- For any m ≥ 1, the first divisor is always 1, so sumSmallestDivisors m 1 = 1. -/
theorem first_divisor_is_one (m : ℕ) (hm : m ≥ 1) :
    (sortedDivisors m).head? = some 1 := by
  sorry

/-- 1 is always in the partial sum set of any m ≥ 1. -/
theorem one_in_partialSumSet (m : ℕ) (hm : m ≥ 1) :
    1 ∈ partialSumSet m := by
  sorry

/-- 1 is representable: sum of first divisor of 1 is 1. -/
theorem representable_1 : IsRepresentable 1 := by
  exact ⟨1, le_refl 1, one_in_partialSumSet 1 (le_refl 1)⟩

/-
## Non-representability of 2

For n = 2: The smallest divisor of any m ≥ 1 is always 1.
- k = 1 gives sum = 1 (not 2)
- k ≥ 2 gives sum ≥ 1 + 2 = 3 (since the second-smallest divisor is ≥ 2)
So 2 is never achievable.
-/

/-- For m ≥ 2, the second-smallest divisor is at least 2
    (it's the smallest prime factor). -/
theorem second_divisor_ge_two (m : ℕ) (hm : m ≥ 2) :
    (sortedDivisors m).length ≥ 2 ∧
    ∀ d, d ∈ (sortedDivisors m).drop 1 → d ≥ 2 := by
  sorry

/-- The sum of any k ≥ 2 smallest divisors of m (m ≥ 2) is at least 3.
    Because the first divisor is 1 and the second is ≥ 2. -/
theorem sum_two_smallest_ge_three (m : ℕ) (hm : m ≥ 2) :
    sumSmallestDivisors m 2 ≥ 3 := by
  sorry

/-- 2 is not representable as a sum of smallest divisors.
    - k=1: sum = 1 ≠ 2
    - k≥2: sum ≥ 3 > 2 -/
theorem not_representable_2 : ¬IsRepresentable 2 := by
  sorry

/-
## Non-representability of 5

For n = 5: We need to check that 5 never appears as a partial sum of divisors.
Key argument: For sum = 5 with k = 2, we need 1 + d₂ = 5, so d₂ = 4.
But if 4 | m, then 2 | m, so d₂ ≤ 2, contradiction.
For k = 3: we need 1 + d₂ + d₃ = 5. Since d₂ ≥ 2, we need d₃ ≤ 2,
but d₃ > d₂ ≥ 2, so d₃ ≥ 3, giving sum ≥ 6. Contradiction.
-/

/-- If 4 divides m, then 2 divides m. -/
theorem four_dvd_implies_two_dvd (m : ℕ) (h : 4 ∣ m) : 2 ∣ m := by
  exact dvd_trans ⟨2, rfl⟩ h

/-- 5 is not representable as a sum of smallest divisors.
    This follows from case analysis on the number of divisors used. -/
theorem not_representable_5 : ¬IsRepresentable 5 := by
  sorry

/-
## Concrete Representability Results
-/

/-- 3 is representable: divisors of 2 are {1, 2}, and 1 + 2 = 3. -/
theorem representable_3 : IsRepresentable 3 := by
  sorry

/-- 4 is representable: divisors of 3 are {1, 3}, and 1 + 3 = 4. -/
theorem representable_4 : IsRepresentable 4 := by
  sorry

/-- 6 is representable: divisors of 6 are {1, 2, 3, 6}, and 1 + 2 + 3 = 6. -/
theorem representable_6 : IsRepresentable 6 := by
  sorry

/-- 7 is representable: divisors of 4 are {1, 2, 4}, and 1 + 2 + 4 = 7. -/
theorem representable_7 : IsRepresentable 7 := by
  sorry

/-- 8 is representable: divisors of 7 are {1, 7}, and 1 + 7 = 8. -/
theorem representable_8 : IsRepresentable 8 := by
  sorry

/-
## f values for small cases
-/

/-- If n is not representable, then the witness set is empty. -/
theorem witnesses_empty_of_not_representable {n : ℕ} (h : ¬IsRepresentable n) :
    witnesses n = ∅ := by
  ext m
  simp [witnesses, IsRepresentable]
  intro hm hmem
  exact h ⟨m, hm, hmem⟩

/-- f(n) = 0 when n is not representable. -/
theorem f_eq_zero_of_not_representable {n : ℕ} (h : ¬IsRepresentable n) :
    f n = 0 := by
  unfold f
  rw [witnesses_empty_of_not_representable h]
  simp

/-- f(2) = 0 because 2 is not representable. -/
theorem f_2_eq_zero : f 2 = 0 :=
  f_eq_zero_of_not_representable not_representable_2

/-- f(5) = 0 because 5 is not representable. -/
theorem f_5_eq_zero : f 5 = 0 :=
  f_eq_zero_of_not_representable not_representable_5

/-
## Structural Properties
-/

/-- Partial sums are monotonically increasing: adding more divisors
    increases the sum (since all divisors are positive). -/
theorem sumSmallestDivisors_mono (m : ℕ) (hm : m ≥ 1) (k₁ k₂ : ℕ)
    (hk : k₁ ≤ k₂) (hk₂ : k₂ ≤ (sortedDivisors m).length) :
    sumSmallestDivisors m k₁ ≤ sumSmallestDivisors m k₂ := by
  sorry

/-- If n is representable via m ≤ bound, then n is representable. -/
theorem representable_of_bounded {n bound : ℕ} (h : IsRepresentableBounded n bound) :
    IsRepresentable n := by
  obtain ⟨m, hm1, _, hmem⟩ := h
  exact ⟨m, hm1, hmem⟩

/-
## The Open Problem

The main questions concern the asymptotic behavior of f(n):
-/

/-- **Open Question I** (DISPROVED by Tao): Is f(n) = o(n)?
    In other words, does f(n)/n → 0 as n → ∞? -/
def erdos_1054_part_i : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    IsRepresentable n → (f n : ℝ) < ε * (n : ℝ)

/-- The set of "bad" n up to M where f(n) is not small relative to n.
    Formulated as a set rather than Finset to avoid decidability issues. -/
noncomputable def badSet (ε : ℝ) (M : ℕ) : Set ℕ :=
  { n : ℕ | n < M ∧ IsRepresentable n ∧ (f n : ℝ) ≥ ε * (n : ℝ) }

/-- **Open Question II** (OPEN): Is f(n) = o(n) for almost all n?
    "Almost all" means: for any ε > 0, the natural density of
    {n : f(n) ≥ εn} is 0.
    We state this using the counting formulation with Set.ncard. -/
def erdos_1054_part_ii : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ δ : ℝ, δ > 0 → ∃ N : ℕ, ∀ M : ℕ, M ≥ N →
    ((badSet ε M).ncard : ℝ) < δ * (M : ℝ)

/-- **Open Question III**: Is limsup f(n)/n = ∞?
    This asks whether there are arbitrarily large n where f(n) ≥ c·n. -/
def erdos_1054_part_iii : Prop :=
  ∀ C : ℝ, ∃ n : ℕ, n ≥ 1 ∧ IsRepresentable n ∧ (f n : ℝ) ≥ C * (n : ℝ)

/-
## Tao's Partial Result

Terry Tao disproved the strong unconditional claim that f(n) = o(n).
He showed that the upper density of {n : f(n) ≤ δn} is O(δ²),
meaning many n have f(n) comparable to n.
-/

/-- Tao's result: Part I is FALSE.
    There exist infinitely many n with f(n) ≥ c·n for some constant c > 0. -/
axiom tao_disproves_part_i : ¬erdos_1054_part_i

/-- Part III follows from Tao's result: limsup f(n)/n = ∞ because
    infinitely many n satisfy f(n) ≥ cn. -/
theorem part_iii_from_tao (h : ¬erdos_1054_part_i) : erdos_1054_part_iii := by
  sorry

/-
## The Two Exceptional Values

Why are exactly 2 and 5 the only non-representable values?

For n = 2: Trapped between k=1 (sum=1) and k≥2 (sum≥3).
For n = 5: If d₂ = 4, then 2|m so d₂ ≤ 2, contradiction.
           If k ≥ 3, sum ≥ 1 + 2 + 3 = 6 > 5.

It is conjectured that every n ≥ 6 with n ≠ 2, 5 is representable.
This would follow from a strong form of Goldbach's conjecture.
-/

/-- Conjecture: all n ≥ 6 are representable. This is believed true
    but a proof would require a strong Goldbach-type result. -/
axiom all_large_representable : ∀ n : ℕ, n ≥ 6 → IsRepresentable n

/-- Combining all results: the only non-representable values are 0, 2, and 5.
    Uses the representability of 1, 3, 4 and the all_large_representable axiom. -/
theorem exceptional_values :
    ∀ n : ℕ, ¬IsRepresentable n → n = 0 ∨ n = 2 ∨ n = 5 := by
  sorry

/-
## Examples of Divisor Sums

Partial sums of sorted divisors for small numbers:
- m = 1: divisors [1], partial sums [1]
- m = 2: divisors [1, 2], partial sums [1, 3]
- m = 3: divisors [1, 3], partial sums [1, 4]
- m = 4: divisors [1, 2, 4], partial sums [1, 3, 7]
- m = 5: divisors [1, 5], partial sums [1, 6]
- m = 6: divisors [1, 2, 3, 6], partial sums [1, 3, 6, 12]
- m = 7: divisors [1, 7], partial sums [1, 8]
- m = 8: divisors [1, 2, 4, 8], partial sums [1, 3, 7, 15]
- m = 9: divisors [1, 3, 9], partial sums [1, 4, 13]
- m = 10: divisors [1, 2, 5, 10], partial sums [1, 3, 8, 18]

Notice that 2 and 5 never appear as partial sums!
-/

end Erdos1054
