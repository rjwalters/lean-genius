/-
Erdős Problem #1056: Consecutive Interval Products ≡ 1 (mod p)

**Statement**: Let k ≥ 2. Does there exist a prime p and consecutive intervals
I₁, ..., Iₖ such that ∏_{n∈Iᵢ} n ≡ 1 (mod p) for all 1 ≤ i ≤ k?

**Status**: OPEN (for general k)

**Known Results**:
- k=2 (Erdős 1979): 3·4 ≡ 5·6·7 ≡ 1 (mod 11)
- k=3 (Makowski 1983): 2·3·4·5 ≡ 6·7·8·9·10·11 ≡ 12·13·14·15 ≡ 1 (mod 17)

**Related Question** (Noll-Simmons): Are there solutions to
q₁! ≡ q₂! ≡ ... ≡ qₖ! (mod p) for arbitrarily large k?

Reference: https://erdosproblems.com/1056
Problem A15 in Guy's "Unsolved Problems in Number Theory"
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos1056

/-
## Part I: Basic Definitions
-/

/-- An interval [a, b] in ℕ. -/
def Interval (a b : ℕ) : Finset ℕ := Finset.Icc a b

/-- Product of all integers in an interval. -/
def intervalProduct (a b : ℕ) : ℕ := ∏ n ∈ Interval a b, n

/-- Check if an interval product ≡ 1 (mod p). -/
def isCongruentToOne (a b p : ℕ) : Prop :=
  intervalProduct a b % p = 1

/-- A sequence of k consecutive intervals (each starts where previous ends + 1). -/
structure ConsecutiveIntervals (k : ℕ) where
  starts : Fin k → ℕ
  ends : Fin k → ℕ
  valid : ∀ i, starts i ≤ ends i
  consecutive : ∀ i : Fin (k - 1),
    starts ⟨i.val + 1, by omega⟩ = ends i + 1

/-- All k intervals have product ≡ 1 (mod p). -/
def AllCongruentToOne (ci : ConsecutiveIntervals k) (p : ℕ) : Prop :=
  ∀ i : Fin k, isCongruentToOne (ci.starts i) (ci.ends i) p

/-- The main question: for k ≥ 2, does such a configuration exist? -/
def ExistsConfiguration (k : ℕ) : Prop :=
  ∃ (p : ℕ) (ci : ConsecutiveIntervals k), p.Prime ∧ AllCongruentToOne ci p

/-
## Part II: Known Examples
-/

/-- k=2: Erdős's example (1979).
    3·4 = 12 ≡ 1 (mod 11)
    5·6·7 = 210 ≡ 1 (mod 11) -/
theorem erdos_k2_example : ExistsConfiguration 2 := by
  use 11
  use {
    starts := ![3, 5]
    ends := ![4, 7]
    valid := by intro i; fin_cases i <;> simp
    consecutive := by intro i; fin_cases i; simp
  }
  constructor
  · norm_num
  · intro i
    fin_cases i <;> native_decide

/-- Verification: 3·4 = 12 ≡ 1 (mod 11). -/
example : 12 % 11 = 1 := by native_decide

/-- Verification: 5·6·7 = 210 ≡ 1 (mod 11). -/
example : 210 % 11 = 1 := by native_decide

/-- k=3: Makowski's example (1983).
    2·3·4·5 = 120 ≡ 1 (mod 17)
    6·7·8·9·10·11 = 332640 ≡ 1 (mod 17)
    12·13·14·15 = 32760 ≡ 1 (mod 17) -/
theorem makowski_k3_example : ExistsConfiguration 3 := by
  use 17
  use {
    starts := ![2, 6, 12]
    ends := ![5, 11, 15]
    valid := by intro i; fin_cases i <;> simp
    consecutive := by intro i; fin_cases i <;> simp
  }
  constructor
  · norm_num
  · intro i
    fin_cases i <;> native_decide

/-- Verification: 2·3·4·5 = 120 ≡ 1 (mod 17). -/
example : 120 % 17 = 1 := by native_decide

/-- Verification: 6·7·8·9·10·11 = 332640 ≡ 1 (mod 17). -/
example : 332640 % 17 = 1 := by native_decide

/-- Verification: 12·13·14·15 = 32760 ≡ 1 (mod 17). -/
example : 32760 % 17 = 1 := by native_decide

/-
## Part III: The Main Conjecture
-/

/-- The main open question: Does ExistsConfiguration k hold for all k ≥ 2? -/
def mainConjecture : Prop := ∀ k ≥ 2, ExistsConfiguration k

/-- What we know so far. -/
theorem known_cases : ExistsConfiguration 2 ∧ ExistsConfiguration 3 :=
  ⟨erdos_k2_example, makowski_k3_example⟩

/-
## Part IV: Factorial Variant (Noll-Simmons)
-/

/-- The Noll-Simmons generalization: do there exist q₁ < ... < qₖ such that
    q₁! ≡ q₂! ≡ ... ≡ qₖ! (mod p) for some prime p? -/
def FactorialVariant (k : ℕ) : Prop :=
  ∃ (p : ℕ) (qs : Fin k → ℕ),
    p.Prime ∧
    (∀ i j : Fin k, i < j → qs i < qs j) ∧  -- strictly increasing
    (∀ i j : Fin k, (qs i).factorial % p = (qs j).factorial % p)

/-- Note: interval products relate to factorials.
    Product of [a, b] = b! / (a-1)! -/
theorem intervalProduct_factorial (a b : ℕ) (ha : a ≥ 1) (hab : a ≤ b) :
    intervalProduct a b = b.factorial / (a - 1).factorial := by
  sorry

/-
## Part V: Observations
-/

/-- The primes 11 and 17 that work have special structure.
    11 = 2·5 + 1 (related to products 3·4 = 12 and 5·6·7 = 210)
    17 = 2·8 + 1 -/
axiom prime_structure : ∀ p : ℕ, p.Prime →
    (∃ ci : ConsecutiveIntervals 2, AllCongruentToOne ci p) →
    ∃ a b : ℕ, p = a * b + 1 ∧ a ∣ (p - 1)

/-- For Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p.
    This constrains which factorials can be ≡ 1 (mod p). -/
theorem wilson_constraint (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q < p) :
    q.factorial % p = 1 → q ≤ 1 ∨ ∃ (r : ℕ), r > q ∧ r < p ∧
      (r.factorial * q.factorial) % p = (p - 1) := by
  sorry

/-
## Part VI: Summary
-/

/-- Erdős Problem #1056: Summary

    **Problem**: For k ≥ 2, find prime p and k consecutive intervals
    with products all ≡ 1 (mod p).

    **Known**:
    - k=2: p=11, intervals [3,4] and [5,7]
    - k=3: p=17, intervals [2,5], [6,11], [12,15]

    **Open**: Does this hold for all k ≥ 2?

    **Generalization** (Noll-Simmons): q₁! ≡ ... ≡ qₖ! (mod p) for large k? -/
theorem erdos_1056_summary :
    ExistsConfiguration 2 ∧
    ExistsConfiguration 3 ∧
    (mainConjecture ↔ ∀ k ≥ 2, ExistsConfiguration k) := by
  refine ⟨erdos_k2_example, makowski_k3_example, ?_⟩
  rfl

end Erdos1056
