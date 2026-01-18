/-
  Erdős Problem #402: Graham's GCD Conjecture

  Source: https://erdosproblems.com/402
  Status: SOLVED (Balasubramanian-Soundararajan 1996)

  Statement:
  For any finite set A ⊂ ℕ, there exist a, b ∈ A such that
  gcd(a, b) ≤ a / |A|.

  Answer: TRUE

  History:
  - Graham (1970): Conjectured the result
  - Szegedy (1986): Proved for all sufficiently large sets
  - Zaharescu (1987): Independent proof for large sets
  - Balasubramanian & Soundararajan (1996): Completed proof for all finite sets

  Graham's Additional Conjecture:
  If A has no common divisor (gcd of all elements is 1), then equality
  gcd(a,b) = a/|A| is achieved only when:
  - A = {1, 2, ..., n}, or
  - A = {L/1, L/2, ..., L/n} where L = lcm(1, ..., n), or
  - A = {2, 3, 4, 6}

  Reference: Graham (1970), Balasubramanian-Soundararajan (1996)
-/

import Mathlib

namespace Erdos402

open Nat Finset

/-! ## Main Statement -/

/--
**Graham's GCD Conjecture (Erdős #402)**:
For any finite set A ⊂ ℕ with |A| ≥ 1, there exist elements a, b ∈ A
such that gcd(a, b) ≤ a / |A|.
-/
theorem erdos_402_graham_conjecture (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) :
    ∃ a ∈ A, ∃ b ∈ A, Nat.gcd a b ≤ a / A.card := by
  -- Proved by Balasubramanian and Soundararajan (1996)
  sorry

/-! ## Equivalent Formulation -/

/--
Alternative formulation: The minimum gcd ratio is at most 1/|A|.
-/
def MinGcdRatio (A : Finset ℕ) : ℚ :=
  if h : A.Nonempty ∧ ∀ x ∈ A, x > 0 then
    A.inf' h.1 fun a =>
      A.inf' h.1 fun b =>
        (Nat.gcd a b : ℚ) / a
  else 1

theorem erdos_402_ratio_bound (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) :
    ∃ a ∈ A, ∃ b ∈ A, (Nat.gcd a b : ℚ) / a ≤ 1 / A.card := by
  sorry

/-! ## Special Cases -/

/-- For singleton sets, the result is trivial: gcd(a,a) = a ≤ a/1 = a. -/
theorem erdos_402_singleton (a : ℕ) (_ : a > 0) :
    ∃ x ∈ ({a} : Finset ℕ), ∃ y ∈ ({a} : Finset ℕ),
    Nat.gcd x y ≤ x / ({a} : Finset ℕ).card := by
  use a, mem_singleton_self a, a, mem_singleton_self a
  simp [Nat.gcd_self]

/-- For {1, 2, ..., n}, we have gcd(1,1) = 1 ≤ 1/n for n = 1. -/
theorem erdos_402_range (n : ℕ) (hn : n ≥ 1) :
    ∃ a ∈ Finset.range (n + 1) \ {0}, ∃ b ∈ Finset.range (n + 1) \ {0},
    Nat.gcd a b ≤ a / (Finset.range (n + 1) \ {0}).card := by
  -- Use a = n, b = n: gcd(n,n) = n, and n/n = 1, so n ≤ 1 only for n = 1
  -- Better: use a = 1, b = 1 for n = 1; otherwise need different approach
  -- For this formalization, we use sorry for the general case
  sorry

/-! ## The {2, 3, 4, 6} Example -/

/-- The special set {2, 3, 4, 6} mentioned by Graham. -/
def GrahamSpecialSet : Finset ℕ := {2, 3, 4, 6}

theorem graham_special_card : GrahamSpecialSet.card = 4 := by native_decide

/-- In {2, 3, 4, 6}, gcd(4, 3) = 1 and 4/4 = 1, so 1 ≤ 1 ✓ -/
theorem graham_special_example :
    ∃ a ∈ GrahamSpecialSet, ∃ b ∈ GrahamSpecialSet,
    Nat.gcd a b ≤ a / GrahamSpecialSet.card := by
  -- Use a = 4, b = 3: gcd(4, 3) = 1, and 4/4 = 1, so 1 ≤ 1 ✓
  use 4
  constructor
  · decide
  use 3
  constructor
  · decide
  -- gcd(4, 3) = 1, 4/4 = 1
  native_decide

/-! ## Graham's Equality Characterization -/

/--
A set A has no common divisor if gcd of all elements is 1.
-/
def HasNoCommonDivisor (A : Finset ℕ) : Prop :=
  A.gcd id = 1

/--
Graham's characterization of equality cases.
When A has no common divisor, equality gcd(a,b) = a/|A| for the optimal pair
is achieved only for:
1. A = {1, ..., n}
2. A = {lcm(1,...,n)/1, ..., lcm(1,...,n)/n}
3. A = {2, 3, 4, 6}
-/
def IsGrahamEqualityCase (A : Finset ℕ) : Prop :=
  (∃ n : ℕ, n ≥ 1 ∧ A = Finset.range (n + 1) \ {0}) ∨
  (∃ n : ℕ, n ≥ 1 ∧ ∃ L : ℕ, L = (Finset.range (n + 1) \ {0}).lcm id ∧
    A = (Finset.range (n + 1) \ {0}).image fun k => L / k) ∨
  A = GrahamSpecialSet

/--
**Graham's Equality Conjecture**: The only primitive sets achieving equality
in the GCD bound are the three families described above.
-/
theorem erdos_402_equality_cases (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) (hprim : HasNoCommonDivisor A)
    (heq : ∀ a ∈ A, ∀ b ∈ A, Nat.gcd a b ≥ a / A.card) :
    IsGrahamEqualityCase A := by
  -- Proved by Szegedy for large sets
  sorry

/-! ## Key Lemmas -/

/-- For coprime elements, gcd(a,b) = 1 ≤ a/|A| when |A| ≤ a. -/
theorem gcd_one_suffices (A : Finset ℕ) (a b : ℕ)
    (hcop : Nat.Coprime a b) (hcard : A.card ≤ a) (hApos : A.card > 0) :
    Nat.gcd a b ≤ a / A.card := by
  rw [Nat.Coprime] at hcop
  rw [hcop]
  exact Nat.one_le_div_iff hApos |>.mpr hcard

/-- If A = {1} (singleton containing 1), gcd(1,1) = 1 ≤ 1/1 = 1 works. -/
theorem one_in_singleton_set :
    ∃ a ∈ ({1} : Finset ℕ), ∃ b ∈ ({1} : Finset ℕ), Nat.gcd a b ≤ a / ({1} : Finset ℕ).card := by
  use 1, mem_singleton_self 1, 1, mem_singleton_self 1
  simp [Nat.gcd_self]

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #402 (Graham's Conjecture) asks: for any finite set A ⊂ ℕ,
do there exist a, b ∈ A with gcd(a,b) ≤ a/|A|?

**Answer: YES**

The problem was progressively solved:
- Szegedy (1986) and Zaharescu (1987) proved it for large sets
- Balasubramanian & Soundararajan (1996) completed the proof for all sets

**Graham's Additional Conjecture** characterizes when equality holds:
only for {1,...,n}, {L/1,...,L/n}, or {2,3,4,6} (when A is primitive).

**References**:
- Graham, R. L. (1970): Original conjecture
- Balasubramanian, R. & Soundararajan, K. (1996): Complete proof
-/

end Erdos402
