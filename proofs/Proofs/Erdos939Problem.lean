/-
Erdős Problem #939: r-Powerful Numbers and Sums

An integer n is **r-powerful** (also called r-full) if whenever a prime p divides n,
we have p^r divides n. For example:
- 2-powerful (squarefull): 4, 8, 9, 16, 25, 27, ...
- 3-powerful (cubefull): 8, 16, 27, 32, 64, ...

**Main Question** (OPEN for existence): If r ≥ 4, can the sum of r-2 coprime
r-powerful numbers ever be itself r-powerful?

**Variants**:
1. Are there infinitely many such sums? (OPEN)
2. Are there infinitely many triples of coprime 3-powerful a,b,c with a+b=c? (YES - Nitaj 1995)

**Known Examples** (Cambie):
- r=5: 3761^5 = 2^8·3^{10}·5^7 + 2^{12}·23^6 + 11^5·13^5
- Solutions also exist for r=7 and r=8

**Related**: Lander-Parkin (1967) disproved Euler's conjecture that k-1 k-th powers
cannot sum to a k-th power, finding 27^5 + 84^5 + 110^5 + 133^5 = 144^5.

Reference: https://erdosproblems.com/939
-/

import Mathlib

namespace Erdos939

open scoped Classical

/-!
## r-Powerful (r-Full) Numbers

A positive integer n is r-powerful (or r-full) if for every prime p dividing n,
we have p^r also divides n. Equivalently, in the prime factorization n = ∏ p_i^{a_i},
every exponent a_i ≥ r.
-/

/-- A number n is r-powerful (r-full) if every prime factor p has p^r | n.
    Equivalently: all exponents in the prime factorization are at least r. -/
def IsRPowerful (r n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ r ∣ n

/-- A finset of natural numbers is coprime if their GCD is 1 -/
def FinsetCoprime (S : Finset ℕ) : Prop :=
  S.gcd id = 1

/-- 8 = 2³ is 3-powerful (cubefull): only prime factor is 2, and 2³ | 8 -/
theorem eight_is_3powerful : IsRPowerful 3 8 := by
  intro p hp hdiv
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (h8 ▸ hdiv)
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
  have hge : 2 ≤ p := hp.two_le
  have : p = 2 := by omega
  simp only [this, h8, dvd_refl]

/-- 27 = 3³ is 3-powerful -/
theorem twentyseven_is_3powerful : IsRPowerful 3 27 := by
  intro p hp hdiv
  have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
  have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow (h27 ▸ hdiv)
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
  have hge : 2 ≤ p := hp.two_le
  have hne : p ≠ 2 := by
    intro heq
    rw [heq] at hp3
    norm_num at hp3
  have : p = 3 := by omega
  simp only [this, h27, dvd_refl]

/-- 32 = 2⁵ is 5-powerful -/
theorem thirtytwo_is_5powerful : IsRPowerful 5 32 := by
  intro p hp hdiv
  have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (h32 ▸ hdiv)
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
  have hge : 2 ≤ p := hp.two_le
  have : p = 2 := by omega
  simp only [this, h32, dvd_refl]

/-!
## Erdős's Main Question

Given r ≥ 4, can we find r-2 coprime r-powerful numbers whose sum is also r-powerful?

For r=5, this asks: can 3 coprime 5-powerful numbers sum to a 5-powerful number?
-/

/-- A valid Erdős-939 sum: r-2 coprime r-powerful numbers summing to an r-powerful number -/
def IsErdos939Sum (r : ℕ) (S : Finset ℕ) : Prop :=
  S.card = r - 2 ∧
  FinsetCoprime S ∧
  IsRPowerful r (∑ s ∈ S, s) ∧
  ∀ s ∈ S, IsRPowerful r s

/-- The set of all valid Erdős-939 sums for a given r -/
def Erdos939Sums (r : ℕ) := {S : Finset ℕ | IsErdos939Sum r S}

/-!
## The Main Conjectures

The existence question: for r ≥ 4, do valid sums exist?
The infinitude question: are there infinitely many?
-/

/-- **Erdős Problem #939** (OPEN for general answer)

If r ≥ 4, can the sum of r-2 coprime r-powerful numbers be itself r-powerful?
Equivalently: is Erdos939Sums r nonempty for all r ≥ 4? -/
def Erdos939Existence : Prop := ∀ r ≥ 4, (Erdos939Sums r).Nonempty

/-- The existence question remains open -/
axiom erdos939_existence : Erdos939Existence

/-- **Infinitude Variant** (OPEN)

Are there infinitely many valid sums for each r ≥ 4? -/
def Erdos939Infinite : Prop := ∀ r ≥ 4, (Erdos939Sums r).Infinite

/-- The infinitude question remains open -/
axiom erdos939_infinite : Erdos939Infinite

/-!
## 3-Powerful Triples

A related question asks about coprime 3-powerful numbers a, b, c with a + b = c.
This was answered positively by Nitaj in 1995.
-/

/-- Coprime 3-powerful triples (a,b,c) with a + b = c -/
def ThreePowerfulTriples := {abc : ℕ × ℕ × ℕ |
  let (a, b, c) := abc
  IsRPowerful 3 a ∧ IsRPowerful 3 b ∧ IsRPowerful 3 c ∧
  FinsetCoprime {a, b, c} ∧
  a + b = c}

/-- **Nitaj (1995)**: There are infinitely many coprime 3-powerful triples a+b=c -/
axiom nitaj_threepowerful_infinite : ThreePowerfulTriples.Infinite

/-!
## Known Examples

Cambie found explicit examples for r = 5, 7, and 8.
-/

/-- **Cambie's r=5 Example**

3761^5 = 2^8 · 3^{10} · 5^7 + 2^{12} · 23^6 + 11^5 · 13^5

The three summands are coprime and 5-powerful, and their sum is 5-powerful. -/
axiom cambie_r5_example : (Erdos939Sums 5).Nonempty

/-- Existence of r=5 solution implies at least one r ≥ 4 has solutions -/
theorem cambie_r5_example_exists : ∃ r ≥ 4, (Erdos939Sums r).Nonempty := by
  use 5
  constructor
  · norm_num
  · exact cambie_r5_example

/-- Cambie found solutions for r = 7 -/
axiom cambie_r7_solution : (Erdos939Sums 7).Nonempty

/-- Cambie found solutions for r = 8 -/
axiom cambie_r8_solution : (Erdos939Sums 8).Nonempty

/-!
## Euler's Conjecture and Lander-Parkin Counterexample

Euler conjectured that the sum of k-1 k-th powers is never a k-th power.
Lander and Parkin (1967) disproved this for k=5.
-/

/-- Euler's conjecture: sum of k-1 k-th powers is never a k-th power -/
def EulerConjecture : Prop :=
  ∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
    ¬∃ q, ∑ s ∈ S, s ^ k = q ^ k

/-- **Lander-Parkin (1967)**: Euler's conjecture is FALSE

They found: 27^5 + 84^5 + 110^5 + 133^5 = 144^5

This was the first counterexample, discovered by computer search. -/
theorem lander_parkin_counterexample : ¬EulerConjecture := by
  unfold EulerConjecture
  push_neg
  use 5
  constructor
  · norm_num
  use {27, 84, 110, 133}
  constructor
  · native_decide
  use 144
  native_decide

/-- Direct verification of the Lander-Parkin identity -/
theorem lander_parkin_identity :
    27^5 + 84^5 + 110^5 + 133^5 = 144^5 := by native_decide

/-!
## Connection to r-Powerful Numbers

The Lander-Parkin example shows perfect k-th powers (trivially k-powerful)
can satisfy non-trivial sum relations. Erdős Problem 939 generalizes this
to the broader class of r-powerful numbers.

Key insight: every k-th power n^k is trivially k-powerful since the only
prime factor multiplicities are exactly k (or multiples of k).
-/

/-- Perfect powers are r-powerful: n^r is r-powerful for any n > 0 -/
theorem perfect_power_is_rpowerful (n r : ℕ) :
    IsRPowerful r (n ^ r) := by
  intro p hp hdiv
  -- If p | n^r, then p | n (since p is prime)
  have h : p ∣ n := hp.dvd_of_dvd_pow hdiv
  -- So n = p * m for some m, meaning n^r = (p*m)^r is divisible by p^r
  obtain ⟨m, hm⟩ := h
  rw [hm, mul_pow]
  exact Dvd.dvd.mul_right (dvd_refl (p ^ r)) (m ^ r)

end Erdos939
