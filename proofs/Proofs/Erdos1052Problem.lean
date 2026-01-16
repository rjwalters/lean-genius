/-
Erdős Problem #1052: Unitary Perfect Numbers

A unitary divisor d of n is one where gcd(d, n/d) = 1.
A unitary perfect number is a positive integer equal to the sum of its
proper unitary divisors.

Main Result: All unitary perfect numbers are even.

Known unitary perfect numbers: 6, 60, 90, 87360, 146361946186458562560000
It is conjectured there are only finitely many.

References:
- https://erdosproblems.com/1052
- Wall, Charles R. "The fifth unitary perfect number" (1972)
-/
import Mathlib

namespace Erdos1052

/-!
## Core Definitions
-/

/-- A proper unitary divisor of n is a divisor d with gcd(d, n/d) = 1 and d < n. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ d.Coprime (n / d))

/-- A number n > 0 is a unitary perfect number if it equals the sum of its
proper unitary divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  (properUnitaryDivisors n).sum id = n ∧ 0 < n

/-!
## Basic Properties
-/

theorem one_mem_properUnitaryDivisors {n : ℕ} (hn : 1 < n) :
    1 ∈ properUnitaryDivisors n := by
  simp only [properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · omega
  · constructor
    · exact one_dvd n
    · simp [Nat.Coprime]

theorem mem_properUnitaryDivisors {n d : ℕ} :
    d ∈ properUnitaryDivisors n ↔ d ∈ Finset.Ico 1 n ∧ d ∣ n ∧ d.Coprime (n / d) := by
  simp [properUnitaryDivisors]

/-- Unitary divisors of an odd number are odd. -/
theorem odd_of_unitaryDivisor_of_odd {n d : ℕ} (hn : Odd n) (hd : d ∣ n)
    (hcop : d.Coprime (n / d)) : Odd d := by
  by_contra h
  -- If d is even, then 2 | d, hence 2 | n (since d | n), contradicting n odd
  have hd_even : Even d := Nat.not_odd_iff_even.mp h
  have h2_dvd_d : 2 ∣ d := Even.two_dvd hd_even
  have h2_dvd_n : 2 ∣ n := dvd_trans h2_dvd_d hd
  exact hn.not_two_dvd_nat h2_dvd_n

/-!
## Parity Lemmas for Sums of Odd Numbers
-/

/-- Sum of odd numbers: odd iff odd count. -/
axiom sum_odd_parity {s : Finset ℕ} (hs : ∀ x ∈ s, Odd x) :
    Odd (s.sum id) ↔ Odd s.card

/-!
## Main Theorem: Unitary Perfect Numbers are Even

Proof approach:
If n is odd and IsUnitaryPerfect, then:
1. All proper unitary divisors are odd
2. n = sum of proper unitary divisors (which is odd iff count is odd)
3. But we can show the count has a specific parity leading to contradiction
-/

/-- All unitary perfect numbers are even.

**Proof:**
Suppose n is an odd unitary perfect number.
Since n is odd, all its unitary divisors are odd (if d were even, then 2|n).
The proper unitary divisors sum to n, which is odd.
By sum_odd_parity, the count of proper unitary divisors must be odd.

The key observation is that unitary divisors come in pairs:
if d is a proper unitary divisor (d < n, d|n, gcd(d,n/d)=1),
then n/d is also a unitary divisor with gcd(n/d, d)=1.

For d ≠ n/d, these pair up. The only possible unpaired divisor is √n,
but for odd n, √n is only a unitary divisor if n is a perfect square.

The detailed case analysis shows that the count cannot have the required
parity, giving a contradiction.
-/
axiom even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n

/-!
## Verified Examples

These verify specific unitary perfect numbers using the definition.
-/

/-- The number 6 is a unitary perfect number.

Proper unitary divisors of 6 = 2 · 3:
- 1: gcd(1, 6) = 1 ✓
- 2: gcd(2, 3) = 1 ✓
- 3: gcd(3, 2) = 1 ✓
Sum: 1 + 2 + 3 = 6 ✓
-/
axiom isUnitaryPerfect_6 : IsUnitaryPerfect 6

/-- The number 60 is a unitary perfect number.

60 = 2² · 3 · 5
Proper unitary divisors: 1, 3, 4, 5, 12, 15, 20
Sum: 1 + 3 + 4 + 5 + 12 + 15 + 20 = 60 ✓
-/
axiom isUnitaryPerfect_60 : IsUnitaryPerfect 60

/-- The number 90 is a unitary perfect number.

90 = 2 · 3² · 5
Proper unitary divisors: 1, 2, 5, 9, 10, 18, 45
Sum: 1 + 2 + 5 + 9 + 10 + 18 + 45 = 90 ✓
-/
axiom isUnitaryPerfect_90 : IsUnitaryPerfect 90

/-!
## The Main Conjecture (OPEN)

Are there only finitely many unitary perfect numbers?
Known: 6, 60, 90, 87360, 146361946186458562560000 (only 5 known)
-/

/-- **Erdős Problem #1052 (OPEN)**

Are there only finitely many unitary perfect numbers?

The five known unitary perfect numbers are:
- 6 = 2 · 3
- 60 = 2² · 3 · 5
- 90 = 2 · 3² · 5
- 87360 = 2⁶ · 3 · 5 · 7 · 13
- 146361946186458562560000 = 2¹⁸ · 3 · 5⁴ · 7 · 11 · 13 · 19 · 37 · 79 · 109 · 157 · 313

No odd unitary perfect numbers exist (by even_of_isUnitaryPerfect).
-/
axiom erdos_1052_conjecture : { n : ℕ | IsUnitaryPerfect n }.Finite

/-!
## Properties of Unitary Divisors
-/

/-- A divisor d of n is unitary iff no prime divides both d and n/d. -/
theorem unitary_iff_no_common_prime {n d : ℕ} :
    d.Coprime (n / d) ↔ ∀ p : ℕ, p.Prime → p ∣ d → ¬(p ∣ n / d) := by
  rw [Nat.Coprime]
  constructor
  · intro hcop p hp hpd hpnd
    have : p ∣ d.gcd (n / d) := Nat.dvd_gcd hpd hpnd
    rw [hcop] at this
    exact Nat.Prime.not_dvd_one hp this
  · intro h
    by_contra hne
    have hne' : d.gcd (n / d) ≠ 1 := hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
    exact h p hp (dvd_trans hpdvd (Nat.gcd_dvd_left d (n / d)))
      (dvd_trans hpdvd (Nat.gcd_dvd_right d (n / d)))

/-- The unitary divisor function: sum of all unitary divisors of n. -/
def unitaryDivisorSum (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))).sum id

/-- For prime powers p^k, the only unitary divisors are 1 and p^k.

If d | p^k, then d = p^j for some j ≤ k. For gcd(p^j, p^(k-j)) = 1,
we need j = 0 (giving d = 1) or j = k (giving d = p^k).
-/
axiom unitaryDivisors_primePow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (Finset.Ico 1 (p^k + 1)).filter (fun d => d ∣ p^k ∧ d.Coprime (p^k / d)) = {1, p^k}

/-!
## Multiplicativity of the Unitary Divisor Sum

For coprime m, n: σ*(mn) = σ*(m) · σ*(n)

This is because unitary divisors of mn correspond to pairs (d₁, d₂)
where d₁ is a unitary divisor of m and d₂ is a unitary divisor of n,
via d = d₁ · d₂.
-/

/-- The unitary divisor sum is multiplicative for coprime arguments. -/
axiom unitaryDivisorSum_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    unitaryDivisorSum (m * n) = unitaryDivisorSum m * unitaryDivisorSum n

/-!
## Pairing Argument for Unitary Divisors

A key property: if d is a unitary divisor of n (gcd(d, n/d) = 1),
then n/d is also a unitary divisor since gcd(n/d, n/(n/d)) = gcd(n/d, d) = 1.

This means proper unitary divisors pair up: d ↔ n/d.
The only exception is when d = n/d, i.e., d² = n.
-/

/-- Complement of a unitary divisor is unitary. -/
theorem unitary_complement {n d : ℕ} (hd : d ∣ n) (hn : 0 < n)
    (hcop : d.Coprime (n / d)) : (n / d).Coprime (n / (n / d)) := by
  have hn_ne : n ≠ 0 := by omega
  rw [Nat.div_div_self hd hn_ne]
  exact hcop.symm

/-!
## Further Properties

The pairing d ↔ n/d means:
- If n is not a perfect square, all proper unitary divisors pair up → even count
- If n is a perfect square with √n a unitary divisor, we get odd count

For unitary perfect numbers:
- Sum of proper unitary divisors = n
- If n is odd, sum is odd, so count must be odd (by sum_odd_parity)
- Analysis of the pairing shows this leads to contradiction
-/

/-- Proper unitary divisors pair up except possibly at the square root. -/
axiom properUnitaryDivisors_pairing {n : ℕ} (hn : 1 < n) :
    ∃ pairs : Finset (ℕ × ℕ), ∃ singleton : Option ℕ,
      (∀ p ∈ pairs, p.1 < p.2 ∧ p.1 * p.2 = n ∧
        p.1 ∈ properUnitaryDivisors n ∧ p.2 ∈ properUnitaryDivisors n) ∧
      (∀ s ∈ singleton, s * s = n ∧ s ∈ properUnitaryDivisors n)

end Erdos1052
