import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

/-!
# Kummer's Theorem (1852)

## What This Proves
Kummer's theorem states that for a prime `p` and natural numbers `n ≥ k`, the highest power
of `p` dividing the binomial coefficient `C(n, k)` equals the number of carries when adding
`k` and `n - k` in base `p`.

$$\nu_p\binom{n}{k} = \text{(number of carries when adding } k \text{ and } n-k \text{ in base } p)$$

Equivalently, using the relationship with digit sums:

$$(p - 1) \cdot \nu_p\binom{n}{k} = S_p(k) + S_p(n-k) - S_p(n)$$

where $S_p(m)$ is the sum of digits of $m$ in base $p$.

## Historical Context
Ernst Kummer proved this theorem in 1852. It provides a beautiful connection between:
- The prime factorization of binomial coefficients
- The arithmetic of carries in positional numeral systems

This result is fundamental in combinatorics, number theory, and has applications in
the study of Pascal's triangle modulo primes.

## Relationship to Lucas' Theorem
Kummer's theorem can be derived from Lucas' theorem. If any digit of `k` exceeds the
corresponding digit of `n` in base `p`, then `C(n,k) ≡ 0 (mod p)`. The number of such
"borrows" determines the exact power of `p` dividing `C(n,k)`.

## Approach
- **Foundation (from Mathlib):** We use `Nat.Prime.multiplicity_choose` which directly
  proves Kummer's theorem by counting positions where carries occur.
- **Key Insight:** A carry at position `i` happens when `k % p^i + (n-k) % p^i ≥ p^i`.
- **Mathlib formulation:** The theorem is stated using the `multiplicity` function and
  a filtered count over positions.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Examples demonstrating the theorem
- [x] Connection to Lucas' theorem shown
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Nat.Prime.multiplicity_choose` : Kummer's theorem in terms of carries
- `Nat.Prime.multiplicity_choose'` : Alternative formulation for C(n+k, k)
- `multiplicity` : The p-adic valuation (highest power of p dividing a number)
- `Choose.lucas_theorem` : Lucas' theorem for binomial coefficients mod p
- `Nat.digits` : Digit representation in arbitrary base

## References
- Kummer, E. (1852). "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen"
- Granville, A. (1997). "Arithmetic properties of binomial coefficients"
-/

namespace KummerTheorem

open Nat Finset

/-! ## The Core Theorem

Kummer's theorem states that the multiplicity of a prime `p` in `C(n,k)` is the number
of positions where adding `k` and `n-k` in base `p` produces a carry.

A carry at position `i` occurs when:
  `k % p^i + (n - k) % p^i ≥ p^i`

This is the "borrow" when subtracting `k` from `n` in base `p`, equivalently. -/

/-- **Kummer's Theorem** (1852)

The multiplicity of prime `p` in `C(n, k)` equals the number of carries when
adding `k` and `n - k` in base `p`.

The carry positions are exactly those `i` where `k % p^i + (n-k) % p^i ≥ p^i`. -/
theorem kummer {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    multiplicity p (Nat.choose n k) =
      ((Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card :=
  Nat.Prime.multiplicity_choose hp hkn hnb

/-- Alternative formulation: multiplicity in `C(n + k, k)` counts carries when adding
    `k` and `n` in base `p`. -/
theorem kummer' {p n k b : ℕ} (hp : p.Prime) (hnb : Nat.log p (n + k) < b) :
    multiplicity p (Nat.choose (n + k) k) =
      ((Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + n % p ^ i).card :=
  Nat.Prime.multiplicity_choose' hp hnb

/-! ## Concrete Examples

Let's verify Kummer's theorem with specific examples. -/

/-- C(10, 4) = 210 = 2 × 3 × 5 × 7, so the multiplicity of 2 is 1.
    In base 2: 4 = 100, 6 = 110. Adding gives 1010 with 1 carry. -/
example : (Nat.choose 10 4).factorization 2 = 1 := by native_decide

/-- C(10, 4) has multiplicity 1 for prime 3.
    In base 3: 4 = 11, 6 = 20. Adding: 11 + 20 = 101 with 1 carry. -/
example : (Nat.choose 10 4).factorization 3 = 1 := by native_decide

/-- C(10, 4) = 210 has multiplicity 1 for prime 5.
    210 = 2 × 3 × 5 × 7 -/
example : (Nat.choose 10 4).factorization 5 = 1 := by native_decide

/-- C(10, 4) = 210 has multiplicity 1 for prime 7. -/
example : (Nat.choose 10 4).factorization 7 = 1 := by native_decide

/-- C(10, 4) = 210 is not divisible by 11 (no carries when adding in base 11). -/
example : (Nat.choose 10 4).factorization 11 = 0 := by native_decide

/-- C(6, 3) = 20 = 4 × 5, so multiplicity of 2 is 2.
    In base 2: 3 = 11, 3 = 11. Adding: 11 + 11 = 110 with 2 carries. -/
example : (Nat.choose 6 3).factorization 2 = 2 := by native_decide

/-- C(4, 2) = 6 = 2 × 3, so multiplicity of 2 is 1.
    In base 2: 2 = 10, 2 = 10. Adding: 10 + 10 = 100 with 1 carry. -/
example : (Nat.choose 4 2).factorization 2 = 1 := by native_decide

/-- A prime p divides C(p, k) for 0 < k < p.
    This follows from Kummer: in base p, k and p-k sum to p with exactly one carry. -/
example : 5 ∣ Nat.choose 5 2 := by native_decide

/-- C(p^n, p^m) where m < n has multiplicity n - m for prime p.
    Example: C(8, 2) = C(2³, 2¹) should have multiplicity 3 - 1 = 2... but let's check.
    Actually C(8, 2) = 28 = 4 × 7 = 2² × 7, so multiplicity is 2. ✓ -/
example : (Nat.choose 8 2).factorization 2 = 2 := by native_decide

/-! ## Power of p Divides C(p^n, k)

A special case: when choosing from a prime power. -/

/-- For 0 < k < p^n, we have p | C(p^n, k). -/
theorem prime_dvd_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hkn : k ≠ p ^ n) :
    p ∣ Nat.choose (p ^ n) k :=
  Nat.Prime.dvd_choose_pow hp hk hkn

/-! ## Connection to Lucas' Theorem

Kummer's theorem is deeply connected to Lucas' theorem. While Lucas tells us when
`C(n,k)` is divisible by `p` (namely when any digit of `k` exceeds the corresponding
digit of `n` in base `p`), Kummer tells us the exact power of `p` dividing `C(n,k)`.

From Mathlib, Lucas' theorem states:
  `C(n, k) ≡ ∏ᵢ C(nᵢ, kᵢ) (mod p)`
where `nᵢ` and `kᵢ` are the i-th digits of `n` and `k` in base `p`. -/

/-- Lucas' theorem: The binomial coefficient mod p is the product of digit-wise binomials.
    This is `Choose.lucas_theorem` from Mathlib. -/
example {n k p : ℕ} [Fact p.Prime] {a : ℕ} (hn : n < p ^ a) (hk : k < p ^ a) :
    Nat.choose n k ≡ ∏ i in Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] :=
  Choose.lucas_theorem hn hk

/-! ## The Digit Sum Formulation

There's an equivalent formulation in terms of digit sums:
  (p - 1) × ν_p(C(n,k)) = S_p(k) + S_p(n-k) - S_p(n)

where S_p(m) is the sum of the base-p digits of m.

This follows from Legendre's formula for factorial multiplicity and
the identity C(n,k) = n! / (k! × (n-k)!). -/

/-- Legendre's formula for factorial multiplicity in terms of digit sums. -/
theorem legendre_digit_sum {n p : ℕ} (hp : p.Prime) :
    (p - 1) * (multiplicity p n !).get (multiplicity.finite_nat_iff.mpr ⟨hp.ne_one, factorial_pos n⟩) =
      n - (p.digits n).sum :=
  Nat.Prime.sub_one_mul_multiplicity_factorial hp

/-! ## Why Kummer's Theorem Matters

1. **Computational**: Efficiently compute the exact power of p dividing C(n,k) without
   computing the binomial coefficient itself (which can be astronomically large).

2. **Structural**: Reveals deep connections between combinatorics and number systems.

3. **Applications**:
   - Pascal's triangle mod p (Sierpiński triangle for p = 2)
   - Divisibility properties of Catalan numbers
   - Study of binomial coefficient sequences

4. **Generalizations**: Leads to theorems about multinomial coefficients and
   q-binomial coefficients. -/

#check kummer
#check kummer'
#check prime_dvd_choose_prime_pow

end KummerTheorem
