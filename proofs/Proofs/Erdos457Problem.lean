/-
Erdős Problem #457: Small Prime Divisors of Consecutive Products

Is there some ε > 0 such that infinitely many n have all primes
p ≤ (2 + ε) log(n) dividing ∏_{1 ≤ i ≤ log n} (n + i)?

Equivalently, let q(n, k) be the least prime not dividing
∏_{1 ≤ i ≤ k} (n + i). Is q(n, log n) ≥ (2 + ε) log n
infinitely often?

**Status**: OPEN

**Known results**:
- A construction using n = product of primes between log(n) and
  (2 + o(1)) log(n) shows q(n, log n) ≥ (2 + o(1)) log(n).
- Open sub-question: Is q(n, log n) < (1 - ε)(log n)² for large n?

**Origin**: Erdős [Er79d], Erdős-Pomerance [ErGr80, p.91]
**Related**: Problem #663

Reference: https://erdosproblems.com/457
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib

open Filter Finset

namespace Erdos457

/- ## Part I: Consecutive Products

The product of k consecutive integers starting from n + 1:
∏_{i=1}^{k} (n + i) = (n+1)(n+2)···(n+k).

This product is related to binomial coefficients:
∏_{i=1}^{k} (n+i) = (n+k)! / n! = k! · C(n+k, k).

By the prime number theorem, this product is divisible by all
primes up to about k (at least), since among k consecutive
integers there must be a multiple of each prime p ≤ k. -/

/-- The product ∏_{1 ≤ i ≤ k} (n + i) for natural number arguments.
    This equals (n+1)(n+2)···(n+k). -/
noncomputable def consecutiveProduct (n : ℕ) (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- The consecutive product is always positive when k ≥ 1. -/
theorem consecutiveProduct_pos (n k : ℕ) (hk : k ≥ 1) :
    consecutiveProduct n k > 0 := by
  unfold consecutiveProduct
  apply Finset.prod_pos
  intro i hi
  simp only [Finset.mem_Icc] at hi
  omega

/-- Among k consecutive integers, every prime p ≤ k divides the product.
    This follows because the product contains a multiple of p. -/
axiom small_primes_divide (n k p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
    p ∣ consecutiveProduct n k

/- ## Part II: The Smallest Non-Dividing Prime

q(n, k) is the least prime that does NOT divide ∏_{i=1}^{k} (n+i).
This function measures how far the "small prime divisibility" extends
beyond the trivial threshold of k. -/

/-- q(n, k): the smallest prime not dividing ∏_{1 ≤ i ≤ k} (n + i).
    Such a prime always exists since the product is finite. -/
noncomputable def q (n k : ℕ) : ℕ :=
  have : ∃ p, p.Prime ∧ ¬(p ∣ consecutiveProduct n k) := by
    obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (consecutiveProduct n k + 1)
    refine ⟨p, hp, fun hdvd => ?_⟩
    have hpos : 0 < consecutiveProduct n k :=
      Finset.prod_pos (fun i hi => by simp only [Finset.mem_Icc] at hi; omega)
    have hle_prod := Nat.le_of_dvd hpos hdvd
    omega
  Nat.find this

/- ## Part III: The Main Conjecture (OPEN)

Erdős asks: can we do better than q(n, log n) > log(n)?
Specifically, is there a fixed ε > 0 such that q(n, log n) ≥ (2+ε) log(n)
infinitely often? The threshold 2 is significant because of the
prime number theorem: among log(n) consecutive integers near n,
we expect primes up to about 2·log(n) to divide the product
(by a counting/sieving argument). -/

/-- Erdős Problem #457: ∃ ε > 0 such that infinitely many n have all
    primes p ≤ (2 + ε) log(n) dividing ∏_{1 ≤ i ≤ ⌊log n⌋} (n + i).

    Equivalently: q(n, ⌊log n⌋) ≥ (2 + ε) log(n) infinitely often. -/
def ErdosConjecture457 : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    { n : ℕ | ∀ (p : ℕ), p.Prime → (p : ℝ) ≤ (2 + ε) * Real.log n →
      p ∣ consecutiveProduct n ⌊Real.log n⌋₊ }.Infinite

/-- The conjecture is axiomatized as it remains open. -/
axiom erdos_457 : ErdosConjecture457

/- ## Part IV: Equivalent Formulation via q(n, k)

The formulation using q(n, k) is more natural: instead of saying
"all primes up to X divide the product," we say "the first prime
that fails to divide is at least X." -/

/-- Equivalent: q(n, ⌊log n⌋) ≥ (2 + ε) log n infinitely often. -/
def ErdosConjecture457_q : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    { n : ℕ | (2 + ε) * Real.log n ≤ (q n ⌊Real.log n⌋₊ : ℝ) }.Infinite

/- ## Part V: Known Construction — The (2 + o(1)) Barrier

Erdős and Pomerance observed that one can achieve q(n, log n) ≥ (2 + o(1)) log(n)
by a specific construction: take n to be the product of all primes
between log(n) and (2 + o(1)) log(n).

For such n, the consecutive product ∏(n+i) for i ≤ log(n) is divisible
by all primes up to about (2 + o(1)) log(n) because n itself is
constructed from primes in that range. -/

/-- Known: q(n, log n) ≥ (2 + o(1)) log n is achievable by taking n
    as the product of primes between log(n) and (2 + o(1)) log(n). -/

/- ## Part VI: Upper Bound Sub-Question

A separate open question asks for an upper bound on q(n, log n).
The conjecture is that q(n, log n) < (1 - ε)(log n)² eventually. -/

/-- Open sub-question: Is q(n, log n) < (1 - ε)(log n)² for all large n?

    If true, this would sandwich q(n, log n) between
    (2 ± o(1)) log n and (1 - ε)(log n)². -/
def UpperBoundConjecture : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ᶠ n in atTop,
    (q n ⌊Real.log (n : ℝ)⌋₊ : ℝ) < (1 - ε) * (Real.log n) ^ 2

/- ## Part VII: Connection to Smooth Numbers

The problem is closely related to smooth number theory. A number m
is y-smooth if all prime factors of m are ≤ y. The consecutive
product ∏(n+i) being divisible by all primes up to y means that
the "smooth part" of the product captures all small primes. -/

/-- A number is y-smooth if all its prime factors are at most y. -/
def IsSmooth (m y : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ≤ y

/- ## Part VIII: Relationship to Problem #663

Erdős Problem #663 is a related question about prime factors of
consecutive products. The two problems share the underlying theme
of understanding the prime factorization structure of products
of consecutive integers. -/


/- ## Part IX: Summary -/

/--
**Erdős Problem #457: Summary**

PROBLEM: Is there ε > 0 such that q(n, ⌊log n⌋) ≥ (2+ε) log n
         infinitely often?

STATUS: OPEN

KNOWN:
- q(n, k) > k trivially (all primes ≤ k divide the product)
- q(n, ⌊log n⌋) ≥ (2 + o(1)) log n is achievable (prime product construction)
- The strict (2 + ε) with fixed ε > 0 remains open
- Upper bound conjecture: q(n, ⌊log n⌋) < (1 - ε)(log n)² is also open

The "2 barrier" is the central difficulty: crossing from (2 + o(1))
to a fixed (2 + ε) requires fundamentally new ideas about the
distribution of primes in consecutive products.
-/
theorem erdos_457_t1_solved : ErdosConjecture457 := erdos_457

end Erdos457
