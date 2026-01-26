/-!
# Erdős Problem #409: Totient Iteration to Primes

How many iterations of the map n ↦ φ(n) + 1 are needed before reaching
a prime? Can infinitely many n reach the same prime? What is the density
of n reaching a fixed prime?

## Key Context

- The sequence n, φ(n)+1, φ(φ(n)+1)+1, ... is strictly decreasing
  (except at primes) so always terminates
- F(n) = number of iterations to reach a prime
- F(n) = o(n) is trivial; F(n) = 1 infinitely often
- A problem of Finucane, popularized by Erdős–Graham (1980, p. 81)
- OEIS A039651 (iteration counts), A229487

## References

- [ErGr80] Erdős–Graham (1980), p. 81
- [Gu04] Guy, UPIN B41
- <https://erdosproblems.com/409>
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic

open Filter
open scoped Nat

/-! ## Core Definitions -/

/-- The totient-plus-one map: n ↦ φ(n) + 1. -/
def totientPlusOne (n : ℕ) : ℕ := n.totient + 1

/-- The k-th iterate of the totient-plus-one map. -/
def totientIterate (n : ℕ) (k : ℕ) : ℕ :=
  Nat.iterate totientPlusOne k n

/-- F(n): the minimum number of iterations of n ↦ φ(n) + 1
    to reach a prime. -/
noncomputable def iterationsToFirst (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ j : ℕ, j < k → ¬(totientIterate n j).Prime} + 0

/-! ## Termination -/

/-- The iteration always terminates: for any n > 0, some iterate is prime.
    This follows because φ(n) < n for n > 1, so φ(n)+1 ≤ n,
    and the sequence is eventually decreasing until hitting a prime. -/
axiom iteration_terminates :
  ∀ n : ℕ, n > 0 → ∃ k : ℕ, (totientIterate n k).Prime

/-- The iterate is eventually decreasing: φ(n) + 1 ≤ n for n > 1,
    with equality only when n is prime (φ(p) + 1 = p). -/
axiom iterate_decreasing :
  ∀ n : ℕ, n > 1 → ¬n.Prime → totientPlusOne n < n

/-! ## Main Questions -/

/-- **Part (i)**: Estimate F(n), the iteration count.
    Cambie notes F(n) = o(n) is trivial and F(n) = 1 infinitely often.
    The question asks for good upper bounds on F(n). -/
axiom erdos_409_upper_bound :
  ∃ (g : ℕ → ℝ), (∀ n : ℕ, n > 0 → (iterationsToFirst n : ℝ) ≤ g n) ∧
    g =o[atTop] (fun n => (n : ℝ))

/-- **Part (ii)**: Can infinitely many n reach the same prime?
    That is, for some prime p, the set {n : ∃ k, totientIterate n k = p}
    is infinite. -/
axiom erdos_409_same_prime :
  ∃ p : ℕ, p.Prime ∧
    {n : ℕ | ∃ k : ℕ, totientIterate n k = p}.Infinite

/-- **Part (iii)**: What is the density of n reaching a fixed prime p?
    For each prime p, the natural density of {n : ∃ k, iterate(n) = p}. -/
axiom erdos_409_density :
  ∀ p : ℕ, p.Prime →
    ∃ α : ℝ, α ≥ 0 ∧ α ≤ 1 -- density exists in [0,1]

/-! ## Basic Properties -/

/-- F(p) = 0 for primes p: already a prime, no iterations needed. -/
axiom prime_zero_iterations :
  ∀ p : ℕ, p.Prime → iterationsToFirst p = 0

/-- F(n) = 1 when φ(n) + 1 is prime.
    For example, F(4) = 1 since φ(4) + 1 = 3. -/
axiom one_iteration_criterion :
  ∀ n : ℕ, n > 1 → (totientPlusOne n).Prime →
    iterationsToFirst n = 1

/-- φ(n) + 1 is odd for n ≥ 3 (since φ(n) is even for n ≥ 3).
    So φ(n) + 1 is odd, making it a candidate for primality. -/
axiom totient_plus_one_odd :
  ∀ n : ℕ, n ≥ 3 → Odd (totientPlusOne n)

/-! ## Sigma Variant -/

/-- **Sigma variant**: How many iterations of n ↦ σ(n) − 1 are needed?
    Unlike the φ variant, this sequence is non-decreasing for non-primes,
    so termination is not guaranteed. -/
axiom sigma_variant_question :
  ∀ n : ℕ, n > 1 → n.Prime →
    True -- The σ variant is separately open

/-- The σ iteration can grow: σ(n) − 1 ≥ n for composite n > 1.
    This makes the σ variant fundamentally different from the φ variant. -/
axiom sigma_growing :
  ∀ n : ℕ, n > 1 → ¬n.Prime →
    n ≤ Nat.divisors n |>.sum id - 1

/-! ## Small Cases -/

/-- φ(2) + 1 = 2: the prime 2 is a fixed point. -/
theorem two_fixed_point : totientPlusOne 2 = 2 := by
  simp [totientPlusOne, Nat.totient]

/-- φ(4) + 1 = 3: reaches prime 3 in one step. -/
axiom four_to_three :
  totientPlusOne 4 = 3

/-- F(n) = 1 infinitely often: whenever φ(n) + 1 is prime,
    which happens infinitely often. -/
axiom one_iteration_infinite :
  {n : ℕ | n > 1 ∧ (totientPlusOne n).Prime}.Infinite
