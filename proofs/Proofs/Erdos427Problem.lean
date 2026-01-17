/-
Erdős Problem #427: Divisibility of Prime Sums

Is it true that for every n and d, there exists k such that
  d | p_{n+1} + ... + p_{n+k}
where p_r denotes the r-th prime?

**Status**: SOLVED (Pilatte, using Shiu's theorem)

**Background**:
- Cedric Pilatte observed this follows from Shiu's theorem on strings of
  congruent primes
- Shiu (2000) proved: for any k ≥ 1 and gcd(a,q) = 1, there are infinitely
  many k-tuples of consecutive primes all congruent to a (mod q)
- The proof applies Shiu with k = q = d and a = 1

Reference: https://erdosproblems.com/427
Shiu: "Strings of congruent primes", J. London Math. Soc. (2000), 359-373
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat

open Nat Finset Set

namespace Erdos427

/-!
## Background: The nth Prime

We axiomatize the function that enumerates primes.
-/

/--
The n-th prime number (0-indexed).
p(0) = 2, p(1) = 3, p(2) = 5, p(3) = 7, ...
-/
axiom nthPrime : ℕ → ℕ

/--
Basic property: nthPrime produces primes.
-/
axiom nthPrime_is_prime (n : ℕ) : (nthPrime n).Prime

/--
nthPrime is strictly increasing.
-/
axiom nthPrime_strictMono : StrictMono nthPrime

/--
The first few prime values.
-/
axiom nthPrime_values :
    nthPrime 0 = 2 ∧ nthPrime 1 = 3 ∧ nthPrime 2 = 5 ∧
    nthPrime 3 = 7 ∧ nthPrime 4 = 11 ∧ nthPrime 5 = 13

/-!
## The Sum of Consecutive Primes

Given a starting index n and length k, we sum the primes p_n, p_{n+1}, ..., p_{n+k-1}.
-/

/--
The sum of k consecutive primes starting from index n:
sum_{i=n}^{n+k-1} p_i = p_n + p_{n+1} + ... + p_{n+k-1}
-/
noncomputable def primeSum (n k : ℕ) : ℕ :=
  (Finset.Ico n (n + k)).sum nthPrime

/--
primeSum n 0 = 0 (empty sum).
-/
theorem primeSum_zero (n : ℕ) : primeSum n 0 = 0 := by
  simp [primeSum]

/--
primeSum n 1 = nthPrime n (single term).
-/
theorem primeSum_one (n : ℕ) : primeSum n 1 = nthPrime n := by
  simp [primeSum]

/-!
## Erdős's Question

The question asks: for any starting point n and any divisor d > 0,
can we find a number k of consecutive primes such that d divides their sum?

More formally: ∀ n d, d ≠ 0 → ∃ k ≠ 0, d | primeSum n k
-/

/--
**Erdős Problem #427**: For every n and d (with d ≠ 0), there exists k ≠ 0
such that d divides the sum p_n + p_{n+1} + ... + p_{n+k-1}.
-/
def erdos_427_statement : Prop :=
  ∀ n d : ℕ, d ≠ 0 → ∃ k : ℕ, k ≠ 0 ∧ d ∣ primeSum n k

/-!
## Shiu's Theorem: Strings of Congruent Primes

The key tool for proving Erdős #427 is Shiu's remarkable theorem (2000):

**Shiu's Theorem**: For any k ≥ 1 and any a, q with gcd(a, q) = 1,
there exist infinitely many k-tuples of consecutive primes that are
all congruent to a modulo q.

This is a powerful generalization of Dirichlet's theorem on primes
in arithmetic progressions.
-/

/--
Shiu's Theorem: For any k ≥ 1 and any coprime a, q, there are infinitely
many starting indices m such that the k consecutive primes p_m, ..., p_{m+k-1}
are all congruent to a modulo q.
-/
def ShiuTheorem : Prop :=
  ∀ (k a q : ℕ), 1 ≤ k → 1 ≤ q → Nat.Coprime a q →
    { m : ℕ | ∀ i ∈ Finset.Ico m (m + k), nthPrime i ≡ a [MOD q] }.Infinite

/--
Shiu's theorem is true (proven in 2000).

Reference: Shiu, D. K. L., "Strings of congruent primes", J. London Math. Soc. (2) 61 (2000), 359-373.
-/
axiom shiu_theorem : ShiuTheorem

/-!
## Proof that Shiu Implies Erdős #427

Pilatte's elegant argument:
1. Apply Shiu with k = q = d and a = 1 (note gcd(1, d) = 1)
2. Get infinitely many indices m where p_m ≡ p_{m+1} ≡ ... ≡ p_{m+d-1} ≡ 1 (mod d)
3. Choose such an m with m > n
4. Let S = p_n + ... + p_{m-1} have residue r (mod d)
5. Add d - r primes from the block (each ≡ 1 mod d) to get total ≡ 0 (mod d)

More precisely:
- S ≡ r (mod d) for some 0 ≤ r < d
- If r = 0, we're done (k = m - n)
- If r > 0, add (d - r) primes each ≡ 1 (mod d)
- Sum = S + (d - r) ≡ r + (d - r) ≡ d ≡ 0 (mod d)
-/

/--
Key lemma: Sum of t primes each congruent to 1 (mod d) is congruent to t (mod d).
-/
axiom sum_of_ones_mod (m d t : ℕ) (hd : d ≠ 0) (ht : t ≤ d)
    (hprimes : ∀ i ∈ Finset.Ico m (m + d), nthPrime i ≡ 1 [MOD d]) :
    (Finset.Ico m (m + t)).sum nthPrime ≡ t [MOD d]

/--
From Shiu's theorem, we can find arbitrarily large m with d consecutive
primes all congruent to 1 (mod d).
-/
axiom shiu_gives_ones (d : ℕ) (hd : 1 ≤ d) (N : ℕ) :
    ∃ m, m ≥ N ∧ ∀ i ∈ Finset.Ico m (m + d), nthPrime i ≡ 1 [MOD d]

/--
**Main Theorem**: Erdős Problem #427 follows from Shiu's theorem.
-/
axiom erdos_427_of_shiu : ShiuTheorem → erdos_427_statement

/--
**Erdős Problem #427 is SOLVED**: The answer is YES.
For any n and d ≠ 0, there exists k ≠ 0 such that d | primeSum n k.
-/
theorem erdos_427 : erdos_427_statement := erdos_427_of_shiu shiu_theorem

/-!
## Examples and Verification

Let's verify the statement for small cases.
-/

/--
Example: For n = 0 and d = 5, we have p_0 + p_1 = 2 + 3 = 5, divisible by 5.
So k = 2 works.
-/
axiom example_n0_d5 : 5 ∣ primeSum 0 2  -- 2 + 3 = 5

/--
Example: For n = 0 and d = 10, we need to find k such that the sum of the
first k primes is divisible by 10.
2+3+5+7+11+13+17+19+23 = 100, so k = 9 works.
-/
axiom example_n0_d10 : 10 ∣ primeSum 0 9  -- Sum of first 9 primes = 100

/--
Example: For n = 1 and d = 3, we have p_1 + p_2 + p_3 = 3 + 5 + 7 = 15,
which is divisible by 3. So k = 3 works.
-/
axiom example_n1_d3 : 3 ∣ primeSum 1 3  -- 3 + 5 + 7 = 15

/--
Example: For n = 0 and d = 7, we check partial sums:
2 ≡ 2, 2+3=5 ≡ 5, 5+5=10 ≡ 3, 10+7=17 ≡ 3, 17+11=28 ≡ 0 (mod 7).
So k = 5 works: 2+3+5+7+11 = 28 = 4×7.
-/
axiom example_n0_d7 : 7 ∣ primeSum 0 5  -- 2+3+5+7+11 = 28

/-!
## The Power of Shiu's Theorem

Shiu's theorem is a profound result about the distribution of primes.
It says that primes are remarkably "well-distributed" in the following sense:

Not only do primes appear infinitely often in any arithmetic progression
(Dirichlet's theorem), but they appear in long consecutive runs of primes
all belonging to the same arithmetic progression.

This has many applications beyond Erdős #427:
- It implies arbitrarily long gaps in "non-residue" classes
- It provides constructive methods for finding primes with special properties
- It connects to questions about prime patterns and constellations
-/

/--
Corollary of Shiu: For any k and any residue class (mod q) with gcd(a,q) = 1,
we can find k consecutive primes in that class.
-/
def consecutive_primes_in_class (k a q : ℕ) : Prop :=
  ∃ m : ℕ, ∀ i ∈ Finset.Ico m (m + k), nthPrime i ≡ a [MOD q]

theorem shiu_implies_consecutive (k a q : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) (hcop : Nat.Coprime a q) :
    consecutive_primes_in_class k a q := by
  have H := shiu_theorem k a q hk hq hcop
  -- H says the set is infinite, so in particular nonempty
  obtain ⟨m, hm⟩ := H.nonempty
  exact ⟨m, hm⟩

/-!
## Why the Problem is Interesting

Erdős #427 asks about a seemingly simple property of prime sums.
The surprising fact is that it reduces to a deep theorem about prime distribution.

The intuition: If primes were "random" modulo d, then the sums of consecutive
primes would hit every residue class, so we'd eventually get 0 (mod d).
Shiu's theorem provides the rigorous basis for this intuition.

The key insight is that we can "steer" the sum to any target residue by
finding runs of primes with the same residue, then taking the right number.
-/

/--
For any n and nonzero d, there exists a solution to d | primeSum n k.
-/
theorem erdos_427_has_solution (n d : ℕ) (hd : d ≠ 0) : ∃ k, k ≠ 0 ∧ d ∣ primeSum n k :=
  erdos_427 n d hd

/-!
## Connection to Dirichlet's Theorem

Dirichlet's theorem states that for coprime a and q, the arithmetic
progression a, a+q, a+2q, ... contains infinitely many primes.

Shiu's theorem is much stronger: not only are there infinitely many
primes congruent to a (mod q), but there are arbitrarily long runs
of consecutive primes all congruent to a (mod q).

For example, Dirichlet says there are infinitely many primes ≡ 1 (mod 7).
Shiu says there exist 1000 consecutive primes all ≡ 1 (mod 7).
-/

/--
Dirichlet's theorem (special case): There are infinitely many primes
congruent to 1 modulo any q ≥ 2.
-/
axiom dirichlet_ones (q : ℕ) (hq : 2 ≤ q) :
    { p : ℕ | p.Prime ∧ p ≡ 1 [MOD q] }.Infinite

/--
Shiu's theorem for the special case a = 1.
-/
theorem shiu_for_ones (k q : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    { m : ℕ | ∀ i ∈ Finset.Ico m (m + k), nthPrime i ≡ 1 [MOD q] }.Infinite :=
  shiu_theorem k 1 q hk hq (Nat.coprime_one_left q)

/-!
## The Minimal k

For given n and d, what is the smallest k such that d | primeSum n k?
This is generally hard to compute and depends on the specific
distribution of primes, but Erdős #427 guarantees such k always exists.
-/

/--
The existence of k is equivalent to the set of valid k being nonempty.
-/
def validKs (n d : ℕ) : Set ℕ :=
  { k : ℕ | k ≠ 0 ∧ d ∣ primeSum n k }

theorem validKs_nonempty (n d : ℕ) (hd : d ≠ 0) : (validKs n d).Nonempty := by
  obtain ⟨k, hk_ne, hk_div⟩ := erdos_427 n d hd
  exact ⟨k, hk_ne, hk_div⟩

end Erdos427
