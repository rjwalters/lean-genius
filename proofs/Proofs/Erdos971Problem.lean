/-
Erdős Problem #971: Distribution of Least Primes in Arithmetic Progressions

Let p(a,d) denote the least prime congruent to a (mod d). Does there exist a
constant c > 0 such that, for all sufficiently large d,

  p(a,d) > (1+c)φ(d)log d

holds for ≫ φ(d) many values of a?

**Status**: OPEN - The general question remains unresolved.

**Partial Results** (Erdős 1949):
- The statement holds for an infinite sequence of d values
- For any ε > 0, the opposite bound p(a,d) < ε φ(d)log d holds for many a

Reference: https://erdosproblems.com/971
-/

import Mathlib

namespace Erdos971

open Filter Finset Real Nat

/-!
## Definitions

We define the least prime in an arithmetic progression, which is the central
object of study in this problem.
-/

/--
`leastCongruentPrime a d` is the least prime number p such that p ≡ a (mod d).

By Dirichlet's theorem on primes in arithmetic progressions, this is well-defined
whenever gcd(a,d) = 1: there are infinitely many primes in such progressions.
-/
noncomputable def leastCongruentPrime (a d : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}

/-!
## The Main Question (Open)

The central question asks whether there exists a constant c > 0 such that
for all sufficiently large d, the least prime p(a,d) exceeds (1+c)φ(d)log d
for a positive proportion of reduced residue classes a.

This is related to understanding the distribution of primes in arithmetic
progressions beyond what is guaranteed by Linnik's theorem.
-/

/--
The main open question: Does there exist c > 0 and C > 0 such that for all
sufficiently large d, at least C·φ(d) reduced residue classes a have their
least prime p(a,d) exceeding (1+c)φ(d)log d?

This remains open as stated for ALL large d.
-/
def mainQuestion : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ d in atTop,
    C * (d.totient : ℝ) ≤
      #{a ∈ Finset.range d | a.Coprime d ∧
        (leastCongruentPrime a d : ℝ) > (1 + c) * d.totient * Real.log d}

/-!
## Partial Results (Erdős 1949)

Erdős proved two significant partial results in his 1949 paper
"On some applications of Brun's method":

1. The main statement holds for an infinite sequence of d values
2. For any ε > 0, most residue classes have SMALL least primes

These results use sieve methods (Brun's sieve) and are beyond Mathlib's
current formalization.
-/

/--
Erdős's first partial result: The statement in `mainQuestion` holds for
infinitely many values of d (though not necessarily all large d).

This is proved using Brun's sieve methods applied to carefully chosen
moduli d with special multiplicative structure.

Reference: Erdős, P., "On some applications of Brun's method",
Acta Univ. Szeged. Sect. Sci. Math. (1949), 57-63.
-/
axiom erdos_infinite_sequence :
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
    {d : ℕ | C * (d.totient : ℝ) ≤
      #{a ∈ Finset.range d | a.Coprime d ∧
        (leastCongruentPrime a d : ℝ) > (1 + c) * d.totient * Real.log d}}.Infinite

/--
Erdős's second partial result: For any ε > 0, a positive proportion of
reduced residue classes have SMALL least primes (less than ε·φ(d)·log d).

This is a complementary result showing that while some classes have large
least primes, many others have small ones.

Reference: Erdős, P., "On some applications of Brun's method",
Acta Univ. Szeged. Sect. Sci. Math. (1949), 57-63.
-/
axiom erdos_many_small :
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ d in atTop,
    C * (d.totient : ℝ) ≤
      #{a ∈ Finset.range d | a.Coprime d ∧
        (leastCongruentPrime a d : ℝ) < ε * d.totient * Real.log d}

/-!
## Context and Significance

This problem relates to several important themes in analytic number theory:

1. **Linnik's Theorem**: The least prime in an arithmetic progression a (mod d)
   satisfies p(a,d) ≤ c·d^L for some constant L (Linnik's constant). Current
   best bounds give L ≤ 5.

2. **Dirichlet's Theorem**: Guarantees infinitely many primes in each
   progression with gcd(a,d) = 1, but says nothing about how small the
   least one is.

3. **Average Behavior**: On average over a, one expects p(a,d) ≈ φ(d)·log d
   by the prime number theorem for arithmetic progressions.

This problem asks whether the extreme deviations from average (specifically,
having least primes larger than (1+c)·average) occur systematically for
many residue classes simultaneously.
-/

/-!
## Computational Example

For small moduli, we can explicitly compute the least primes. For d = 10,
the reduced residue classes are {1, 3, 7, 9} and we have:
- p(1, 10) = 11 (least prime ≡ 1 mod 10)
- p(3, 10) = 3 (least prime ≡ 3 mod 10)
- p(7, 10) = 7 (least prime ≡ 7 mod 10)
- p(9, 10) = 19 (least prime ≡ 9 mod 10)
-/

/-- 3 is prime and congruent to 3 mod 10. -/
theorem example_p_3_10 : Nat.Prime 3 ∧ 3 ≡ 3 [MOD 10] := by
  constructor
  · decide
  · native_decide

/-- 11 is prime and congruent to 1 mod 10. -/
theorem example_p_1_10 : Nat.Prime 11 ∧ 11 ≡ 1 [MOD 10] := by
  constructor
  · decide
  · native_decide

end Erdos971
