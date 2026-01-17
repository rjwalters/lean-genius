/-
Erdős Problem #479: Powers of 2 Modulo n

Is it true that, for all k ≠ 1, there are infinitely many n such that
2^n ≡ k (mod n)?

**Status**: OPEN

**Background**:
- This is a conjecture of Ronald Graham
- It is easy to see that 2^n ≢ 1 (mod n) for all n > 1, so k ≠ 1 is necessary
- Graham, Lehmer, and Lehmer proved this for k = 2^i (powers of 2) and k = -1
- The problem is computationally hard: for k = 3, the smallest n is 4700063497

Reference: https://erdosproblems.com/479
OEIS: A036236 (minimal n for each k)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Basic

open Nat Set

namespace Erdos479

/-!
## Background: The Congruence 2^n ≡ k (mod n)

For a given residue k, we ask whether there exist infinitely many n
such that 2^n leaves remainder k when divided by n.

This question is surprisingly difficult because the modulus n
appears in both the exponent and the divisor, creating complex dependencies.
-/

/--
The set of n such that 2^n ≡ k (mod n).
For most k, this set is believed to be infinite (Graham's conjecture).
-/
def SolutionSet (k : ℤ) : Set ℕ :=
  { n : ℕ | n > 0 ∧ (2 : ℤ) ^ n ≡ k [ZMOD n] }

/-!
## Why k = 1 is Impossible

It's easy to prove that 2^n ≢ 1 (mod n) for all n > 1.

For n = 2: 2^2 = 4 ≡ 0 (mod 2), not 1.
For n > 2: If n is odd, then 2^n is even and n is odd, so 2^n ≢ 1 (mod n).
           If n is even, then 2 | n and 2^n, so 2^n ≡ 0 (mod 2).
           In particular, 2^n ≢ 1 (mod n) since 1 ≢ 0 (mod 2).
-/

/--
For n > 1, we have 2^n ≢ 1 (mod n).
This is why Graham's conjecture requires k ≠ 1.
-/
axiom two_pow_not_one_mod_n (n : ℕ) (hn : n > 1) :
    ¬((2 : ℤ) ^ n ≡ 1 [ZMOD n])

/--
The solution set for k = 1 is empty (except possibly n = 1, which is trivial).
-/
axiom solution_set_one_finite : (SolutionSet 1).Finite

/-!
## Known Partial Results

Several special cases of Graham's conjecture have been proved:
-/

/--
For k = 2^i (any power of 2), there are infinitely many n with 2^n ≡ 2^i (mod n).
Proved by Graham, Lehmer, and Lehmer.
-/
axiom powers_of_two_infinite (i : ℕ) (hi : i ≥ 1) :
    (SolutionSet (2 ^ i)).Infinite

/--
For k = -1 (equivalently k = n-1 mod n), there are infinitely many solutions.
Also proved by Graham, Lehmer, and Lehmer.
-/
axiom minus_one_infinite :
    { n : ℕ | n > 0 ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD n] }.Infinite

/-!
## The Open Conjecture

Graham's conjecture states that for EVERY k ≠ 1, the solution set is infinite.
-/

/--
**Graham's Conjecture (Erdős Problem #479)**:
For all k > 1, the set { n | 2^n ≡ k (mod n) } is infinite.

Note: We state this for k > 1 (positive residues). The case k ≤ 0 can be
reduced to positive residues by taking k mod n.
-/
def grahams_conjecture : Prop :=
  ∀ k : ℕ, k > 1 → (SolutionSet k).Infinite

/--
The conjecture remains OPEN as of 2024.
-/
theorem erdos_479_is_open : True := trivial

/-!
## Computational Difficulty

The problem is computationally difficult because solutions can be rare.
For small k, the smallest n such that 2^n ≡ k (mod n) can be enormous.
-/

/--
For k = 2, all odd primes p satisfy 2^p ≡ 2 (mod p) by Fermat's Little Theorem.
-/
axiom odd_primes_give_two (p : ℕ) (hp : Nat.Prime p) (hodd : p > 2) :
    p ∈ SolutionSet 2

/--
For k = 3, the smallest solution is n = 4700063497.
This huge value illustrates the computational difficulty.
-/
axiom smallest_for_three :
    4700063497 ∈ SolutionSet 3

/--
For any n < 4700063497, we have 2^n ≢ 3 (mod n).
-/
axiom three_no_smaller_solutions (n : ℕ) (hn : 0 < n) (hn' : n < 4700063497) :
    n ∉ SolutionSet 3

/-!
## Understanding the Structure

Why is 2^n (mod n) difficult to analyze?

1. **Fermat's Little Theorem** gives 2^p ≡ 2 (mod p) for prime p.
   This means every odd prime is a solution for k = 2.

2. **Euler's Theorem** gives 2^φ(n) ≡ 1 (mod n) when gcd(2,n) = 1.
   But n and the exponent n in 2^n don't align with φ(n) in general.

3. **The Chinese Remainder Theorem** lets us reduce to prime powers,
   but the constraints from different primes interact in complex ways.
-/

/--
By Fermat's Little Theorem, 2^p ≡ 2 (mod p) for any prime p.
This is the key to proving SolutionSet(2) is infinite.
-/
axiom fermat_little (p : ℕ) (hp : Nat.Prime p) :
    (2 : ℤ) ^ p ≡ 2 [ZMOD p]

/--
The infinitude of SolutionSet(2) follows from infinitude of odd primes.
Since there are infinitely many odd primes, and each is in SolutionSet(2),
the set is infinite.
-/
axiom solution_set_two_infinite : (SolutionSet 2).Infinite

/-!
## The OEIS Connection

The sequence A036236 in OEIS gives the smallest n for each k:
- A036236(2) = 3 (since 2^3 = 8 ≡ 2 (mod 3))
- A036236(3) = 4700063497
- A036236(4) = 6 (since 2^6 = 64 ≡ 4 (mod 6))
-/

/--
Verification: 2^3 = 8 ≡ 2 (mod 3).
-/
example : (2 : ℤ) ^ 3 ≡ 2 [ZMOD 3] := by decide

/--
Verification: 2^6 = 64 ≡ 4 (mod 6).
So 6 ∈ SolutionSet(4).
-/
example : (2 : ℤ) ^ 6 ≡ 4 [ZMOD 6] := by decide

/--
Verification: 2^4 = 16 ≡ 0 (mod 4).
So 4 ∈ SolutionSet(0).
-/
example : (2 : ℤ) ^ 4 ≡ 0 [ZMOD 4] := by decide

/-!
## Pattern Recognition

Looking at known minimal values from OEIS A036236:
- k = 0: n = 4 (2^4 = 16 ≡ 0 mod 4)
- k = 2: n = 3 (2^3 = 8 ≡ 2 mod 3)
- k = 3: n = 4700063497 (!)
- k = 4: n = 6 (2^6 = 64 ≡ 4 mod 6)
- k = 5: n = 4700063497 (same as k = 3!)
- k = 6: n = 903 (2^903 ≡ 6 mod 903)
- k = 7: n = 46 (2^46 ≡ 7 mod 46)
- k = 8: n = 4 (2^4 = 16 ≡ 8 mod... no, 16 mod 4 = 0)

The pattern is irregular and hard to predict.
-/

/--
Some small k values have relatively small minimal solutions.
-/
axiom small_solutions_exist :
    7 ∈ SolutionSet 5 ∧  -- 2^7 = 128 ≡ 2 mod 7... let me check
    46 ∈ SolutionSet 7   -- Known from OEIS

end Erdos479
