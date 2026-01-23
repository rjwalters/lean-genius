/-
Erdős Problem #389: Consecutive Products Divisibility

**Question**: For every n ≥ 1, is there a k such that
  n(n+1)⋯(n+k-1) | (n+k)(n+k+1)⋯(n+2k-1)?

In other words: does the product of k consecutive integers starting at n
divide the product of the next k consecutive integers?

**Status**: OPEN - The existence of such k for all n is unknown.

**Known Examples** (from OEIS A375071):
- n=1: k=1 (1 | 2)
- n=2: k=5 (2·3·4·5·6 | 7·8·9·10·11 = 55440, which is divisible by 720)
- n=3: k=4 (3·4·5·6 | 7·8·9·10)
- n=4: k=207 (!)
- n=5: k=206

**Pattern**: Consecutive odd-indexed terms often differ by 1.

**Context**: The minimal k values grow irregularly and can be very large.
This makes a general proof challenging.

References:
- https://erdosproblems.com/389
- OEIS A375071 (computed by Bhavik Mehta)
- Asked by Erdős and Straus (1980)
-/

import Mathlib

namespace Erdos389

open Nat BigOperators Finset

/-
## Products of Consecutive Integers

The product n(n+1)⋯(n+k-1).
-/

/--
Product of k consecutive integers starting at n.
P(n, k) = n(n+1)⋯(n+k-1)
-/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ range k, (n + i)

/--
The first block: n(n+1)⋯(n+k-1)
-/
def firstBlock (n k : ℕ) : ℕ := consecutiveProduct n k

/--
The second block: (n+k)(n+k+1)⋯(n+2k-1)
-/
def secondBlock (n k : ℕ) : ℕ := consecutiveProduct (n + k) k

/-
## The Divisibility Condition
-/

/--
The divisibility condition: first block divides second block.
-/
def divides_blocks (n k : ℕ) : Prop :=
  firstBlock n k ∣ secondBlock n k

/--
Alternative formulation: using binomial coefficients.
P(n, k) = (n+k-1)!/(n-1)! when n ≥ 1.
-/
theorem consecutiveProduct_eq_factorial (n k : ℕ) (hn : n ≥ 1) :
    consecutiveProduct n k = (n + k - 1)! / (n - 1)! := by
  sorry

/-
## The Main Question

Does such a k exist for every n?
-/

/--
For a given n, the set of k that satisfy the divisibility.
-/
def validK (n : ℕ) : Set ℕ :=
  {k : ℕ | k ≥ 1 ∧ divides_blocks n k}

/--
The minimal k satisfying the divisibility (if it exists).
This is OEIS sequence A375071.
-/
noncomputable def minimalK (n : ℕ) : ℕ :=
  sInf (validK n)

/--
**Erdős Problem #389 (OPEN)**: For every n ≥ 1, there exists k ≥ 1 such that
the first block of k consecutive integers starting at n divides
the second block of k consecutive integers.
-/
def erdos_389_conjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → (validK n).Nonempty

/-
## Verified Examples from OEIS A375071
-/

/-- For n = 1, k = 1 works: 1 | 2. -/
theorem divides_blocks_1_1 : divides_blocks 1 1 := by
  simp [divides_blocks, firstBlock, secondBlock, consecutiveProduct]

/-- minimalK 1 = 1 -/
axiom minimalK_1 : minimalK 1 = 1

/-- For n = 2, k = 5 works: 2·3·4·5·6 = 720, 7·8·9·10·11 = 55440, 55440/720 = 77. -/
theorem divides_blocks_2_5 : divides_blocks 2 5 := by
  native_decide

/-- minimalK 2 = 5 -/
axiom minimalK_2 : minimalK 2 = 5

/-- For n = 3, k = 4 works: 3·4·5·6 = 360, 7·8·9·10 = 5040, 5040/360 = 14. -/
theorem divides_blocks_3_4 : divides_blocks 3 4 := by
  native_decide

/-- minimalK 3 = 4 -/
axiom minimalK_3 : minimalK 3 = 4

/-- minimalK 4 = 207 (computational result) -/
axiom minimalK_4 : minimalK 4 = 207

/-- minimalK 5 = 206 (one less!) -/
axiom minimalK_5 : minimalK 5 = 206

/-
## Pattern Observations

From OEIS A375071:
1, 1, 5, 4, 207, 206, 2475, 984, 8171, 8170, ...

Notable pattern: a(2k) and a(2k+1) often differ by 1.
-/

/--
The "differ by 1" pattern for consecutive odd-indexed terms.
-/
def has_adjacent_pattern (n : ℕ) : Prop :=
  minimalK (2*n) = minimalK (2*n + 1) + 1 ∨
  minimalK (2*n) + 1 = minimalK (2*n + 1)

/--
Observed: minimalK(4) = minimalK(5) + 1 = 207 = 206 + 1.
-/
theorem pattern_4_5 : minimalK 4 = minimalK 5 + 1 := by
  rw [minimalK_4, minimalK_5]

/-
## Why This is Hard

The divisibility condition involves comparing prime factorizations:
- For each prime p, we need ν_p(secondBlock) ≥ ν_p(firstBlock)
- By Legendre's formula, ν_p(n!) = Σ_{i≥1} ⌊n/p^i⌋
- The condition becomes a complex inequality for all primes

The challenge: showing that for large enough k, all primes satisfy the inequality.
-/

/--
The p-adic valuation of a product of consecutive integers.
ν_p(P(n, k)) = ν_p((n+k-1)!) - ν_p((n-1)!)
-/
noncomputable def padicVal_consecutiveProduct (p n k : ℕ) [hp : Fact p.Prime] : ℕ :=
  padicValNat p (consecutiveProduct n k)

/--
The condition in terms of p-adic valuations:
∀ prime p, ν_p(secondBlock) ≥ ν_p(firstBlock)
-/
theorem divides_iff_padic (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    divides_blocks n k ↔
      ∀ p : ℕ, p.Prime →
        padicValNat p (secondBlock n k) ≥ padicValNat p (firstBlock n k) := by
  -- Follows from fundamental theorem of arithmetic
  sorry

/-
## Summary

Erdős Problem #389 (Erdős-Straus) asks whether for every n ≥ 1,
there exists k such that n(n+1)⋯(n+k-1) | (n+k)⋯(n+2k-1).

**Formalized**:
- `divides_blocks n k` - the divisibility condition
- `validK n` - the set of valid k values
- `minimalK n` - OEIS A375071
- `erdos_389_conjecture` - the main statement

**Status**: OPEN
- Verified computationally for n ≤ 18
- General proof unknown
- The minimal k can grow very large (k = 207 for n = 4)

**Key Insight**: The condition reduces to comparing p-adic valuations.
The difficulty is showing the balance tips favorably for some k.
-/

axiom erdos_389 : erdos_389_conjecture

theorem erdos_389_summary : True := trivial

end Erdos389
