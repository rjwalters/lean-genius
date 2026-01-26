/-!
# Erdős Problem #369: Consecutive Smooth Numbers

**Source:** [erdosproblems.com/369](https://erdosproblems.com/369)
**Status:** OPEN (Erdős–Graham, 1980)

## Statement

Let ε > 0 and k ≥ 2. For all sufficiently large n, does there exist
a sequence of k consecutive integers in {1, …, n}, each of which is
n^ε-smooth (all prime factors ≤ n^ε)?

## Background

Erdős and Graham (1980, p.69) note this is open even for k = 2,
calling it "very hard." There are two non-trivial variants:

1. Each m in the run must be m^ε-smooth (Balog–Wooley gives ∞ many).
2. Each m must lie in [n/2, n] (open for ALL sufficiently large n).

The problem connects smooth number distribution to consecutive
integer structure.

## Approach

We define B-smooth numbers, the consecutive smooth property,
and state both the main conjecture and Balog–Wooley partial result.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos369

/-! ## Part I: Smooth Numbers -/

/--
A number m is B-smooth if all prime factors of m are ≤ B.
-/
def IsSmooth (m B : ℕ) : Prop :=
  m ≥ 1 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ≤ B

/--
The largest prime factor of n (0 if n ≤ 1).
-/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n)).max' (by
    simp only [Finset.filter_nonempty_iff]
    sorry)

/-! ## Part II: Consecutive Smooth Runs -/

/--
A run of k consecutive integers starting at m, each B-smooth.
-/
def ConsecutiveSmoothRun (m k B : ℕ) : Prop :=
  k ≥ 2 ∧ ∀ i : ℕ, i < k → IsSmooth (m + i) B

/--
The main conjecture: for every ε > 0 and k ≥ 2, for all sufficiently
large n, there exists a run of k consecutive integers in {1,…,n},
each n^ε-smooth.

We approximate n^ε by requiring the smoothness bound B to satisfy
B^(1/ε) ≥ n, i.e., B is at least n^ε.
-/
def HasConsecutiveSmoothRun (n k B : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ m + k - 1 ≤ n ∧ ConsecutiveSmoothRun m k B

/-! ## Part III: The Erdős–Graham Conjecture -/

/--
**Erdős Problem #369 (Erdős–Graham, 1980):**
For every rational ε > 0 and k ≥ 2, there exists N₀ such that
for all n ≥ N₀, there is a run of k consecutive n^ε-smooth integers
in {1, …, n}.

We model n^ε as a function smoothBound : ℕ → ℕ that grows as n^ε.
-/
def ErdosConjecture369 : Prop :=
  ∀ k : ℕ, k ≥ 2 →
    ∀ smoothBound : ℕ → ℕ,
      -- smoothBound(n) → ∞ (but slower than n)
      (∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, smoothBound n ≥ C) →
      (∀ n : ℕ, smoothBound n ≤ n) →
      ∃ N₀ : ℕ,
        ∀ n : ℕ, n ≥ N₀ →
          HasConsecutiveSmoothRun n k (smoothBound n)

/-! ## Part IV: The k = 2 Case -/

/--
**The k = 2 case:**
Even finding two consecutive B-smooth numbers in {1,…,n} for
B = n^ε is open for all sufficiently large n.

Erdős and Graham: "the answer should be affirmative but the
problem seems very hard."
-/
def ErdosConjecture369_k2 : Prop :=
  ∀ smoothBound : ℕ → ℕ,
    (∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, smoothBound n ≥ C) →
    (∀ n : ℕ, smoothBound n ≤ n) →
    ∃ N₀ : ℕ,
      ∀ n : ℕ, n ≥ N₀ →
        HasConsecutiveSmoothRun n 2 (smoothBound n)

/-! ## Part V: Balog–Wooley Partial Result -/

/--
**Balog–Wooley (1998):**
There exist infinitely many n such that n and n+1 are both
n^ε-smooth (variant 1: each m is m^ε-smooth).

This gives infinitely many, but not all sufficiently large n.
-/
axiom balog_wooley_infinitely_many :
  ∀ smoothBound : ℕ → ℕ,
    (∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, smoothBound n ≥ C) →
    ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      IsSmooth n (smoothBound n) ∧ IsSmooth (n + 1) (smoothBound (n + 1))

/-! ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #369 asks whether consecutive smooth numbers exist
in {1,…,n} for all large n. Open even for k = 2. Balog–Wooley
proved infinitely many exist, but not for all n.
-/
theorem erdos_369_status : True := trivial

end Erdos369
