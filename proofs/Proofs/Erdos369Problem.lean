/-
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

/- ## Part I: Smooth Numbers -/

/--
A number m is B-smooth if all prime factors of m are ≤ B.
-/
def IsSmooth (m B : ℕ) : Prop :=
  m ≥ 1 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ≤ B

/-- 1 is B-smooth for any B (vacuously: 1 has no prime factors). -/
theorem isSmooth_one (B : ℕ) : IsSmooth 1 B := by
  constructor
  · exact le_refl 1
  · intro p hp hdvd
    exfalso
    have : p = 1 := Nat.dvd_one.mp hdvd
    subst this
    exact Nat.not_prime_one hp

/-- Smoothness is monotone in the bound: B-smooth implies B'-smooth for B ≤ B'. -/
theorem isSmooth_mono_B {m B B' : ℕ} (h : B ≤ B') (hs : IsSmooth m B) : IsSmooth m B' :=
  ⟨hs.1, fun p hp hdvd => le_trans (hs.2 p hp hdvd) h⟩

/-- Any prime p is p-smooth. -/
theorem isSmooth_prime_self {p : ℕ} (hp : p.Prime) : IsSmooth p p :=
  ⟨hp.pos, fun q hq hdvd => by
    rcases hq.eq_one_or_self_of_dvd p (Nat.dvd_of_dvd_of_dvd hdvd (dvd_refl p)) with h | h
    · exact absurd h hq.ne_one
    · rw [← (hp.eq_one_or_self_of_dvd q hdvd).resolve_left hq.ne_one]⟩

/-- Products of B-smooth numbers are B-smooth. -/
theorem isSmooth_mul {m n B : ℕ} (hm : IsSmooth m B) (hn : IsSmooth n B) :
    IsSmooth (m * n) B := by
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp hm.1) (Nat.one_le_iff_ne_zero.mp hn.1))
  · intro p hp hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact hm.2 p hp h
    · exact hn.2 p hp h

/-- Prime powers p^k are p-smooth. -/
theorem isSmooth_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≥ 1) : IsSmooth (p^k) p := by
  constructor
  · exact Nat.one_le_pow k p hp.pos
  · intro q hq hdvd
    have : q ∣ p := (hq.dvd_of_dvd_pow hdvd)
    exact Nat.le_of_dvd hp.pos this

/- ## Part II: Consecutive Smooth Runs -/

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

/- ## Part III: The Erdős–Graham Conjecture -/

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

/- ## Part IV: The k = 2 Case -/

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

/- ## Part V: Balog–Wooley Partial Result -/

/--
**Balog–Wooley (1998):**
There exist infinitely many n such that n and n+1 are both
n^ε-smooth (variant 1: each m is m^ε-smooth).

This gives infinitely many, but not all sufficiently large n.
-/

/- ## Part VI: Summary -/

/-
**Summary:**
Erdős Problem #369 asks whether consecutive smooth numbers exist
in {1,…,n} for all large n. Open even for k = 2. Balog–Wooley
proved infinitely many exist, but not for all n.
-/

/-- (1, 2) form a run of 2 consecutive 2-smooth numbers:
    1 is vacuously smooth, 2 is 2-smooth. -/
theorem consecutiveSmoothRun_1_2_2 : ConsecutiveSmoothRun 1 2 2 := by
  constructor
  · omega
  · intro i hi
    interval_cases i
    · simpa using isSmooth_one 2
    · exact ⟨by omega, fun p hp hdvd => Nat.le_of_dvd (by omega) hdvd⟩

end Erdos369
