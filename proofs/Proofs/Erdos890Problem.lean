/-!
# Erdős Problem #890: Sum of ω over Consecutive Integers

**Source:** [erdosproblems.com/890](https://erdosproblems.com/890)
**Status:** OPEN (Erdős–Selfridge [ErSe67])

## Statement

Two conjectures about S_k(n) = ∑_{0 ≤ i < k} ω(n + i):

1. For every k ≥ 1: lim inf_{n → ∞} S_k(n) ≤ k + π(k)?
2. lim sup_{n → ∞} S_k(n) · log log n / log n = 1?

## Background

Erdős and Selfridge proved the lower bound:
  lim inf S_k(n) ≥ k + π(k) − 1
using Pólya's theorem on gaps between k-smooth numbers.
The classical result gives lim sup ω(n) · log log n / log n = 1.

## Approach

We formalize ω(n) (distinct prime factor count), the cumulative
sum S_k(n), the prime counting function π, and both conjectures.
The Erdős–Selfridge lower bound is stated as an axiom.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter

namespace Erdos890

/-! ## Part I: Arithmetic Primitives -/

/--
Distinct prime factor count ω(n): number of distinct primes dividing n.
-/
def omega (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ n % p = 0) |>.card

/--
Prime counting function π(k): number of primes ≤ k.
-/
def primePi (k : ℕ) : ℕ :=
  (Finset.range (k + 1)).filter Nat.Prime |>.card

/--
Cumulative sum S_k(n) = ∑_{0 ≤ i < k} ω(n + i).
-/
def cumulativeOmega (k n : ℕ) : ℕ :=
  (Finset.range k).sum fun i => omega (n + i)

/-! ## Part II: Liminf and Limsup Notions -/

/--
Liminf of a sequence: the greatest lower bound of the eventual behavior.
We define it as a predicate: the liminf of f is at most L.
-/
def LiminfAtMost (f : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧ f n ≤ L

/--
Liminf of a sequence is at least L.
-/
def LiminfAtLeast (f : ℕ → ℕ) (L : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → f n ≥ L

/--
Limsup of a real-valued sequence equals a target.
Used for the ratio S_k(n) · log log n / log n → 1.
-/
def LimsupRatioIsOne (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℚ, ε > 0 →
    -- Eventually f(n) · log log n / log n ≤ 1 + ε
    (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (f n : ℚ) * Real.log (Real.log n) ≤ (1 + ε) * Real.log n) ∧
    -- Infinitely often f(n) · log log n / log n ≥ 1 − ε
    (∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      (f n : ℚ) * Real.log (Real.log n) ≥ (1 - ε) * Real.log n)

/-! ## Part III: Conjecture 1 (Liminf Bound) -/

/--
**Erdős–Selfridge Conjecture (Part 1):**
For every k ≥ 1, lim inf_{n → ∞} S_k(n) ≤ k + π(k).

That is, there are infinitely many n where the sum of ω across
k consecutive integers is at most k + π(k).
-/
def ErdosConjecture890_liminf : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    LiminfAtMost (cumulativeOmega k) (k + primePi k)

/-! ## Part IV: Conjecture 2 (Limsup Ratio) -/

/--
**Erdős–Selfridge Conjecture (Part 2):**
lim sup_{n → ∞} S_k(n) · log log n / log n = 1.

The maximum growth rate of S_k(n) matches that of ω(n) alone.
-/
def ErdosConjecture890_limsup (k : ℕ) : Prop :=
  LimsupRatioIsOne (cumulativeOmega k)

/-! ## Part V: Known Results -/

/--
**Erdős–Selfridge Lower Bound [ErSe67]:**
For every k ≥ 1, lim inf S_k(n) ≥ k + π(k) − 1.

This follows from Pólya's theorem on gaps between k-smooth numbers.
-/
axiom erdos_selfridge_lower_bound :
  ∀ k : ℕ, k ≥ 1 →
    LiminfAtLeast (cumulativeOmega k) (k + primePi k - 1)

/--
**Classical result:**
lim sup ω(n) · log log n / log n = 1.

The single-integer version is well known.
-/
axiom classical_omega_limsup : LimsupRatioIsOne omega

/-! ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #890 asks two questions about S_k(n) = ∑ ω(n+i):
(1) Is lim inf S_k(n) ≤ k + π(k)? (known: ≥ k + π(k) − 1)
(2) Is lim sup S_k(n) · log log n / log n = 1? (known for k = 1)
Both remain open for general k.
-/
theorem erdos_890_lower_bound :
    ∀ k : ℕ, k ≥ 1 →
      LiminfAtLeast (cumulativeOmega k) (k + primePi k - 1) :=
  erdos_selfridge_lower_bound

end Erdos890
