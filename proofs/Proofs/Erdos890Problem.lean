/-
Erdős Problem #890: Sum of ω over Consecutive Integers

Source: https://erdosproblems.com/890
Status: OPEN (Erdős–Selfridge, 1967)

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

Uses Mathlib's ArithmeticFunction.omega (ω) for the distinct prime factor count
and Nat.primeCounting for π. Computable verification provided for small cases.
The two open conjectures are stated as Prop definitions.
The Erdős–Selfridge lower bound is axiomatized as a known but deep result.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Nat Finset Filter

open scoped ArithmeticFunction.omega

namespace Erdos890

-- ## Part I: Core Definitions

/--
Cumulative sum S_k(n) = ∑_{0 ≤ i < k} ω(n + i).
Uses Mathlib's ω (ArithmeticFunction.omega) for the distinct prime factor count.
-/
noncomputable def cumulativeOmega (k n : ℕ) : ℕ :=
  (Finset.range k).sum fun i => ω (n + i)

/--
Prime counting function π via Mathlib's Nat.primeCounting.
Convenience alias for readability.
-/
noncomputable abbrev pi (k : ℕ) : ℕ := Nat.primeCounting k

-- ## Part II: Liminf and Limsup Notions

/--
Liminf predicate: the liminf of f is at most L.
Equivalently: f(n) ≤ L infinitely often.
-/
def LiminfAtMost (f : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧ f n ≤ L

/--
Liminf predicate: the liminf of f is at least L.
Equivalently: eventually f(n) ≥ L.
-/
def LiminfAtLeast (f : ℕ → ℕ) (L : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → f n ≥ L

/--
Limsup ratio predicate: lim sup f(n) · log log n / log n = 1.
Formalized as: for all ε > 0,
(a) eventually f(n) · log(log n) ≤ (1+ε) · log n, and
(b) infinitely often f(n) · log(log n) ≥ (1−ε) · log n.
-/
def LimsupRatioIsOne (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (f n : ℝ) * Real.log (Real.log n) ≤ (1 + ε) * Real.log n) ∧
    (∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      (f n : ℝ) * Real.log (Real.log n) ≥ (1 - ε) * Real.log n)

-- ## Part III: Conjecture 1 (Liminf Bound)

/--
**Erdős–Selfridge Conjecture (Part 1):**
For every k ≥ 1, lim inf_{n → ∞} S_k(n) ≤ k + π(k).

There are infinitely many n where the sum of ω across
k consecutive integers is at most k + π(k).
-/
def ErdosConjecture890_liminf : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    LiminfAtMost (cumulativeOmega k) (k + pi k)

-- ## Part IV: Conjecture 2 (Limsup Ratio)

/--
**Erdős–Selfridge Conjecture (Part 2):**
lim sup_{n → ∞} S_k(n) · log log n / log n = 1.

The maximum growth rate of S_k(n) matches that of ω(n) alone.
-/
def ErdosConjecture890_limsup (k : ℕ) : Prop :=
  LimsupRatioIsOne (cumulativeOmega k)

-- ## Part V: Known Results (Axioms)

/--
**Erdős–Selfridge Lower Bound (1967):**
For every k ≥ 1, lim inf S_k(n) ≥ k + π(k) − 1.

Proof sketch: n(n+1)···(n+k-1) is divisible by all primes ≤ k.
By Pólya's theorem (k-smooth numbers have unbounded gaps), for large n,
all but at most one of n, ..., n+k-1 has a prime factor > k.
Hence ∑ ω(n+i) ≥ k + (number of primes ≤ k) − 1 = k + π(k) − 1.
-/
axiom erdos_selfridge_lower_bound :
  ∀ k : ℕ, k ≥ 1 →
    LiminfAtLeast (cumulativeOmega k) (k + pi k - 1)

-- ## Part VI: Structural Theorems

/--
Monotonicity: S_{k+1}(n) ≥ S_k(n) for all n, since we sum one more term.
-/
theorem cumulativeOmega_mono (k n : ℕ) :
    cumulativeOmega k n ≤ cumulativeOmega (k + 1) n := by
  unfold cumulativeOmega
  apply Finset.sum_le_sum_of_subset
  intro i hi
  simp only [Finset.mem_range] at hi ⊢
  omega

/--
The Erdős–Selfridge lower bound applied at k = 1.
-/
theorem erdos_890_lower_bound_k1 :
    LiminfAtLeast (cumulativeOmega 1) (1 + pi 1 - 1) :=
  erdos_selfridge_lower_bound 1 (le_refl 1)

/--
If Conjecture 1 holds, the liminf is sandwiched:
k + π(k) − 1 ≤ lim inf S_k(n) ≤ k + π(k).
-/
theorem erdos_890_liminf_sandwich :
    ErdosConjecture890_liminf →
    ∀ k : ℕ, k ≥ 1 →
      LiminfAtLeast (cumulativeOmega k) (k + pi k - 1) ∧
      LiminfAtMost (cumulativeOmega k) (k + pi k) := by
  intro hconj k hk
  exact ⟨erdos_selfridge_lower_bound k hk, hconj k hk⟩

/--
The known lower bound restated as a top-level theorem.
-/
theorem erdos_890_known_lower_bound :
    ∀ k : ℕ, k ≥ 1 →
      LiminfAtLeast (cumulativeOmega k) (k + pi k - 1) :=
  erdos_selfridge_lower_bound

-- ## Part VII: Additional Structural Lemmas

/-- S_0(n) = 0: the empty sum. -/
theorem cumulativeOmega_zero (n : ℕ) : cumulativeOmega 0 n = 0 := by
  unfold cumulativeOmega; simp

/-- S_1(n) = ω(n): the single-term sum reduces to a single ω evaluation. -/
theorem cumulativeOmega_one (n : ℕ) : cumulativeOmega 1 n = ω n := by
  unfold cumulativeOmega; simp [Finset.sum_range_one]

/-- Sum splitting: S_{k+j}(n) = S_k(n) + S_j(n + k). -/
theorem cumulativeOmega_add (k j n : ℕ) :
    cumulativeOmega (k + j) n = cumulativeOmega k n + cumulativeOmega j (n + k) := by
  unfold cumulativeOmega; rw [Finset.sum_range_add]
  congr 1; apply Finset.sum_congr rfl; intro i _; congr 1; omega

-- ## Part VIII: Conjecture 1 Verified for k = 1

/-- ω(p) = 1 for any prime p: a prime has exactly one distinct prime factor. -/
theorem omega_prime {p : ℕ} (hp : Nat.Prime p) : ω p = 1 := by
  have h : p.primeFactors = {p} := by
    ext q; simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, hqp, -⟩
      exact (hp.eq_one_or_self_of_dvd q hqp).resolve_left hq.one_lt.ne'
    · rintro rfl; exact ⟨hp, dvd_refl p, hp.ne_zero⟩
  simp [ArithmeticFunction.omega, h]

/-- **Conjecture 1 verified for k = 1:**
    For k = 1, S₁(n) = ω(n). Every prime p has ω(p) = 1 ≤ 1 + π(1), and primes
    are unbounded (Euclid), so lim inf S₁(n) ≤ 1 + π(1). -/
theorem conjecture1_k1 : LiminfAtMost (cumulativeOmega 1) (1 + pi 1) := by
  intro N₀
  obtain ⟨p, hN, hp⟩ := Nat.exists_infinite_primes N₀
  exact ⟨p, hN, by rw [cumulativeOmega_one]
                     calc ω p = 1 := omega_prime hp
                       _ ≤ 1 + pi 1 := by omega⟩

end Erdos890
