/-!
# Erdős Problem #122: Distribution of n + f(n) in Short Intervals

**Source:** [erdosproblems.com/122](https://erdosproblems.com/122)
**Status:** OPEN (Erdős–Pomerance–Sárközy)

## Statement

For which number-theoretic functions f is it true that, for any F(n)
with f(n)/F(n) → 0 for almost all n, there are infinitely many x
such that #{n : n + f(n) ∈ (x, x + F(x))} / F(x) → ∞?

## Background

Erdős, Pomerance, and Sárközy [ErPoSa97] proved this holds for
f = d (divisor function) and f = ω (number of distinct prime divisors).
Erdős conjectured it fails for f = φ (Euler's totient) and f = σ
(sum of divisors).

## Approach

We formalize the key predicate: a function f has the "short interval
concentration property" if the counting function grows faster than
F(x) for infinitely many x, whenever f(n)/F(n) → 0 a.e.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter

namespace Erdos122

/-! ## Part I: Number-Theoretic Functions -/

/--
The divisor function d(n): number of positive divisors of n.
-/
def divisorCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0) |>.card

/--
The number of distinct prime divisors ω(n).
-/
def distinctPrimeCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ n % p = 0) |>.card

/--
Euler's totient function φ(n): count of k ≤ n with gcd(k, n) = 1.
-/
def eulerTotient (n : ℕ) : ℕ :=
  (Finset.range n).filter (fun k => Nat.Coprime (k + 1) n) |>.card

/--
Sum of divisors σ(n): sum of all positive divisors of n.
-/
def sumOfDivisors (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0)).sum id

/-! ## Part II: Counting in Intervals -/

/--
Count of n with n + f(n) in the interval (x, x + F(x)].
-/
def countInInterval (f : ℕ → ℕ) (F : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + F x + 1)).filter
    (fun n => n + f n > x ∧ n + f n ≤ x + F x) |>.card

/--
The growth condition: f(n)/F(n) → 0 for almost all n.
Formalized as: for all ε > 0, the set of n with f(n) ≥ ε · F(n)
has natural density 0.
-/
def GrowthDominates (f : ℕ → ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ ε : ℚ, ε > 0 →
    ∀ δ : ℚ, δ > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        ((Finset.range N).filter (fun n => (f n : ℚ) ≥ ε * F n)).card < δ * N

/-! ## Part III: The Short Interval Concentration Property -/

/--
**Short interval concentration property (SICP):**
A function f has SICP if for every F with f(n)/F(n) → 0 a.e.,
there are infinitely many x with #{n : n + f(n) ∈ (x, x+F(x))} / F(x) → ∞.

Formally: for every F dominating f and every C > 0, there are
infinitely many x with countInInterval f F x > C · F(x).
-/
def HasSICP (f : ℕ → ℕ) : Prop :=
  ∀ F : ℕ → ℕ, (∀ n, F n ≥ 1) →
    GrowthDominates f F →
    ∀ C : ℕ, C ≥ 1 →
      ∀ x₀ : ℕ, ∃ x : ℕ, x ≥ x₀ ∧
        countInInterval f F x > C * F x

/-! ## Part IV: Known Results -/

/--
**Erdős–Pomerance–Sárközy Theorem [ErPoSa97]:**
The divisor function d has SICP.
-/
axiom divisor_count_has_SICP : HasSICP divisorCount

/--
**Erdős–Pomerance–Sárközy Theorem (variant):**
The distinct prime count function ω has SICP.
-/
axiom prime_count_has_SICP : HasSICP distinctPrimeCount

/-! ## Part V: Conjectured Failures -/

/--
**Erdős's conjecture: φ fails SICP.**
Euler's totient function does NOT have the short interval
concentration property.
-/
def ErdosConjecture122_phi : Prop :=
  ¬HasSICP eulerTotient

/--
**Erdős's conjecture: σ fails SICP.**
The sum of divisors function does NOT have the short interval
concentration property.
-/
def ErdosConjecture122_sigma : Prop :=
  ¬HasSICP sumOfDivisors

/--
**Combined Erdős Problem #122:**
Characterize which number-theoretic functions have SICP.
The divisor function and distinct prime count do; Euler's totient
and sum of divisors conjecturally do not.
-/
def ErdosProblem122 : Prop :=
  HasSICP divisorCount ∧
  HasSICP distinctPrimeCount ∧
  ¬HasSICP eulerTotient ∧
  ¬HasSICP sumOfDivisors

/-! ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #122 asks which number-theoretic functions have the
short interval concentration property. The divisor function and ω
are known to have it; φ and σ are conjectured not to. The general
characterization remains open.
-/
theorem erdos_122_known_results :
    HasSICP divisorCount ∧ HasSICP distinctPrimeCount :=
  ⟨divisor_count_has_SICP, prime_count_has_SICP⟩

end Erdos122
