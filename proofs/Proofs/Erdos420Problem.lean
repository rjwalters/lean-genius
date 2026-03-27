/-
Erdős Problem #420: Divisor Function Ratios for Factorials

Source: https://erdosproblems.com/420
Status: PARTIALLY SOLVED (Erdős-Graham-Ivić-Pomerance 1996)

Statement:
If τ(n) counts the number of divisors of n, define
  F(f,n) = τ((n + ⌊f(n)⌋)!) / τ(n!)

Questions:
1. Is lim_{n→∞} F((log n)^C, n) = ∞ for large C?
2. Is F(log n, n) everywhere dense in (1, ∞)?
3. More generally, if f(n) ≤ log n is monotonic with f(n) → ∞, is F(f,n) everywhere dense?

Known Results:
- lim F(n^{1/2}, n) = ∞ (easy, can improve to n^{1/2-c})
- liminf F(c log n, n) = 1 for any c > 0 (EGIP96)
- lim F(n^{4/9}, n) = ∞ (EGIP96)
- If f(n) = o((log n)^2), then F(f,n) ~ 1 for almost all n (EGIP96)

Connections to Prime Gaps:
- Bounded prime gaps ⟹ limsup F(g(n), n) = ∞ for any g(n) → ∞
- Cramér's conjecture ⟹ lim F(g(n)(log n)^2, n) = ∞ for any g(n) → ∞

References:
- [EGIP96] Erdős, Graham, Ivić, Pomerance: "On the number of divisors of n!" (1996)
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Set.Basic

open Nat BigOperators Finset Real

namespace Erdos420

/-
## Part I: The Divisor Function

τ(n) = number of positive divisors of n.
-/

/--
**Divisor Counting Function** τ(n):
The number of positive divisors of n.
Uses Mathlib's Nat.divisors.
-/
def tau (n : ℕ) : ℕ := n.divisors.card

/--
τ(1) = 1 (only divisor is 1 itself).
-/
theorem tau_one : tau 1 = 1 := by
  simp [tau, Nat.divisors_one]

/--
τ(p) = 2 for prime p (divisors are 1 and p).
-/
theorem tau_prime (p : ℕ) (hp : p.Prime) : tau p = 2 := by
  simp [tau, Nat.divisors_prime hp]

/--
τ is multiplicative for coprime arguments.
-/

/-
## Part II: Divisor Function of Factorials

τ(n!) grows extremely fast. Understanding its behavior is key.
-/

/--
**Factorial Divisor Count:**
The number of divisors of n!.
-/
def tauFactorial (n : ℕ) : ℕ := tau n.factorial

/--
τ(n!) has a well-known asymptotic formula due to Ramanujan and others.
For large n:
  log τ(n!) ~ n · log 2 / log log n
-/

/-
## Part III: The F Function

F(f, n) = τ((n + ⌊f(n)⌋)!) / τ(n!)

This measures how much τ grows when we extend from n! to (n+k)!.
-/

/--
**The F function:**
Ratio of divisor counts for extended factorials.
-/
noncomputable def F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (tauFactorial (n + ⌊f n⌋.toNat) : ℝ) / (tauFactorial n : ℝ)

/--
F(f, n) ≥ 1 always, since (n + k)! is divisible by n!.
-/

/-
## Part IV: Easy Result - F(√n, n) → ∞
-/

/--
**Easy Result:**
lim_{n→∞} F(√n, n) = ∞

When f(n) = √n, the ratio τ((n + √n)!) / τ(n!) grows without bound.

Erdős and Graham note this is "easy to show" and the exponent 1/2
can be improved to 1/2 - c for some small c > 0.
-/
axiom sqrt_gives_infinity :
    ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → F (fun n => Real.sqrt n) n > M

/--
**Improvement:**
The exponent can be reduced below 1/2.
-/

/-
## Part V: EGIP96 Results

Key results from Erdős-Graham-Ivić-Pomerance (1996).
-/

/--
**EGIP96 Theorem 1:**
liminf_{n→∞} F(c log n, n) = 1 for any c > 0.

This means the ratio can get arbitrarily close to 1 along
subsequences, even when f(n) = c log n.
-/

/--
**EGIP96 Theorem 2:**
lim_{n→∞} F(n^{4/9}, n) = ∞

The exponent 4/9 can be improved slightly.
-/
axiom four_ninths_gives_infinity :
    ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → F (fun n => (n : ℝ)^(4/9)) n > M

/--
**EGIP96 Theorem 3:**
If f(n) = o((log n)²), then F(f, n) ~ 1 for almost all n.

"Almost all" means the exceptional set has density 0.
-/

/-
## Part VI: Connection to Prime Gaps
-/

/--
**Bounded Prime Gaps Implication:**
The existence of infinitely many bounded prime gaps implies
limsup_{n→∞} F(g(n), n) = ∞ for any g(n) → ∞.

This follows from: if p, p+k are both prime with k bounded,
then τ((p+k-1)!) / τ(p!) captures a prime gap effect.
-/
axiom bounded_gaps_implies_limsup_infinity :
    (∃ k : ℕ, ∃ᶠ p in Filter.atTop, p.Prime ∧ (p + k).Prime) →
      ∀ g : ℕ → ℝ, (∀ M, ∃ N, ∀ n ≥ N, g n > M) →
        ∀ M : ℝ, ∃ᶠ n in Filter.atTop, F g n > M

/--
**Zhang's Theorem (2013):**
There exist infinitely many pairs of primes differing by at most 70 million.
This was later improved to 246 (Polymath project).
-/
axiom zhang_bounded_gaps : ∃ k : ℕ, k ≤ 70000000 ∧
    ∃ᶠ p in Filter.atTop, p.Prime ∧ (p + k).Prime

/--
**Corollary:**
Zhang's theorem implies limsup F(g(n), n) = ∞ for any g(n) → ∞.
-/
theorem bounded_gaps_consequence :
    ∀ g : ℕ → ℝ, (∀ M, ∃ N, ∀ n ≥ N, g n > M) →
      ∀ M : ℝ, ∃ᶠ n in Filter.atTop, F g n > M := by
  intro g hg M
  apply bounded_gaps_implies_limsup_infinity
  · obtain ⟨k, _, hk⟩ := zhang_bounded_gaps
    exact ⟨k, hk⟩
  · exact hg

/--
**Cramér's Conjecture Implication:**
If Cramér's conjecture holds (prime gaps are O((log p)²)),
then lim F(g(n) · (log n)², n) = ∞ for any g(n) → ∞.
-/

/-
## Part VII: Open Questions
-/

/--
**Open Questions:**
1. Is lim_{n→∞} F((log n)^C, n) = ∞ for large C? (Unknown for specific C values)
2. Is F(log n, n) everywhere dense in (1, ∞)? (liminf = 1 but density unknown)
3. For monotonic f ≤ log n with f → ∞, is F(f, n) everywhere dense in (1, ∞)?
-/

/-
## Part VIII: Main Result
-/

/--
**Erdős Problem #420: PARTIALLY SOLVED**

Key established results:
1. liminf F(c log n, n) = 1 for any c > 0
2. lim F(n^{4/9}, n) = ∞
3. F(f, n) ~ 1 for almost all n when f = o((log n)²)

Open: Behavior for f between log n and n^{4/9}.
-/
theorem erdos_420 :
    -- lim F(√n, n) = ∞
    (∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → F (fun n => Real.sqrt n) n > M) ∧
    -- lim F(n^{4/9}, n) = ∞
    (∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → F (fun n => (n : ℝ)^(4/9)) n > M) :=
  ⟨sqrt_gives_infinity, four_ninths_gives_infinity⟩

/-
## Part IX: Legendre's Formula and τ(n!)
-/

/--
**Connection to τ(n!) Formula:**
By Legendre's formula, n! = ∏_p p^{⌊n/p⌋ + ⌊n/p²⌋ + ...}
So τ(n!) = ∏_p (1 + ⌊n/p⌋ + ⌊n/p²⌋ + ...)
This product over primes ≤ n grows extremely fast.
-/

/--
**Legendre's Formula:**
The exponent of prime p in n! is ∑_{i≥1} ⌊n/p^i⌋.
-/

/-
## Part X: Summary and Historical Notes
-/

/--
**Erdős Problem #420: Summary**

**KNOWN (EGIP96):**
- liminf F(c log n, n) = 1 for any c > 0
- lim F(n^{4/9}, n) = ∞
- F(f, n) ~ 1 a.e. for f = o((log n)²)

**OPEN:**
- Behavior for f between (log n)^C and n^{4/9}
- Density of F(log n, n) in (1, ∞)

**KEY INSIGHT:**
Zhang's bounded gaps theorem implies limsup F(g(n), n) = ∞
for any g(n) → ∞.
-/
theorem erdos_420_summary :
    -- F(√n, n) → ∞ and F(n^{4/9}, n) → ∞
    (∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → F (fun n => Real.sqrt n) n > M) ∧
    (∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → F (fun n => (n : ℝ)^(4/9)) n > M) ∧
    -- Bounded gaps consequence
    (∀ g : ℕ → ℝ, (∀ M, ∃ N, ∀ n ≥ N, g n > M) →
      ∀ M : ℝ, ∃ᶠ n in Filter.atTop, F g n > M) :=
  ⟨sqrt_gives_infinity, four_ninths_gives_infinity, bounded_gaps_consequence⟩

end Erdos420
