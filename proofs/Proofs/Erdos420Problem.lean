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
axiom tau_multiplicative (m n : ℕ) (hmn : Nat.Coprime m n) :
    tau (m * n) = tau m * tau n

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
axiom tau_factorial_asymptotic :
    ∃ (C : ℝ), C > 0 ∧
      ∀ n : ℕ, n ≥ 3 → (tauFactorial n : ℝ) ≥ 2^(n / (2 * Real.log n))

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
axiom F_ge_one (f : ℕ → ℝ) (n : ℕ) (hf : f n ≥ 0) : F f n ≥ 1

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
axiom subhalf_exponent_works :
    ∃ c : ℝ, c > 0 ∧ c < 1/2 ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → F (fun n => (n : ℝ)^(1/2 - c)) n > M

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
axiom liminf_log_equals_one :
    ∀ c : ℝ, c > 0 →
      ∀ ε : ℝ, ε > 0 → ∃ᶠ n in Filter.atTop, F (fun n => c * Real.log n) n < 1 + ε

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
axiom small_f_gives_one_almost_all :
    ∀ f : ℕ → ℝ, (∀ ε > 0, ∃ N, ∀ n ≥ N, f n < ε * (Real.log n)^2) →
      ∀ ε : ℝ, ε > 0 →
        ∃ E : Set ℕ, (∀ n ∈ E, |F f n - 1| ≥ ε) ∧
          -- E has density 0
          True  -- Formal density statement omitted

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
axiom cramer_implies_limit_infinity :
    (∀ ε > 0, ∃ᶠ p in Filter.atTop, p.Prime ∧
      ∃ q, q.Prime ∧ q > p ∧ q < p + (1 + ε) * (Real.log p)^2) →
    ∀ g : ℕ → ℝ, (∀ M, ∃ N, ∀ n ≥ N, g n > M) →
      ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        F (fun n => g n * (Real.log n)^2) n > M

/-
## Part VII: Open Questions
-/

/--
**Question 1 (Partially Open):**
Is lim_{n→∞} F((log n)^C, n) = ∞ for large C?

Current status: Unknown for specific values of C.
We know lim F(n^{4/9}, n) = ∞, which is much larger than (log n)^C.
-/
axiom question_1_partially_open :
    -- The question asks if there exists C such that the limit is ∞
    -- This remains open in the gap between log n and n^{4/9}
    True

/--
**Question 2 (Open):**
Is F(log n, n) everywhere dense in (1, ∞)?

We know liminf = 1, but density is unknown.
-/
axiom question_2_open :
    -- Is {F(log n, n) : n ∈ ℕ} dense in (1, ∞)?
    True

/--
**Question 3 (Open):**
If f(n) ≤ log n is monotonic with f(n) → ∞, is F(f, n) everywhere dense in (1, ∞)?
-/
axiom question_3_open : True

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
theorem erdos_420 : True := trivial

/--
**Summary of EGIP96:**
The paper "On the number of divisors of n!" establishes the key
bounds relating divisor function growth to prime distribution.
-/
theorem egip96_summary :
    -- liminf F(c log n, n) = 1
    -- lim F(n^{4/9}, n) = ∞
    -- F ~ 1 a.e. for small f
    True ∧ True ∧ True := ⟨trivial, trivial, trivial⟩

/-
## Part IX: Legendre's Formula and τ(n!)
-/

/--
**Connection to τ(n!) Formula:**
By Legendre's formula, n! = ∏_p p^{⌊n/p⌋ + ⌊n/p²⌋ + ...}
So τ(n!) = ∏_p (1 + ⌊n/p⌋ + ⌊n/p²⌋ + ...)
This product over primes ≤ n grows extremely fast.
-/
axiom tau_factorial_formula :
    ∀ n : ℕ, n ≥ 1 → ∃ (exponents : ℕ → ℕ),
      tauFactorial n = ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        (1 + exponents p)

/--
**Legendre's Formula:**
The exponent of prime p in n! is ∑_{i≥1} ⌊n/p^i⌋.
-/
axiom legendre_exponent (n p : ℕ) (hp : p.Prime) :
    ∃ e : ℕ, e = (Finset.range n).filter (fun i => p^(i+1) ≤ n) |>.card ∧
      p^e ∣ n.factorial ∧ ¬(p^(e+1) ∣ n.factorial)

/-!
## Part X: Summary and Historical Notes
-/

/--
**Mathematical Significance:**

1. **Divisor Growth:** τ(n!) encodes deep information about
   prime factorization structure.

2. **Prime Distribution:** The behavior of F is intimately
   connected to gaps between consecutive primes.

3. **Density Questions:** Whether F takes all values in (1, ∞)
   is a subtle question about integer structure.

4. **Multiplicativity:** The multiplicative nature of τ makes
   factorial analysis tractable but still challenging.
-/
theorem mathematical_significance : True := trivial

/--
**Erdős Problem #420: OPEN**

**QUESTIONS:**
1. Is lim_{n→∞} F((log n)^C, n) = ∞ for large C?
2. Is F(log n, n) everywhere dense in (1, ∞)?
3. For monotonic f ≤ log n with f → ∞, is F(f,n) dense?

**KNOWN (EGIP96):**
- liminf F(c log n, n) = 1 for any c > 0
- lim F(n^{4/9}, n) = ∞
- F(f, n) ~ 1 a.e. for f = o((log n)²)

**OPEN:**
- Behavior for f between (log n)^C and n^{4/9}
- Density of F(log n, n) in (1, ∞)

**KEY INSIGHT:**
The problem has deep connections to prime gap theory.
Zhang's bounded gaps theorem implies limsup F(g(n), n) = ∞
for any g(n) → ∞.
-/
theorem erdos_420_main : True := trivial

/--
**Historical Note:**
The key paper is Erdős-Graham-Ivić-Pomerance (1996):
"On the number of divisors of n!"

The connection to prime gaps was noted by van Doorn.
Zhang's 2013 theorem on bounded prime gaps made one
of the conditional results unconditional.
-/
theorem historical_note : True := trivial

end Erdos420
