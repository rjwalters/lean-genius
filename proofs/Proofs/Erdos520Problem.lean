/-
  Erdős Problem #520: Rademacher Multiplicative Functions

  Let f be a Rademacher multiplicative function: a random {-1, 0, 1}-valued
  multiplicative function where for each prime p we independently choose
  f(p) ∈ {-1, 1} uniformly at random, and extend multiplicatively to
  square-free integers (with f(n) = 0 if n is not square-free).

  **Conjecture (OPEN)**: Does there exist some constant c > 0 such that,
  almost surely,
    limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √(N log log N) = c?

  This is related to the law of the iterated logarithm for random
  multiplicative functions.

  References:
  - https://erdosproblems.com/520
  - Wintner, A., "Random factorizations and Riemann's hypothesis" (1944)
  - Harper, A. J., "Moments of random multiplicative functions" (2020)
-/

import Mathlib

open MeasureTheory ProbabilityTheory Nat Real Filter Set Finset

namespace Erdos520

/-
## Core Definitions

A Rademacher multiplicative function is a random multiplicative function where:
- f(1) = 1
- For each prime p, f(p) ∈ {-1, 1} chosen uniformly and independently
- For square-free n = p₁...pᵣ, f(n) = f(p₁)...f(pᵣ)
- For non-square-free n, f(n) = 0
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A random function f : ℕ → Ω → ℝ is **Rademacher multiplicative** if:
- f(1) = 1 always
- For each prime p, f(p) is uniformly distributed on {-1, 1}
- The values at different primes are independent
- f is extended multiplicatively to square-free integers
- f(n) = 0 for non-square-free n -/
structure IsRademacherMultiplicative (f : ℕ → Ω → ℝ) : Prop where
  /-- f(1) = 1 for all outcomes. -/
  map_one : ∀ ω, f 1 ω = 1
  /-- For primes, f(p) is uniformly distributed on {-1, 1}. -/
  prob_of_prime : ∀ p, p.Prime → ℙ {ω | f p ω = 1} = 1/2 ∧ ℙ {ω | f p ω = -1} = 1/2
  /-- Values at different primes are independent. -/
  indep_primes : ∀ p q, p.Prime → q.Prime → p ≠ q →
    ℙ {ω | f p ω = 1 ∧ f q ω = 1} = ℙ {ω | f p ω = 1} * ℙ {ω | f q ω = 1}
  /-- f is multiplicative on coprime arguments. -/
  map_mul_coprime : ∀ a b ω, a.Coprime b → f (a * b) ω = f a ω * f b ω
  /-- f vanishes on non-square-free integers. -/
  map_non_squarefree : ∀ n ω, ¬Squarefree n → f n ω = 0

/-
## The Partial Sum

The partial sum S_N(ω) = ∑_{m ≤ N} f(m, ω) is the key object of study.
-/

/-- The partial sum of f up to N. -/
noncomputable def partialSum (f : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Icc 1 N, f m ω

/-- The normalized partial sum: S_N / √(N log log N). -/
noncomputable def normalizedSum (f : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  if _h : N ≥ 3 then
    partialSum f N ω / Real.sqrt (N * Real.log (Real.log N))
  else 0

/-
## The Main Conjecture (OPEN)

Does the limsup of the normalized sum converge to a universal constant?
-/

/-- **Erdős Problem #520 (OPEN)**: For Rademacher multiplicative functions,
does there exist a constant c > 0 such that almost surely,
  limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √(N log log N) = c?

This asks whether the law of the iterated logarithm holds for random
multiplicative functions with a universal constant. -/

/-
## Related Results

Several partial results are known about moments and fluctuations.
-/

/-- **Wintner's Result (1944)**: The partial sums satisfy E[S_N²] = ∑_{m ≤ N, squarefree} 1.

This is because E[f(m)f(n)] = 1 if m = n and squarefree, 0 otherwise. -/

/-- The number of square-free integers up to N is asymptotically (6/π²)N.

This implies E[S_N²] ~ (6/π²)N. -/

/-- **Harper's Bound (2020)**: The moments of S_N have specific growth rates.

For k ≥ 1: E[|S_N|^{2k}] ≍ N^k (log log N)^{k²}. -/

/-
## Properties of Rademacher Multiplicative Functions
-/

/-
## Connection to the Law of the Iterated Logarithm

The normalization √(N log log N) comes from the LIL. For i.i.d. random
variables, the LIL says:
  limsup_{N → ∞} S_N / √(2N log log N) = σ   almost surely

For multiplicative functions, the dependence structure changes the constant.
-/

/-- The classical LIL constant for i.i.d. is √2.
For multiplicative functions, the constant may be different. -/
noncomputable def lilConstant : ℝ := Real.sqrt 2

/-
## The Square-Free Sieve

The structure of square-free integers is crucial for understanding
Rademacher multiplicative functions.
-/

/-- The indicator of square-free integers. -/
def squarefreeIndicator (n : ℕ) : ℕ := if Squarefree n then 1 else 0

/-- For square-free n with prime factorization n = p₁...pᵣ,
f(n) = f(p₁)...f(pᵣ) which is uniformly distributed on {-1, 1}. -/

end Erdos520
