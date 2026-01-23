/-
Erdős Problem #451: Prime-Free Consecutive Products

**Question**: Estimate n_k, the smallest integer > 2k such that
∏_{1 ≤ i ≤ k}(n_k - i) has no prime factor in (k, 2k).

**Status**: OPEN - The exact growth rate is unknown.

**Known Bounds**:
- Lower: n_k > k^{1+c} for some constant c (Erdős-Graham)
- Upper: n_k ≤ ∏_{k < p < 2k} p = e^{O(k)} (Adenwalla)

**Conjectures**:
- n_k > k^d for all constant d (superpolynomial growth)
- n_k < e^{o(k)} (subexponential growth)

**Context**: The product (n-1)(n-2)⋯(n-k) for n > 2k typically contains prime
factors in (k, 2k) by Bertrand's postulate. Finding n where this product
AVOIDS all such primes is restrictive. The question is: how restrictive?

**Key Observation**: By Bertrand's postulate, there's always a prime p in (k, 2k).
For the product to avoid p, we need n ≢ i (mod p) for all 1 ≤ i ≤ k.
This gives k forbidden residues. Combining for all primes in (k, 2k)
via Chinese Remainder Theorem gives the upper bound.

References:
- https://erdosproblems.com/451
- [Er79d] Erdős, "Some unconventional problems in number theory" (1979)
-/

import Mathlib

namespace Erdos451

open Nat Finset BigOperators

/-
## Basic Definitions

The product (n-1)(n-2)⋯(n-k) and the condition of having no prime factors in (k, 2k).
-/

/--
The product ∏_{1 ≤ i ≤ k}(n - i) = (n-1)(n-2)⋯(n-k).
This is the falling factorial n(n-1)⋯(n-k+1) shifted by 1.
-/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ range k, (n - (i + 1))

/--
A prime p divides a product iff it divides some factor.
-/
lemma prime_dvd_prod_iff {s : Finset ℕ} {f : ℕ → ℕ} {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ i ∈ s, f i ↔ ∃ i ∈ s, p ∣ f i := by
  simp only [Prime.dvd_finset_prod_iff hp]

/--
The primes in the interval (k, 2k).
-/
def primesInInterval (k : ℕ) : Finset ℕ :=
  (range (2 * k)).filter (fun p => k < p ∧ p.Prime)

/--
The product has no prime factor in (k, 2k).
-/
def hasNoPrimeFactorInInterval (n k : ℕ) : Prop :=
  ∀ p ∈ primesInInterval k, ¬(p ∣ consecutiveProduct n k)

/--
The set of n > 2k satisfying the condition.
-/
def validIntegers (k : ℕ) : Set ℕ :=
  {n : ℕ | 2 * k < n ∧ hasNoPrimeFactorInInterval n k}

/-
## The Main Definition

n_k is the minimum of the valid integers set.
-/

/--
n_k is the smallest integer > 2k with the property.
-/
noncomputable def nk (k : ℕ) : ℕ :=
  sInf {n : ℕ | 2 * k < n ∧ hasNoPrimeFactorInInterval n k}

/-
## Key Observations

Understanding why the set is non-empty and what constrains n_k.
-/

/--
By Bertrand's postulate, there exists a prime p in (k, 2k) for k ≥ 1.
-/
axiom bertrand_postulate (k : ℕ) (hk : 1 ≤ k) :
    ∃ p, k < p ∧ p < 2 * k ∧ p.Prime

/--
The product of all primes in (k, 2k), called the "partial primorial".
This is an upper bound for n_k.
-/
noncomputable def primorialInterval (k : ℕ) : ℕ :=
  ∏ p ∈ primesInInterval k, p

/--
There exists n satisfying the condition, so the set is non-empty.
The upper bound is given by the partial primorial.
-/
axiom validIntegers_nonempty (k : ℕ) (hk : 1 ≤ k) :
    (validIntegers k).Nonempty

/-
## Known Bounds

The proven lower and upper bounds from the literature.
-/

/--
**Erdős-Graham Lower Bound**: There exists c > 0 such that n_k > k^{1+c}.

The proof uses estimates on the number of primes in (k, 2k) and
their distribution among the residues modulo p.
-/
axiom erdos_graham_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 2 → (nk k : ℝ) > k ^ (1 + c)

/--
**Adenwalla Upper Bound**: n_k ≤ primorialInterval(k).

Proof: By Chinese Remainder Theorem, we can find n that avoids all
k residue classes for each prime in (k, 2k). The primorial is such an n.
-/
theorem adenwalla_upper_bound (k : ℕ) (hk : 1 ≤ k) :
    nk k ≤ primorialInterval k := by
  -- The primorial satisfies the condition by CRT argument
  sorry

/--
The primorial is e^{O(k)} by the Prime Number Theorem.
Specifically, ∑_{k < p < 2k} log p ~ k (Chebyshev's θ function).
-/
axiom primorial_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 2 → (primorialInterval k : ℝ) ≤ Real.exp (C * k)

/-
## Conjectured Bounds

What Erdős believed to be true.
-/

/--
**Erdős Conjecture (Lower)**: n_k > k^d for all constant d.
This means n_k grows faster than any polynomial.
-/
axiom erdos_conjecture_lower :
    ∀ d : ℕ, ∀ᶠ k in Filter.atTop, (nk k : ℝ) > k ^ d

/--
**Erdős Conjecture (Upper)**: n_k < e^{o(k)}.
This means n_k grows slower than any exponential.
-/
axiom erdos_conjecture_upper :
    ∀ ε > 0, ∀ᶠ k in Filter.atTop, (nk k : ℝ) < Real.exp (ε * k)

/-
## Why This is Interesting

The problem explores the intersection of:
1. Bertrand's postulate (primes in (k, 2k))
2. Divisibility constraints on products
3. Chinese Remainder Theorem constructions
4. Growth rate questions (polynomial vs exponential)
-/

/--
The condition n ∉ {1, 2, ..., k} (mod p) for all primes p in (k, 2k).
By CRT, the density of such n is ∏_p (1 - k/p) over primes in (k, 2k).
-/
axiom density_argument :
    ∀ k : ℕ, k ≥ 2 →
      ∏ p ∈ primesInInterval k, (1 - (k : ℝ) / p) > 0

/-
## Example Values

Small cases to build intuition.
-/

/-- For k = 1, we need n > 2 with (n-1) having no prime factor in (1, 2).
    But (1, 2) contains no primes, so all n > 2 work. Thus n_1 = 3. -/
theorem nk_one : nk 1 = 3 := by
  sorry

/-- For k = 2, we need n > 4 with (n-1)(n-2) having no prime factor in (2, 4).
    The only prime in (2, 4) is 3. We need (n-1)(n-2) ≢ 0 (mod 3).
    n = 5: (4)(3) = 12, divisible by 3. ✗
    n = 6: (5)(4) = 20, not divisible by 3. ✓
    Thus n_2 = 6. -/
theorem nk_two : nk 2 = 6 := by
  sorry

/-
## Summary

Erdős Problem #451 asks for the growth rate of n_k, the smallest n > 2k
such that (n-1)(n-2)⋯(n-k) has no prime factor in (k, 2k).

**Known**:
- k^{1+c} < n_k ≤ e^{O(k)}

**Conjectured**:
- k^d < n_k < e^{o(k)} for all d

**Open**: The exact growth rate (intermediate between polynomial and exponential).
-/

theorem erdos_451_summary :
    (∃ c : ℝ, c > 0 ∧ ∀ k ≥ 2, (nk k : ℝ) > k ^ (1 + c)) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ k ≥ 2, (nk k : ℝ) ≤ Real.exp (C * k)) :=
  ⟨erdos_graham_lower_bound, by
    obtain ⟨C, hC, h⟩ := primorial_bound
    refine ⟨C, hC, fun k hk => ?_⟩
    calc (nk k : ℝ) ≤ primorialInterval k := by exact_mod_cast adenwalla_upper_bound k (by omega)
      _ ≤ Real.exp (C * k) := h k hk⟩

end Erdos451
