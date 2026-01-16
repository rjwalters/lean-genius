/-
Erdős Problem #295: Egyptian Fractions with Large Denominators

Let N ≥ 1 and let k(N) denote the smallest k such that there exist
N ≤ n₁ < n₂ < ... < nₖ with 1 = 1/n₁ + 1/n₂ + ... + 1/nₖ.

**Question (OPEN)**: Is it true that lim_{N→∞} k(N) - (e-1)N = ∞?

**Known Result**: Erdős and Straus (1971) proved the existence of
constants c > 0 and O > 0 such that:
  -c < k(N) - (e-1)N ≪ N/log N

This bounds k(N) between (e-1)N - c and (e-1)N + O·N/log N for large N.
The question of whether k(N) - (e-1)N → ∞ remains open.

Reference: https://erdosproblems.com/295
Original source: [ErGr80] Erdős-Graham, Old and New Problems in Combinatorial Number Theory
Related: [ErSt71b] Erdős-Straus, Amer. Math. Monthly (1971), 302-303
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Basic

open scoped Real
open Filter

namespace Erdos295

/-!
## Egyptian Fractions Background

An Egyptian fraction is a sum of distinct unit fractions (fractions with numerator 1).
Every positive rational can be written as an Egyptian fraction - this goes back to
ancient Egypt and was studied extensively by Fibonacci.

This problem asks about representations of 1 as an Egyptian fraction where all
denominators are at least N. As N grows, we need more terms to sum to 1.
-/

/--
For each N, there exists a representation of 1 as a sum of distinct unit fractions
with all denominators ≥ N. This is a foundational existence result.

For example:
- N = 2: 1 = 1/2 + 1/3 + 1/6
- N = 3: 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/20

The existence follows from the greedy algorithm: repeatedly subtract the largest
possible unit fraction 1/⌈1/r⌉ from the remaining sum r, starting with r = 1.
-/
axiom exists_egyptian_representation (N : ℕ) (hN : N ≥ 1) :
    ∃ (k : ℕ) (n : Fin k → ℕ),
      k ≥ 1 ∧
      (∀ i, N ≤ n i) ∧
      Function.Injective n ∧
      (∀ i j, i < j → n i < n j) ∧
      ∑ i, (1 : ℝ) / n i = 1

/--
k(N) is the smallest number of terms needed to represent 1 as a sum of
distinct unit fractions with all denominators at least N.

This axiom asserts the existence of this minimal value.
-/
axiom k (N : ℕ) : ℕ

/--
k(N) achieves a representation of 1 with all denominators ≥ N.
-/
axiom k_achieves (N : ℕ) (hN : N ≥ 1) :
    ∃ (n : Fin (k N) → ℕ),
      (∀ i, N ≤ n i) ∧
      Function.Injective n ∧
      (∀ i j, i < j → n i < n j) ∧
      ∑ i, (1 : ℝ) / n i = 1

/--
k(N) is minimal: any representation with denominators ≥ N needs at least k(N) terms.
-/
axiom k_minimal (N : ℕ) (m : ℕ) (n : Fin m → ℕ)
    (hN : ∀ i, N ≤ n i) (hsum : ∑ i, (1 : ℝ) / n i = 1) : k N ≤ m

/--
The Erdős-Straus theorem (1971): There exist constants c > 0 and O > 0 such that
for all sufficiently large N:
  -c < k(N) - (e-1)·N < O · N / log N

This is a deep result in analytic number theory. The proof uses careful analysis
of the harmonic series and properties of Egyptian fraction representations.

The lower bound -c shows k(N) ≥ (e-1)N - c, meaning we need at least about (e-1)N terms.
The upper bound shows k(N) ≤ (e-1)N + O(N/log N), providing an efficient construction.

The appearance of e-1 ≈ 1.718 is related to the fact that the harmonic series
H_n = 1 + 1/2 + ... + 1/n ≈ ln(n) + γ, where γ is the Euler-Mascheroni constant.
-/
axiom erdos_straus_bounds :
    ∃ (C : ℝ) (O : ℝ), C > 0 ∧ O > 0 ∧
      ∀ᶠ (N : ℕ) in atTop,
        (k N : ℝ) - (Real.exp 1 - 1) * N > -C ∧
        (k N : ℝ) - (Real.exp 1 - 1) * N < O * N / Real.log N

/--
**OPEN PROBLEM**: Does k(N) - (e-1)N → ∞ as N → ∞?

The Erdős-Straus bounds show:
  -c < k(N) - (e-1)N < O · N/log N

The lower bound is constant, but the upper bound grows (slowly) with N.
The question is whether the actual value tends to infinity, or remains bounded.

This formalization states the open question. The `Prop` here represents
the mathematical statement that k(N) - (e-1)N → +∞.
-/
def erdos_295_conjecture : Prop :=
  Tendsto (fun N => (k N : ℝ) - (Real.exp 1 - 1) * N) atTop atTop

/--
Note: The main conjecture `erdos_295_conjecture` is OPEN as of 2024.
Neither a proof nor a disproof is known.
-/
theorem erdos_295_is_open : True := trivial

/-!
## Concrete Examples

For small N, we can verify specific Egyptian fraction decompositions.
-/

/--
Example: 1 = 1/2 + 1/3 + 1/6 (denominators ≥ 2)
This shows k(2) ≤ 3.
-/
theorem example_N2 : (1 : ℚ)/2 + 1/3 + 1/6 = 1 := by norm_num

/--
Example: 1 = 1/2 + 1/4 + 1/5 + 1/20 (denominators ≥ 2)
Another representation with 4 terms.
-/
theorem example_N2_alt : (1 : ℚ)/2 + 1/4 + 1/5 + 1/20 = 1 := by norm_num

/--
Example: 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/20 (denominators ≥ 3)
This is one possible representation for N = 3.
-/
theorem example_N3 : (1 : ℚ)/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1 := by norm_num

/--
The value (e-1) ≈ 1.71828... appears because for large N, the minimum number
of unit fractions 1/n with n ≥ N needed to sum to 1 is approximately (e-1)N.

This comes from the asymptotic: ∑_{n=N}^{M} 1/n ≈ ln(M/N), and we need
ln(M/N) ≈ 1 (to sum to 1), giving M ≈ eN, so roughly (e-1)N terms.
-/
theorem e_minus_one_positive : Real.exp 1 - 1 > 0 := by
  have h := Real.one_lt_exp_iff.mpr (by norm_num : (1 : ℝ) > 0)
  linarith

end Erdos295
