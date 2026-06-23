/-
Erdős Problem #284: Maximum First Denominator for Egyptian Fraction Representations of 1

Source: https://erdosproblems.com/284
Status: SOLVED (Croot 2001)

Statement:
Let f(k) be the maximal n₁ such that there exist n₁ < n₂ < ... < nₖ with
1 = 1/n₁ + 1/n₂ + ... + 1/nₖ.

Is it true that f(k) = (1 + o(1)) · k/(e-1)?

Answer: YES

Key Results:
- Upper bound: f(k) ≤ (1+o(1))k/(e-1) is trivial (harmonic series)
- Croot (2001): For any N > 1, ∃ distinct n₁ < ... < nₖ ∈ (N, eN]
  with 1 = Σ 1/nᵢ. This implies the matching lower bound.

The constant e - 1 ≈ 1.718 comes from ∫₁^e 1/x dx = 1.

Tags: number-theory, unit-fractions, egyptian-fractions
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Finset Real

namespace Erdos284

/-
## Part I: Egyptian Fraction Representations
-/

/--
**Unit Fractions:**
A unit fraction is 1/n for positive integer n.
-/
def UnitFraction (n : ℕ) (hn : n ≥ 1) : ℚ := 1 / n

/--
**Egyptian Fraction Representation:**
A representation of r as a sum of distinct unit fractions.
-/
def IsEgyptianRep (S : Finset ℕ) (r : ℚ) : Prop :=
  (∀ n ∈ S, n ≥ 1) ∧ S.sum (fun n => (1 : ℚ) / n) = r

/--
**Representations of 1:**
A set of distinct positive integers whose reciprocals sum to 1.
-/
def RepresentsOne (S : Finset ℕ) : Prop :=
  IsEgyptianRep S 1

/--
**Minimum Element:**
For a finite set of positive integers, the minimum element.
-/
def minElement (S : Finset ℕ) (hS : S.Nonempty) : ℕ := S.min' hS

/-
## Part II: The Function f(k)
-/

/--
**The f(k) Function:**
f(k) = max{n₁ : ∃ n₁ < ... < nₖ with 1 = Σ 1/nᵢ}
The maximum first denominator in a k-term representation of 1.
Axiomatized since the sSup formulation requires showing the set is
bounded above and nonempty.
-/
axiom f (k : ℕ) : ℕ

/--
**f is well-defined for k ≥ 2:**
There exist k-term representations of 1 for k ≥ 2.
-/
/-
## Part III: The Upper Bound
-/

/--
**Harmonic Series in an Interval:**
Σ_{u ≤ n ≤ eu} 1/n ≈ 1 as u → ∞.

More precisely: Σ_{n=u}^{⌊eu⌋} 1/n = 1 + o(1).
-/
/--
**Upper Bound (Trivial):**
f(k) ≤ (1 + o(1)) · k/(e-1)

Proof: If n₁ = u is the first denominator, we need k terms from [u, ∞).
The reciprocal sum from [u, eu] is about 1, so we need at least (e-1)u terms.
Hence k ≥ (e-1-o(1))u, giving u ≤ (1+o(1))k/(e-1).
-/
axiom f_upper_bound :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
      (f k : ℝ) ≤ (1 + ε) * k / (Real.exp 1 - 1)

/-- **Note**: The previously axiomatized `e_minus_one_constant` stating
    `Real.exp 1 - 1 = ∫ x in 1..e, 1/x` was mathematically incorrect
    (the integral equals 1 = ln e, not e - 1 ≈ 1.718). It was unused
    by any theorem, so it has been removed. -/

/-
## Part IV: Croot's Lower Bound (2001)
-/

/--
**Croot's Theorem (2001):**
For any N > 1, there exist distinct integers n₁ < ... < nₖ
in the interval (N, eN] such that 1 = Σ 1/nᵢ.
-/
/--
**Croot's Result Implies Lower Bound:**
f(k) ≥ (1 - o(1)) · k/(e-1)
-/
axiom f_lower_bound :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
      (f k : ℝ) ≥ (1 - ε) * k / (Real.exp 1 - 1)

/--
**The Main Result:**
f(k) = (1 + o(1)) · k/(e-1)
-/
/-
## Part V: Examples
-/

/--
**Example: k = 4** (PROVED)
1 = 1/2 + 1/4 + 1/5 + 1/20
Here n₁ = 2, and we expect f(4) ≈ 4/(e-1) ≈ 2.33.
-/
theorem example_k4 : RepresentsOne {2, 4, 5, 20} := by
  constructor
  · intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn; omega
  · simp only [Finset.sum_insert (show (2 : ℕ) ∉ ({4, 5, 20} : Finset ℕ) by decide),
      Finset.sum_insert (show (4 : ℕ) ∉ ({5, 20} : Finset ℕ) by decide),
      Finset.sum_insert (show (5 : ℕ) ∉ ({20} : Finset ℕ) by decide),
      Finset.sum_singleton]
    norm_num

/-
## Part VI: Summary
-/

/--
**Erdős Problem #284: SOLVED**

**QUESTION:** Is f(k) = (1 + o(1)) · k/(e-1)?
where f(k) = max{n₁ : 1 = 1/n₁ + ... + 1/nₖ}

**ANSWER:** YES (Croot 2001)

**KEY INSIGHT:** The interval (N, eN] has harmonic sum ≈ 1,
so for k terms starting at n₁ = N, we need k ≈ (e-1)N.
Solving: N ≈ k/(e-1).

**TECHNIQUES:**
- Upper bound: Direct counting using harmonic series
- Lower bound: Constructive proof showing such representations exist
-/
theorem erdos_284_summary :
    -- Upper bound
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (f k : ℝ) ≤ (1 + ε) * k / (Real.exp 1 - 1)) ∧
    -- Lower bound
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (f k : ℝ) ≥ (1 - ε) * k / (Real.exp 1 - 1)) :=
  ⟨f_upper_bound, f_lower_bound⟩

/--
**Erdős Problem #284: SOLVED**
f(k) = (1 + o(1)) · k/(e-1), proved by Croot (2001).
-/
theorem erdos_284 :
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (f k : ℝ) ≤ (1 + ε) * k / (Real.exp 1 - 1)) ∧
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (f k : ℝ) ≥ (1 - ε) * k / (Real.exp 1 - 1)) :=
  erdos_284_summary

end Erdos284
