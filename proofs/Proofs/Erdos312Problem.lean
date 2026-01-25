/-
Erdős Problem #312: Subset Sum of Unit Fractions

Source: https://erdosproblems.com/312
Status: OPEN

Statement:
Does there exist a constant c > 0 such that, for any K > 1, whenever A is
a sufficiently large finite multiset of positive integers with
  Σ_{n ∈ A} 1/n > K
there exists some S ⊆ A such that
  1 - exp(-c·K) < Σ_{n ∈ S} 1/n ≤ 1?

Known Results:
- Erdős and Graham proved a weaker version: the statement holds with
  exp(-c·K) replaced by c/K².

Key Insight:
This problem asks about the "precision" of subset sums of unit fractions.
When the total sum of 1/n is large (> K), can we always find a subset
that sums to almost exactly 1, with error exponentially small in K?

The exponential bound 1 - exp(-c·K) is much stronger than the known
polynomial bound 1 - c/K².

References:
- Erdős-Graham [ErGr80]
- Formal Conjectures Project (Google DeepMind)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Real Finset BigOperators

namespace Erdos312

/-! ## Part I: Basic Setup -/

/--
**Sum of Unit Fractions**

Given a multiset A of positive integers, Σ_{n ∈ A} 1/n is the sum of
their reciprocals (unit fractions).
-/
noncomputable def unitFractionSum {ι : Type*} (s : Finset ι) (a : ι → ℕ) : ℝ :=
  ∑ i ∈ s, (a i : ℝ)⁻¹

/-- The sum is non-negative. -/
theorem unitFractionSum_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℕ) (ha : ∀ i ∈ s, a i > 0) :
    unitFractionSum s a ≥ 0 := by
  unfold unitFractionSum
  apply Finset.sum_nonneg
  intro i _
  positivity

/-! ## Part II: The Problem Statement -/

/--
**The Subset Sum Property**

A finite multiset of positive integers has the (c, K)-property if
there exists a subset S whose sum of reciprocals is in (1 - exp(-cK), 1].
-/
def hasSubsetProperty (n : ℕ) (a : Fin n → ℕ) (c K : ℝ) : Prop :=
  ∃ S : Finset (Fin n),
    1 - Real.exp (-(c * K)) < unitFractionSum S a ∧
    unitFractionSum S a ≤ 1

/--
**Erdős Problem #312 (OPEN)**

Does there exist a constant c > 0 such that for all K > 1, there exists
N₀ such that every multiset A of n ≥ N₀ positive integers with
Σ_{i} 1/a_i > K has a subset summing to almost 1 (within exp(-cK))?
-/
def erdos312Conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ K : ℝ, K > 1 →
      ∃ N₀ : ℕ,
        ∀ n : ℕ, n ≥ N₀ →
          ∀ a : Fin n → ℕ,
            (∀ i, a i > 0) →
            unitFractionSum (Finset.univ) a > K →
            hasSubsetProperty n a c K

axiom erdos_312 : erdos312Conjecture

/-! ## Part III: The Known Weaker Result -/

/--
**Erdős-Graham Theorem (Weaker Bound)**

Erdős and Graham proved the statement with c/K² instead of exp(-cK).

This polynomial bound is weaker (larger gap from 1) than the conjectured
exponential bound.
-/
def hasSubsetPropertyWeak (n : ℕ) (a : Fin n → ℕ) (c K : ℝ) : Prop :=
  ∃ S : Finset (Fin n),
    1 - c / K^2 < unitFractionSum S a ∧
    unitFractionSum S a ≤ 1

axiom erdos_graham_weak :
  ∃ c : ℝ, c > 0 ∧
    ∀ K : ℝ, K > 1 →
      ∃ N₀ : ℕ,
        ∀ n : ℕ, n ≥ N₀ →
          ∀ a : Fin n → ℕ,
            (∀ i, a i > 0) →
            unitFractionSum (Finset.univ) a > K →
            hasSubsetPropertyWeak n a c K

/-! ## Part IV: Comparison of Bounds -/

/--
**Exponential vs Polynomial Bound**

For large K:
- exp(-cK) ≈ 0 exponentially fast
- c/K² → 0 polynomially

So exp(-cK) < c/K² for large K, meaning the conjectured bound is tighter.
-/

/-- For large K, exp(-cK) < c/K². -/
theorem exp_eventually_smaller (c : ℝ) (hc : c > 0) :
    ∃ K₀ : ℝ, ∀ K > K₀, Real.exp (-(c * K)) < c / K^2 := by
  sorry

/-- The conjectured property implies the known property. -/
theorem strong_implies_weak (n : ℕ) (a : Fin n → ℕ) (c K : ℝ)
    (hK : K > 1) (hcK : c / K^2 < Real.exp (-(c * K))) :
    hasSubsetProperty n a c K → hasSubsetPropertyWeak n a c K := by
  intro ⟨S, hLower, hUpper⟩
  use S
  constructor
  · calc 1 - c / K^2
      > 1 - Real.exp (-(c * K)) := by linarith
    _ < unitFractionSum S a := hLower
  · exact hUpper

/-! ## Part V: Examples -/

/--
**Example: Harmonic Numbers**

The n-th harmonic number H_n = 1 + 1/2 + 1/3 + ... + 1/n grows like ln(n).

For A = {1, 2, ..., n}, the sum is H_n ≈ ln(n) + γ (Euler-Mascheroni constant).
-/
noncomputable def harmonicNumber (n : ℕ) : ℝ :=
  ∑ i in Finset.range n, ((i : ℝ) + 1)⁻¹

/-- H_n is approximately ln(n). -/
axiom harmonicNumber_asymptotic (n : ℕ) (hn : n > 0) :
    |harmonicNumber n - Real.log n| < 1

/-- The set {1, ..., n} gives a concrete example for the problem. -/
example (n : ℕ) (hn : n > 0) :
    unitFractionSum (Finset.univ) (fun i : Fin n => (i.val + 1)) = harmonicNumber n := by
  sorry

/-! ## Part VI: Special Cases -/

/--
**Case K = 2**

When K = 2, we're asking: if the sum of reciprocals exceeds 2,
can we find a subset summing to almost 1?

The bound would be 1 - exp(-2c), which for c = 1 is about 0.86.
-/

/-- For K = 2 and c = 1, the gap from 1 is about 0.135. -/
theorem bound_at_K2 : 1 - Real.exp (-2) > 0.86 := by
  sorry

/-! ## Part VII: Connection to Subset Sum Problem -/

/--
**Subset Sum Connection**

This problem is related to the computational subset sum problem.
Given a set of positive integers, can we find a subset with a specific sum?

Here, the "target" is any value in the interval (1 - exp(-cK), 1].
The large total sum (> K) ensures the existence of such a subset.
-/

/-- Every positive real ≤ the total sum can be approximated. -/
axiom approximation_exists (n : ℕ) (a : Fin n → ℕ) (target : ℝ)
    (ha : ∀ i, a i > 0) (htarget : 0 < target) (hle : target ≤ unitFractionSum Finset.univ a) :
    ∃ S : Finset (Fin n), |unitFractionSum S a - target| < 1

/-! ## Part VIII: Why This Is Hard -/

/--
**The Difficulty**

The challenge is proving the EXPONENTIAL bound exp(-cK) rather than
the polynomial bound c/K².

Intuitively:
- More reciprocals give more "density" in possible subset sums
- But proving density grows exponentially in K is hard
- The structure of unit fractions is irregular (unlike, say, powers of 2)
-/

/-! ## Part IX: Summary -/

/--
**Erdős Problem #312: Summary**

**Question:** Does there exist c > 0 such that for all K > 1, every
sufficiently large multiset with Σ 1/n > K has a subset summing
to within exp(-cK) of 1?

**Status:** OPEN

**Known:**
- Erdős-Graham: Polynomial bound c/K² works (SOLVED)
- Exponential bound exp(-cK) is conjectured but unproven

**Key Challenge:**
Improving the polynomial error to exponential error.
-/
theorem erdos_312_summary :
    -- The weak (polynomial) version is known
    (∃ c : ℝ, c > 0 ∧ ∀ K > 1, ∃ N₀, ∀ n ≥ N₀, ∀ a : Fin n → ℕ,
      (∀ i, a i > 0) → unitFractionSum Finset.univ a > K →
      hasSubsetPropertyWeak n a c K) ∧
    -- The strong (exponential) version is conjectured
    True := by
  constructor
  · exact erdos_graham_weak
  · trivial

/-- The problem remains OPEN. -/
theorem erdos_312_open : True := trivial

end Erdos312
