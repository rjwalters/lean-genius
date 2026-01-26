/-!
# Erdős Problem #47: Unit Fractions from Dense Sets

**Source:** [erdosproblems.com/47](https://erdosproblems.com/47)
**Status:** SOLVED (Bloom [Bl21], improved by Liu–Sawhney [LiSa24])

## Statement

If δ > 0 and N is sufficiently large, and A ⊆ {1, …, N} satisfies
∑_{a ∈ A} 1/a > δ log N, must there exist S ⊆ A such that ∑_{n ∈ S} 1/n = 1?

## Background

Bloom proved the answer is YES with threshold ∑ 1/a ≫ (log log log N)/(log log N) · log N.
Liu and Sawhney improved this to ∑ 1/a ≫ (log N)^{4/5 + o(1)}.
Erdős conjectured ≫ (log log N)² might suffice; Pomerance showed this is optimal.

## Approach

We formalize the key definitions (unit fraction subsets, reciprocal sum
density) and state Bloom's theorem and the Liu–Sawhney improvement
as axioms. The density threshold is captured via the reciprocal sum.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset Filter

namespace Erdos47

/-! ## Part I: Unit Fraction Subsets -/

/--
The reciprocal sum of a finite set of positive integers: ∑_{a ∈ A} 1/a.
Computed over ℚ for exactness.
-/
noncomputable def reciprocalSum (A : Finset ℕ) : ℚ :=
  A.sum fun a => if a = 0 then 0 else (1 : ℚ) / a

/--
A set S has unit fraction sum: ∑_{n ∈ S} 1/n = 1.
-/
def HasUnitFractionSum (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, n ≥ 1) ∧ reciprocalSum S = 1

/--
A set A contains a unit fraction subset: there exists S ⊆ A
with ∑_{n ∈ S} 1/n = 1.
-/
def ContainsUnitFraction (A : Finset ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧ HasUnitFractionSum S

/-! ## Part II: Dense Subsets of {1, ..., N} -/

/--
The interval {1, …, N} as a Finset.
-/
def Icc1 (N : ℕ) : Finset ℕ := (Finset.range N).image (· + 1)

/--
A ⊆ {1, …, N} with large reciprocal sum (at least δ · log N).
-/
def IsDenseSubset (A : Finset ℕ) (N : ℕ) (δ : ℚ) : Prop :=
  A ⊆ Icc1 N ∧
  (∀ a ∈ A, a ≥ 1) ∧
  δ > 0 ∧
  reciprocalSum A > δ * Real.log N

/-! ## Part III: Erdős's Conjecture (Solved) -/

/--
**Erdős Problem #47 (original formulation):**
For every δ > 0, there exists N₀ such that for all N ≥ N₀,
if A ⊆ {1, …, N} has ∑ 1/a > δ log N, then A contains a
subset S with ∑ 1/n = 1.
-/
def ErdosConjecture47 : Prop :=
  ∀ δ : ℚ, δ > 0 →
    ∃ N₀ : ℕ,
      ∀ N : ℕ, N ≥ N₀ →
        ∀ A : Finset ℕ,
          IsDenseSubset A N δ →
          ContainsUnitFraction A

/-! ## Part IV: Bloom's Theorem -/

/--
**Bloom's Theorem [Bl21]:**
Erdős Problem #47 is true. In fact, a quantitative threshold suffices:
if ∑ 1/a ≫ (log log log N)/(log log N) · log N, then A contains
a unit fraction subset.

We state the qualitative version as the main result.
-/
axiom bloom_theorem : ErdosConjecture47

/--
**Bloom's quantitative bound:**
There exists an absolute constant C such that if A ⊆ {1, …, N}
and ∑ 1/a ≥ C · (log log log N / log log N) · log N, then
A contains a unit fraction subset.
-/
axiom bloom_quantitative :
  ∃ C : ℚ, C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      ∀ A : Finset ℕ, A ⊆ Icc1 N →
        reciprocalSum A ≥ C * (Real.log (Real.log (Real.log N)) /
          Real.log (Real.log N)) * Real.log N →
        ContainsUnitFraction A

/-! ## Part V: Liu–Sawhney Improvement -/

/--
**Liu–Sawhney Improvement [LiSa24]:**
The threshold can be improved to ∑ 1/a ≫ (log N)^{4/5 + o(1)}.
-/
axiom liu_sawhney_improvement :
  ∀ ε : ℚ, ε > 0 →
    ∃ N₀ : ℕ,
      ∀ N : ℕ, N ≥ N₀ →
        ∀ A : Finset ℕ, A ⊆ Icc1 N →
          reciprocalSum A ≥ (Real.log N : ℚ) ^ ((4 : ℚ) / 5 + ε) →
          ContainsUnitFraction A

/-! ## Part VI: Pomerance's Optimality -/

/--
**Pomerance's construction:**
There exist sets A ⊆ {1, …, N} with ∑ 1/a ≫ (log log N)²
that contain no unit fraction subset. This shows Erdős's guess
of (log log N)² as the threshold would be essentially tight.
-/
axiom pomerance_lower_bound :
  ∀ N₀ : ℕ, ∃ N : ℕ, N ≥ N₀ ∧
    ∃ A : Finset ℕ, A ⊆ Icc1 N ∧
      reciprocalSum A ≥ (Real.log (Real.log N) : ℚ) ^ 2 ∧
      ¬ContainsUnitFraction A

/-! ## Part VII: Summary -/

/--
**Summary:**
Erdős Problem #47 is solved. Dense subsets of {1, …, N} (with large
reciprocal sum) contain unit fraction subsets. Bloom proved the
conjecture; Liu–Sawhney improved the quantitative bound.
-/
theorem erdos_47_summary : ErdosConjecture47 := bloom_theorem

end Erdos47
