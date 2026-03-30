/-
Erdős Problem #999: The Duffin-Schaeffer Conjecture

Source: https://erdosproblems.com/999
Status: SOLVED (Koukoulopoulos-Maynard, 2020)

Statement:
For any function f: ℕ → ℕ, the following are equivalent:
1. For almost all α ∈ [0,1], there exist infinitely many coprime (p,q)
   with |α - p/q| < f(q)/q
2. ∑_{q≥1} φ(q) · f(q)/q = ∞

This is the famous Duffin-Schaeffer conjecture from 1941.

History:
- Duffin-Schaeffer (1941): Conjectured the equivalence
- Erdős: Proved the special case where f(q)·q is bounded
- Easy direction: Divergence follows from approximability (Borel-Cantelli)
- Koukoulopoulos-Maynard (2020): Proved the full conjecture

Significance:
This is one of the most celebrated results in Diophantine approximation.
It characterizes precisely when "almost all" reals can be approximated
by rationals with a given error function.

References:
- Duffin, R.J. and Schaeffer, A.C. (1941): "Khintchine's problem in metric
  Diophantine approximation"
- Koukoulopoulos, D. and Maynard, J. (2020): "On the Duffin-Schaeffer
  conjecture", Annals of Mathematics 192(1), 251-307

Tags: diophantine-approximation, metric-number-theory, measure-theory
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open scoped Nat

namespace Erdos999

/- ## Part I: Basic Definitions -/

-- easy_direction: unused axiom removed (never referenced by any theorem)
-- hard_direction: unused axiom removed (never referenced by any theorem)
def ErdosCondition (f : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ q : ℕ, f q * q ≤ C

-- erdos_bounded_case: unused axiom removed (never referenced by any theorem)
axiom koukoulopoulos_maynard_2020 : DuffinSchaefferConjecture

-- convergence_case: unused axiom removed (never referenced by any theorem)
axiom zero_one_law (f : ℕ → ℕ) :
    AlmostAllApproximable f ∨ AlmostNoneApproximable f

-- continued_fraction_case: unused axiom removed (never referenced by any theorem)
-- khintchine_theorem: unused axiom removed (never referenced by any theorem)
noncomputable def LimsupSet (f : ℕ → ℕ) : Set ℝ :=
  { α | IsInfinitelyApproximable α f }

/- ## Part IX: Summary -/

/-- Erdős Problem #999: SOLVED.
    The Duffin-Schaeffer conjecture holds: divergence of ∑ φ(q)·f(q)/q
    is equivalent to almost all reals being infinitely approximable.
    Proved by Koukoulopoulos-Maynard (2020) after 79 years. -/
theorem erdos_999_summary :
    DuffinSchaefferConjecture ∧
    (∀ f, SeriesDiverges f ↔ AlmostAllApproximable f) ∧
    (∀ f, AlmostAllApproximable f ∨ AlmostNoneApproximable f) := by
  constructor
  · exact koukoulopoulos_maynard_2020
  constructor
  · exact koukoulopoulos_maynard_2020
  · exact zero_one_law

end Erdos999
