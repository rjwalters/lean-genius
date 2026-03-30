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

/-- Euler's totient function φ(n) -/
noncomputable def eulerPhi (n : ℕ) : ℕ := Nat.totient n

/-- A real α is (f, q)-approximable if |α - p/q| < f(q)/q for some coprime p -/
def IsApproximable (α : ℝ) (f : ℕ → ℕ) (q : ℕ) : Prop :=
  ∃ p : ℤ, Int.gcd p.natAbs q = 1 ∧ |α - (p : ℝ) / q| < (f q : ℝ) / q

/-- A real α is infinitely f-approximable if approximable for infinitely many q -/
def IsInfinitelyApproximable (α : ℝ) (f : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ q > N, IsApproximable α f q

/- ## Part II: The Divergence Condition -/

/-- The Duffin-Schaeffer sum: ∑_{q=1}^{N} φ(q) · f(q) / q -/
noncomputable def DuffinSchaefferSum (f : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (N + 1), (eulerPhi q : ℝ) * (f q : ℝ) / q

/-- The Duffin-Schaeffer series diverges -/
def SeriesDiverges (f : ℕ → ℕ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, DuffinSchaefferSum f N > M

/-- The Duffin-Schaeffer series converges -/
def SeriesConverges (f : ℕ → ℕ) : Prop :=
  ∃ L : ℝ, ∀ N : ℕ, DuffinSchaefferSum f N ≤ L

/- ## Part III: Measure-Theoretic Formulation -/

/-- "Almost all" reals means measure 1 in [0,1] -/
def AlmostAll (P : ℝ → Prop) : Prop :=
  ∃ S : Set ℝ, (∀ x ∈ S, P x) ∧ MeasureTheory.volume (Set.Icc 0 1 \ S) = 0

/-- Almost all α are infinitely f-approximable -/
def AlmostAllApproximable (f : ℕ → ℕ) : Prop :=
  AlmostAll (fun α => IsInfinitelyApproximable α f)

/-- Almost no α is infinitely f-approximable -/
def AlmostNoneApproximable (f : ℕ → ℕ) : Prop :=
  AlmostAll (fun α => ¬IsInfinitelyApproximable α f)

/- ## Part IV: The Duffin-Schaeffer Conjecture -/

/-- The Duffin-Schaeffer Conjecture: Divergence ↔ Almost all approximable -/
def DuffinSchaefferConjecture : Prop :=
  ∀ f : ℕ → ℕ, SeriesDiverges f ↔ AlmostAllApproximable f

/-- The easy direction: Approximable ⟹ Divergence (via Borel-Cantelli) -/
/-- The hard direction: Divergence ⟹ Approximable (the actual conjecture).
    This took 79 years to prove (1941-2020). -/
/- ## Part V: Erdős's Partial Result -/

/-- Erdős's condition: f(q) · q is bounded -/
def ErdosCondition (f : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ q : ℕ, f q * q ≤ C

/-- Erdős's theorem: The conjecture holds when f(q)·q is bounded -/
/- ## Part VI: Koukoulopoulos-Maynard Theorem (2020) -/

/-- Koukoulopoulos-Maynard (2020): The full Duffin-Schaeffer conjecture.
    Published in Annals of Mathematics 192(1), 251-307. -/
axiom koukoulopoulos_maynard_2020 : DuffinSchaefferConjecture

/-- The Duffin-Schaeffer theorem (named version) -/
theorem duffin_schaeffer_theorem : DuffinSchaefferConjecture :=
  koukoulopoulos_maynard_2020

/- ## Part VII: Consequences -/

/-- If the series converges, almost no α is infinitely approximable -/
/-- Zero-One Law: either almost all or almost none are approximable.
    Follows from the Duffin-Schaeffer theorem: divergence gives 'all',
    convergence gives 'none'. -/
axiom zero_one_law (f : ℕ → ℕ) :
    AlmostAllApproximable f ∨ AlmostNoneApproximable f

/-- Classical case: f(q) = 1 gives almost all approximable (continued fractions) -/
/- ## Part VIII: Khintchine's Theorem (Related) -/

/-- Khintchine's original theorem (1924): for monotone decreasing f,
    ∑ f(q)/q = ∞ ↔ almost all α are approximable.
    Duffin-Schaeffer generalizes this to non-monotone f with the φ(q) correction. -/
/-- The limsup set of infinitely approximable reals -/
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
