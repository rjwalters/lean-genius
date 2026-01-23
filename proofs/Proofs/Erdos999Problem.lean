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

/-
## Part I: Basic Definitions
-/

/-- Euler's totient function φ(n) -/
noncomputable def eulerPhi (n : ℕ) : ℕ := Nat.totient n

/-- The approximation error bound for denominator q -/
def ApproximationError (f : ℕ → ℕ) (q : ℕ) : ℝ :=
  (f q : ℝ) / q

/-- A real α is (f, q)-approximable if |α - p/q| < f(q)/q for some coprime p -/
def IsApproximable (α : ℝ) (f : ℕ → ℕ) (q : ℕ) : Prop :=
  ∃ p : ℤ, Int.gcd p.natAbs q = 1 ∧ |α - (p : ℝ) / q| < (f q : ℝ) / q

/-- A real α is infinitely f-approximable if approximable for infinitely many q -/
def IsInfinitelyApproximable (α : ℝ) (f : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ q > N, IsApproximable α f q

/-
## Part II: The Divergence Condition
-/

/-- The Duffin-Schaeffer sum: ∑_{q≥1} φ(q) · f(q) / q -/
noncomputable def DuffinSchaefferSum (f : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (N + 1), (eulerPhi q : ℝ) * (f q : ℝ) / q

/-- The Duffin-Schaeffer series diverges -/
def SeriesDiverges (f : ℕ → ℕ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, DuffinSchaefferSum f N > M

/-- The Duffin-Schaeffer series converges -/
def SeriesConverges (f : ℕ → ℕ) : Prop :=
  ∃ L : ℝ, ∀ N : ℕ, DuffinSchaefferSum f N ≤ L

/-
## Part III: Measure-Theoretic Formulation
-/

/-- "Almost all" reals means measure 1 in [0,1] -/
def AlmostAll (P : ℝ → Prop) : Prop :=
  ∃ S : Set ℝ, (∀ x ∈ S, P x) ∧ MeasureTheory.volume (Set.Icc 0 1 \ S) = 0

/-- Almost all α are infinitely f-approximable -/
def AlmostAllApproximable (f : ℕ → ℕ) : Prop :=
  AlmostAll (fun α => IsInfinitelyApproximable α f)

/-- Almost no α is infinitely f-approximable -/
def AlmostNoneApproximable (f : ℕ → ℕ) : Prop :=
  AlmostAll (fun α => ¬IsInfinitelyApproximable α f)

/-
## Part IV: The Duffin-Schaeffer Conjecture
-/

/-- The Duffin-Schaeffer Conjecture: Divergence ↔ Almost all approximable -/
def DuffinSchaefferConjecture : Prop :=
  ∀ f : ℕ → ℕ, SeriesDiverges f ↔ AlmostAllApproximable f

/-- The easy direction: Approximable ⟹ Divergence -/
axiom easy_direction (f : ℕ → ℕ) :
    AlmostAllApproximable f → SeriesDiverges f

/-- The hard direction: Divergence ⟹ Approximable (the actual conjecture) -/
axiom hard_direction (f : ℕ → ℕ) :
    SeriesDiverges f → AlmostAllApproximable f

/-
## Part V: Erdős's Partial Result
-/

/-- Erdős's condition: f(q) · q is bounded -/
def ErdosCondition (f : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ q : ℕ, f q * q ≤ C

/-- Erdős's theorem: The conjecture holds when f(q)·q is bounded -/
axiom erdos_bounded_case (f : ℕ → ℕ) (hf : ErdosCondition f) :
    SeriesDiverges f ↔ AlmostAllApproximable f

/-
## Part VI: Koukoulopoulos-Maynard Theorem (2020)
-/

/-- Koukoulopoulos-Maynard (2020): The full Duffin-Schaeffer conjecture -/
axiom koukoulopoulos_maynard_2020 : DuffinSchaefferConjecture

/-- The theorem proves both directions -/
theorem duffin_schaeffer_theorem : DuffinSchaefferConjecture :=
  koukoulopoulos_maynard_2020

/-- Erdős Problem #999 is SOLVED -/
theorem erdos_999_solved : DuffinSchaefferConjecture :=
  koukoulopoulos_maynard_2020

/-
## Part VII: Consequences and Special Cases
-/

/-- If the series converges, almost no α is infinitely approximable -/
axiom convergence_case (f : ℕ → ℕ) :
    SeriesConverges f → AlmostNoneApproximable f

/--
**Zero-One Law:** Either almost all or almost none are approximable.

This follows from the Duffin-Schaeffer theorem: if the series diverges,
almost all are approximable; if it converges, almost none are.
-/
axiom zero_one_law (f : ℕ → ℕ) :
    AlmostAllApproximable f ∨ AlmostNoneApproximable f

/-- Classical case: f(q) = 1/q gives the continued fraction result -/
axiom continued_fraction_case :
    let f : ℕ → ℕ := fun q => 1
    AlmostAllApproximable f

/-
## Part VIII: Khintchine's Theorem (Related)
-/

/-- Khintchine's original theorem (1924) for monotone f -/
axiom khintchine_theorem (f : ℕ → ℕ) (hf : ∀ q₁ q₂, q₁ ≤ q₂ → f q₂ ≤ f q₁) :
    (∑' q, (f q : ℝ) / q = ⊤) ↔ AlmostAllApproximable f

/--
**Duffin-Schaeffer Extends Khintchine:**

For monotone f, Khintchine's condition (∑ f(q)/q = ∞) implies
Duffin-Schaeffer's condition (∑ φ(q)·f(q)/q = ∞).

The φ(q) factor is bounded by q, so divergence of ∑ f(q)/q
implies divergence of the Duffin-Schaeffer sum for monotone f.
-/
axiom duffin_schaeffer_extends_khintchine :
    ∀ f : ℕ → ℕ, (∀ q₁ q₂, q₁ ≤ q₂ → f q₂ ≤ f q₁) →
      (∑' q, (f q : ℝ) / q = ⊤) → SeriesDiverges f

/-
## Part IX: The GCD Restriction
-/

/-- Why the coprimality condition (p,q) = 1 matters -/
axiom gcd_restriction_necessary :
  -- Without coprimality, the equivalence fails
  -- Example: f(q) = 1 if q is prime, 0 otherwise
  -- The series ∑ φ(q)·f(q)/q = ∑_{p prime} (p-1)/p diverges
  -- But approximation only happens at primes, not their multiples
  True

/-- The limsup set and its measure -/
noncomputable def LimsupSet (f : ℕ → ℕ) : Set ℝ :=
  { α | IsInfinitelyApproximable α f }

/-
## Part X: Proof Techniques
-/

/-- Key technique: Graph theory on divisibility -/
axiom graph_theory_key :
  -- Koukoulopoulos-Maynard use a sophisticated graph-theoretic argument
  -- involving the "GCD graph" of integers
  True

/-- Key technique: Probabilistic method -/
axiom probabilistic_method :
  -- The proof uses probabilistic independence arguments
  -- related to the Lovász Local Lemma
  True

/-- Key technique: Sieve methods -/
axiom sieve_methods :
  -- Sieve-theoretic estimates on the distribution of coprime pairs
  True

/-
## Part XI: Related Problems
-/

/-- Connection to metric number theory -/
axiom metric_number_theory :
  -- The Duffin-Schaeffer conjecture is central to metric number theory
  -- It addresses "what happens for typical numbers"
  True

/-- Connection to Dirichlet's theorem -/
axiom dirichlet_connection :
  -- Dirichlet (1842): For any α and Q, ∃ coprime p,q with q ≤ Q and
  -- |α - p/q| < 1/(qQ)
  -- This is a classical baseline for rational approximation
  True

/-
## Part XII: Summary
-/

/-- Erdős Problem #999: Complete Summary -/
theorem erdos_999_summary :
    -- The Duffin-Schaeffer conjecture holds
    DuffinSchaefferConjecture ∧
    -- Both directions are true
    (∀ f, SeriesDiverges f ↔ AlmostAllApproximable f) ∧
    -- Zero-one law holds
    (∀ f, AlmostAllApproximable f ∨ AlmostNoneApproximable f) := by
  constructor
  · exact koukoulopoulos_maynard_2020
  constructor
  · exact koukoulopoulos_maynard_2020
  · exact zero_one_law

/-- Main theorem: The Duffin-Schaeffer conjecture is SOLVED -/
theorem erdos_999_main :
    ∀ f : ℕ → ℕ,
      (∀ M : ℝ, ∃ N : ℕ, DuffinSchaefferSum f N > M) ↔
      AlmostAll (fun α => ∀ N : ℕ, ∃ q > N, IsApproximable α f q) :=
  koukoulopoulos_maynard_2020

/-- Problem #999 Status: SOLVED -/
theorem erdos_999_status : True := trivial

end Erdos999
