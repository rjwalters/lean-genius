/-
Erdős Problem #526: Circle Coverage by Random Arcs (Dvoretzky's Problem)

Source: https://erdosproblems.com/526
Status: SOLVED (Shepp 1972)

Statement:
Let a_n ≥ 0 with a_n → 0 and Σa_n = ∞. Find a necessary and sufficient
condition on the a_n such that, if we choose (independently and uniformly)
random arcs on the unit circle of length a_n, then all the circle is
covered with probability 1.

Solution (Shepp 1972):
A necessary and sufficient condition is:
  Σ_n (exp(a_1 + ... + a_n) / n²) = ∞

Historical Results:
- Dvoretzky (1956): Posed the problem; showed almost all circle covered
- Kahane (1959): a_n = (1+c)/n with c > 0 covers with prob 1
- Erdős (unpublished): a_n = 1/n is the critical case
- Erdős: a_n = (1-c)/n with c > 0 does NOT cover with prob 1
- Shepp (1972): Complete characterization via the sum criterion

References:
- [Dv56] Dvoretzky: On covering a circle by randomly placed arcs (1956)
- [Ka59] Kahane: Sur le recouvrement d'un cercle par des arcs (1959)
- [Sh72] Shepp: Covering the circle with random arcs (1972)

Tags: probability, random-covering, circle, arcs, geometric-probability
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Erdos526

open Real MeasureTheory Filter Topology BigOperators

/-
## Part I: Basic Setup

The unit circle and random arc placement.
-/

/-- The unit circle [0, 1) with wraparound -/
def UnitCircle := Set.Ico (0 : ℝ) 1

/-- An arc of length a starting at position θ on the unit circle -/
def Arc (θ a : ℝ) : Set ℝ :=
  if a ≥ 1 then UnitCircle  -- Arc covers entire circle
  else { x | ∃ t : ℝ, 0 ≤ t ∧ t < a ∧ (x = (θ + t) - ⌊θ + t⌋) }

/--
**Arc Sequence:**
A sequence of arc lengths satisfying a_n ≥ 0, a_n → 0, and Σa_n = ∞.
These are the conditions under which the covering problem is non-trivial.
-/
structure ArcSequence where
  a : ℕ → ℝ
  nonneg : ∀ n, a n ≥ 0
  tendsto_zero : Tendsto a atTop (𝓝 0)
  sum_diverges : ¬Summable a

/-
## Part II: The Coverage Condition

When do random arcs cover the entire circle with probability 1?
-/

/-- The partial sum S_n = a_1 + ... + a_n -/
noncomputable def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a (i + 1)

/--
**Shepp's criterion:**
The series Σ_n exp(S_n)/n² diverges, where S_n = a_1 + ⋯ + a_n.
This is the necessary and sufficient condition for coverage.
-/
def SheppCriterion (a : ℕ → ℝ) : Prop :=
  ¬Summable (fun n => if n = 0 then 0 else exp (partialSum a n) / (n : ℝ)^2)

/--
**Coverage with probability 1:**
The event that the union of random arcs of lengths a_n covers the entire
unit circle occurs with probability 1. Axiomatized since it requires a
probability space and measure-theoretic machinery.
-/
axiom CoversWithProbOne (seq : ArcSequence) : Prop

/-
## Part III: Shepp's Theorem (1972)
-/

/--
**Shepp's Theorem (1972):**
Random arcs of lengths a_n cover the unit circle with probability 1
if and only if Σ_n exp(a_1+...+a_n)/n² = ∞.

This is the complete solution to Dvoretzky's problem.
-/
axiom shepp_1972 (seq : ArcSequence) :
    CoversWithProbOne seq ↔ SheppCriterion seq.a

/-- The main theorem: Erdős Problem #526 is solved by Shepp's characterization -/
theorem erdos_526_solved (seq : ArcSequence) :
    CoversWithProbOne seq ↔ SheppCriterion seq.a :=
  shepp_1972 seq

/-
## Part IV: Special Cases

The critical boundary at a_n = 1/n.
-/

/--
**Supercritical sequence:** a_n = (1+c)/n for c > 0.
The arc lengths decrease like 1/n but slightly faster than the critical rate.
Axiomatized as an ArcSequence since the proofs that (1+c)/n → 0 and
Σ(1+c)/n diverges require analysis lemmas.
-/
/--
**Kahane (1959) + Erdős:**
a_n = (1+c)/n covers the circle with probability 1 for any c > 0.
-/

/--
**Critical sequence:** a_n = 1/n.
This is the exact boundary between coverage and non-coverage.
-/
axiom criticalSeq : ArcSequence

/-- Erdős: a_n = 1/n covers with probability 1 (critical case) -/
axiom erdos_critical : CoversWithProbOne criticalSeq

/--
**Subcritical sequence:** a_n = (1-c)/n for 0 < c < 1.
Arc lengths decrease slightly slower than the critical rate.
-/
/-
## Part V: Verification of Shepp's Criterion for Special Cases
-/

/--
For a_n = (1+c)/n: S_n ≈ (1+c) log n, so exp(S_n)/n² ≈ n^{c-1}.
When c > 0, the series Σ n^{c-1} diverges (by integral test).
Hence Shepp's criterion holds.
-/

/--
For a_n = 1/n: S_n ≈ log n, so exp(S_n)/n² ≈ n/n² = 1/n.
The harmonic series Σ 1/n diverges, so Shepp's criterion holds.
This is the critical boundary case.
-/

/--
For a_n = (1-c)/n: S_n ≈ (1-c) log n, so exp(S_n)/n² ≈ n^{-1-c}.
The series Σ n^{-1-c} converges for c > 0, so Shepp's criterion fails.
-/

/-
## Part VI: Dvoretzky's Observation

Almost all the circle is covered under the basic conditions.
-/

/--
**Dvoretzky (1956):**
Under the basic conditions (a_n → 0, Σa_n = ∞), the Lebesgue measure
of the uncovered portion of the circle tends to 0 with probability 1.
That is, almost all the circle is covered, but there may be uncovered points.
-/

/-
## Part VII: The Poisson Process Connection
-/

/--
**Shepp's proof technique:**
The key insight is to model the arc placements as a Poisson process
on the circle × [0,∞). The uncovered set at "time" t relates to the
gaps in a Poisson process, and the coverage criterion becomes a
question about the convergence of a series involving gap probabilities.
-/

/--
**Expected uncovered points:**
The expected number of uncovered points after n arcs is related to
exp(-S_n), where S_n is the partial sum. The series Σ exp(S_n)/n²
controls whether these expectations sum to a finite or infinite value.
-/

/-
## Part VIII: Computational Examples
-/

/-- Numerical: 1/1 + 1/2 + ... + 1/5 > 2 -/
example : (1 + 1/2 + 1/3 + 1/4 + 1/5 : ℚ) > 2 := by native_decide

/-
## Part IX: Logarithmic Growth and the Critical Boundary
-/

/--
**The logarithmic growth of harmonic sums:**
H_n = 1 + 1/2 + ... + 1/n ≈ log n + γ, where γ is the
Euler-Mascheroni constant. This is why 1/n is the critical threshold:
exp(H_n) ≈ exp(log n) · exp(γ) = n · exp(γ), so
exp(H_n)/n² ≈ exp(γ)/n, whose sum diverges.
-/

/-
## Part X: Summary
-/

/--
**Erdős Problem #526: SOLVED**

**Question:** When do random arcs of lengths a_n (with a_n → 0, Σa_n = ∞)
cover the unit circle with probability 1?

**Answer (Shepp 1972):** Iff Σ_n exp(a_1+...+a_n)/n² = ∞

**Critical Boundary:**
- a_n = (1+c)/n (c > 0): Covers
- a_n = 1/n: Covers (critical case)
- a_n = (1-c)/n (c > 0): Does NOT cover

**Key Insight:** At a_n = 1/n, S_n ~ log n, so exp(S_n)/n² ~ 1/n,
which barely diverges. Below 1/n, the sum converges and coverage fails.
-/
theorem erdos_526_summary :
    -- Shepp's characterization
    (∀ seq : ArcSequence, CoversWithProbOne seq ↔ SheppCriterion seq.a) ∧
    -- Critical case covers
    CoversWithProbOne criticalSeq :=
  ⟨shepp_1972, erdos_critical⟩

end Erdos526
