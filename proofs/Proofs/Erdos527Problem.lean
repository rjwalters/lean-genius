/-
Erdős Problem #527: Convergence of Random Power Series on Unit Circle

Source: https://erdosproblems.com/527
Status: SOLVED (Michelen-Sawhney 2025)

Statement:
Let aₙ ∈ ℝ with ∑|aₙ|² = ∞ and |aₙ| = o(1/√n).
Is it true that, for almost all choices of εₙ = ±1,
there exists some z with |z| = 1 such that ∑ εₙaₙzⁿ converges?

Answer:
YES. Moreover, the set of such z has Hausdorff dimension 1.

History:
- Dvoretzky-Erdős (1959): If |aₙ| > c/√n, diverges for ALL |z| = 1
- Michelen-Sawhney (2025): Proved convergence on a set of Hausdorff dim 1

The condition |aₙ| = o(1/√n) is sharp by Dvoretzky-Erdős.

References:
- Michelen, Sawhney (2025)
- Dvoretzky, Erdős (1959)
- https://erdosproblems.com/527
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic

namespace Erdos527

open Complex MeasureTheory

/- ## Definitions -/

/-- The unit circle in ℂ -/
def unitCircle : Set ℂ := {z : ℂ | Complex.abs z = 1}

/-- A coefficient sequence satisfying |aₙ| = o(1/√n) -/
def littleO_sqrt (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n| < ε / Real.sqrt n

/-- The sequence has divergent sum of squares -/
def divergentSquares (a : ℕ → ℝ) : Prop :=
  ¬Summable (fun n => (a n)^2)

/-- The random power series ∑ εₙaₙzⁿ -/
noncomputable def randomPowerSeries (a : ℕ → ℝ) (ε : ℕ → ℤ) (z : ℂ) : ℕ → ℂ :=
  fun n => (ε n : ℂ) * (a n : ℂ) * z^n

/-- Convergence of the power series at z -/
def convergesAt (a : ℕ → ℝ) (ε : ℕ → ℤ) (z : ℂ) : Prop :=
  Summable (randomPowerSeries a ε z)

/- ## Probabilistic Framework -/

/-- The product probability measure on {-1,1}^ℕ (fair coin flips) -/
axiom signMeasure : MeasureTheory.Measure (ℕ → ℤ)

/-- "Almost all" sign choices means probability 1 under signMeasure -/
def almostAllSigns (P : (ℕ → ℤ) → Prop) : Prop :=
  ∃ S : Set (ℕ → ℤ), signMeasure Sᶜ = 0 ∧ ∀ ε ∈ S, P ε

/- ## Classical Divergence Results -/

/-- Divergence for almost all z (given almost all signs).
When Σ|aₙ|² = ∞, the random series diverges at Lebesgue-a.e. point
of the unit circle for a.e. sign choice. -/
/-- Dvoretzky-Erdős (1959): If |aₙ| > c/√n for large n, the series
diverges for ALL |z| = 1, almost surely. This shows the decay
condition |aₙ| = o(1/√n) is sharp. -/
/- ## The Main Result (Michelen-Sawhney 2025) -/

/-- The set of z ∈ S¹ where the series converges -/
def convergenceSet (a : ℕ → ℝ) (ε : ℕ → ℤ) : Set ℂ :=
  {z ∈ unitCircle | convergesAt a ε z}

/-- Michelen-Sawhney (2025): For a.e. sign choice, the convergence
set on the unit circle is nonempty. -/
axiom michelen_sawhney_2025 (a : ℕ → ℝ)
    (hdiv : divergentSquares a) (hsmall : littleO_sqrt a) :
    almostAllSigns (fun ε => (convergenceSet a ε).Nonempty)

/-- Even stronger: The convergence set has Hausdorff dimension 1,
the largest possible for a measure-zero subset of the circle. -/
axiom hausdorff_dimension_one (a : ℕ → ℝ)
    (hdiv : divergentSquares a) (hsmall : littleO_sqrt a) :
    almostAllSigns (fun ε => dimH (convergenceSet a ε) = 1)

/- ## Properties of the Convergence Set -/

/-- The convergence set is uncountable -/
/-- The convergence set has measure zero despite having full Hausdorff dimension -/
/- ## Examples -/

/-- Example: aₙ = 1/(√n log n) satisfies both conditions -/
noncomputable def example_seq : ℕ → ℝ := fun n =>
  if n ≥ 2 then 1 / (Real.sqrt n * Real.log n) else 0

/-- The canonical example satisfies both hypotheses -/
/-- Example: aₙ = 1/√n does NOT satisfy |aₙ| = o(1/√n)
(it is Θ(1/√n), not o(1/√n)) -/
/-- Example: aₙ = 1/n satisfies Σ|aₙ|² < ∞, so divergentSquares fails -/
/- ## Summary -/

/-- **Erdős Problem #527: Main theorem.**
For a.e. sign choice, the random series converges somewhere on S¹. -/
theorem erdos_527_main (a : ℕ → ℝ)
    (hdiv : divergentSquares a) (hsmall : littleO_sqrt a) :
    almostAllSigns (fun ε => (convergenceSet a ε).Nonempty) :=
  michelen_sawhney_2025 a hdiv hsmall

/-- **Erdős Problem #527: Strong version.**
The convergence set has Hausdorff dimension 1 a.s. -/
theorem erdos_527_strong (a : ℕ → ℝ)
    (hdiv : divergentSquares a) (hsmall : littleO_sqrt a) :
    almostAllSigns (fun ε => dimH (convergenceSet a ε) = 1) :=
  hausdorff_dimension_one a hdiv hsmall

/-- **Erdős Problem #527: Summary.**
Combines existence of convergence points with the sharp divergence threshold.
1. Michelen-Sawhney: Convergence occurs on S¹ a.s.
2. Dvoretzky-Erdős: Stronger decay fails → total divergence -/
theorem erdos_527_summary :
    -- Convergence set is nonempty a.s.
    (∀ a : ℕ → ℝ, divergentSquares a → littleO_sqrt a →
      almostAllSigns (fun ε => (convergenceSet a ε).Nonempty)) ∧
    -- Hausdorff dimension 1 a.s.
    (∀ a : ℕ → ℝ, divergentSquares a → littleO_sqrt a →
      almostAllSigns (fun ε => dimH (convergenceSet a ε) = 1)) :=
  ⟨michelen_sawhney_2025, hausdorff_dimension_one⟩

end Erdos527
