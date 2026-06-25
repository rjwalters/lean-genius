import Mathlib

/-
# Buffon's Needle / Noodle — Additivity of Expected Crossings over Concatenation
  (OQ-01-OQ-01-OQ-01-OQ-02)

## Lineage

This is an open-question descendant of `BuffonsNeedleOQ01OQ01OQ01.lean`
("Axiom-Free Smooth Noodle via Concrete Integration"), which proves the
Buffon–Barbier formula for an arbitrary C¹ curve γ : ℝ → ℝ × ℝ on [a, b]:

  concreteSmoothExpectedCrossings γ a b d = 2 · arcLength(γ) / (π · d),

where the *concrete* expected-crossing functional is the double integral

  concreteSmoothExpectedCrossings γ a b d
    = (1/(π·d)) · ∫_a^b ∫_0^π |γ'ₓ(t)·sin θ + γ'_y(t)·cos θ| dθ dt.

The parent development established the *value* of this functional. What it
never recorded is the structural property that makes Barbier's argument work
in the first place: the functional is **additive over concatenation of the
parameter interval**. A noodle traversed from a to b, split at an interior
point c, has expected crossings equal to the sum of the expected crossings of
its two halves. Iterating, a curve partitioned into n pieces has expected
crossings equal to the sum over the pieces.

This is the formal "a noodle is a sum of needles" decomposition: combined with
the parent's shape-independence result it gives an independent route to
Barbier's constant 2/(π·d).

## What is proved here (self-contained, Mathlib-only)

We reproduce the *concrete* functional definition verbatim (so this file is
faithful to the parent without importing it — keeping the file Mathlib-only),
then prove, with **0 axioms and 0 sorries**:

* `expectedCrossings_self`     : empty parameter interval ⇒ 0 crossings.
* `expectedCrossings_additive` : additivity across one interior split point.
* `expectedCrossings_additive_of_continuous`
                               : the same, with the integrability side
                                 conditions discharged for curves with a
                                 continuous angular integrand.
* `expectedCrossings_additive3`: additivity across two interior split points.
* `expectedCrossings_partition`: additivity over an arbitrary n-piece partition
                                 `pts m, pts (m+1), …, pts n` of the parameter
                                 interval (the general "noodle = Σ needles").

## Honest scope

Mathematically these are direct consequences of additivity of the *outer*
interval integral (`intervalIntegral.integral_add_adjacent_intervals` and
`intervalIntegral.sum_integral_adjacent_intervals_Ico`); the inner angular
integral and the constant 1/(π·d) are inert. The contribution is not a deep
theorem — it is the missing *structural lemma* of the Buffon family, stated and
proved for the exact functional the family uses, with the precise integrability
hypotheses made explicit.

Adapted from erdosproblems.com lineage (Apache 2.0 License).
-/

open Real intervalIntegral MeasureTheory

namespace BuffonsNeedleConcatenation

/-- The inner *angular* integrand at parameter `t`:
    `∫_0^π |γ'ₓ(t)·sin θ + γ'_y(t)·cos θ| dθ`.

    This is the per-point contribution to the expected number of crossings;
    it depends only on the velocity `γ'(t)`. -/
noncomputable def angularIntegrand (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π,
    |(deriv (Prod.fst ∘ γ) t) * Real.sin θ + (deriv (Prod.snd ∘ γ) t) * Real.cos θ|

/-- Expected number of crossings of a C¹ curve `γ` on the parameter interval
    `[a, b]` with a unit grid of lines at spacing `d`.

    This is **definitionally** `BuffonsNeedleOQ01OQ01.concreteSmoothExpectedCrossings`
    (same double integral, same order), re-stated here so the file depends only
    on Mathlib. -/
noncomputable def expectedCrossings (γ : ℝ → ℝ × ℝ) (a b d : ℝ) : ℝ :=
  (1 / (π * d)) * ∫ t in a..b, angularIntegrand γ t

/-- A degenerate (empty) parameter interval contributes no crossings. -/
@[simp]
theorem expectedCrossings_self (γ : ℝ → ℝ × ℝ) (a d : ℝ) :
    expectedCrossings γ a a d = 0 := by
  simp only [expectedCrossings, integral_same, mul_zero]

/-- **Additivity across one split point.** For an interior parameter value `c`,
    the expected crossings over `[a, b]` equal those over `[a, c]` plus those
    over `[c, b]`, provided the angular integrand is interval-integrable on each
    piece. (No ordering of `a, c, b` is required — interval integrals handle
    orientation.) -/
theorem expectedCrossings_additive (γ : ℝ → ℝ × ℝ) (a c b d : ℝ)
    (hac : IntervalIntegrable (angularIntegrand γ) volume a c)
    (hcb : IntervalIntegrable (angularIntegrand γ) volume c b) :
    expectedCrossings γ a b d
      = expectedCrossings γ a c d + expectedCrossings γ c b d := by
  simp only [expectedCrossings]
  rw [← mul_add, integral_add_adjacent_intervals hac hcb]

/-- Additivity across one split point, with the integrability hypotheses
    discharged from continuity of the angular integrand (which holds, e.g., for
    `C¹` curves with continuous velocity). -/
theorem expectedCrossings_additive_of_continuous (γ : ℝ → ℝ × ℝ) (a c b d : ℝ)
    (hcont : Continuous (angularIntegrand γ)) :
    expectedCrossings γ a b d
      = expectedCrossings γ a c d + expectedCrossings γ c b d :=
  expectedCrossings_additive γ a c b d
    (hcont.intervalIntegrable a c) (hcont.intervalIntegrable c b)

/-- **Additivity across two split points** `c₁, c₂` (a three-piece noodle). -/
theorem expectedCrossings_additive3 (γ : ℝ → ℝ × ℝ) (a c₁ c₂ b d : ℝ)
    (h1 : IntervalIntegrable (angularIntegrand γ) volume a c₁)
    (h2 : IntervalIntegrable (angularIntegrand γ) volume c₁ c₂)
    (h3 : IntervalIntegrable (angularIntegrand γ) volume c₂ b) :
    expectedCrossings γ a b d
      = expectedCrossings γ a c₁ d + expectedCrossings γ c₁ c₂ d
        + expectedCrossings γ c₂ b d := by
  rw [expectedCrossings_additive γ a c₁ b d h1 (h2.trans h3),
      expectedCrossings_additive γ c₁ c₂ b d h2 h3]
  ring

/-- **General partition additivity** ("noodle = Σ needles"). For a chain of
    parameter points `pts m ≤ … ≤ pts n` (given as values of a sequence
    `pts : ℕ → ℝ`), the expected crossings of the curve over the whole interval
    `[pts m, pts n]` equal the sum of the expected crossings over the `n - m`
    consecutive pieces, provided the angular integrand is interval-integrable on
    each piece. -/
theorem expectedCrossings_partition (γ : ℝ → ℝ × ℝ) (d : ℝ) (pts : ℕ → ℝ)
    (m n : ℕ) (hmn : m ≤ n)
    (hint : ∀ k ∈ Finset.Ico m n,
      IntervalIntegrable (angularIntegrand γ) volume (pts k) (pts (k + 1))) :
    expectedCrossings γ (pts m) (pts n) d
      = ∑ k ∈ Finset.Ico m n, expectedCrossings γ (pts k) (pts (k + 1)) d := by
  simp only [expectedCrossings]
  rw [← sum_integral_adjacent_intervals_Ico hmn hint, Finset.mul_sum]

end BuffonsNeedleConcatenation
