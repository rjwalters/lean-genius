/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): the **area** of the cyclotomic
level set, squeezed between two concentric discs.

Parent: `Proofs.Erdos1215Problem` asks whether, for polynomials `P` with all roots on
the unit circle, there is a bounded-level path from `0` to `∞` inside
`{z : |P(z)| < C}`.  OQ-02 restricts to the *cyclotomic* polynomials `Φ_n`.

The companion `CyclotomicPolynomialsOQ02OQ02` pinned the level set
`{z : |Φ_n(z)| < C}` between two concentric balls about the origin:

      closedBall(0, r)  ⊆  {|Φ_n| < C}  ⊆  closedBall(0, 1 + C^{1/φ(n)}),
                                          whenever `0 ≤ r` and `(r + 1)^{φ(n)} < C`.

This entry pushes that geometric sandwich through the Lebesgue measure on `ℂ ≅ ℝ²`,
turning the two-sided *containment* into a two-sided *area* estimate.  Using
`Complex.volume_closedBall` (`volume (closedBall a ρ) = ENNReal.ofReal ρ ^ 2 · π`)
and monotonicity of measure, we get, for `0 ≤ r` and `(r + 1)^{φ(n)} < C`,

      π · r²  ≤  area {|Φ_n| < C}  ≤  π · (1 + C^{1/φ(n)})².

In particular the cyclotomic level set has **finite area** — a purely
measure-theoretic strengthening of researcher-4's qualitative boundedness result.
This is the "area between two balls" follow-up requested in `state.md`, and it is the
antithesis of a Mac Lane labyrinth: not only is the region bounded, its planar
Lebesgue measure is controlled by an explicit, degree-uniform disc area that shrinks
towards `π · 2² = 4π` as `φ(n) → ∞` (for fixed `C > 1`).

Main results:
* `volume_levelSet_le`        : `area {|Φ_n| < C} ≤ π · (1 + C^{1/φ(n)})²`.
* `volume_levelSet_lt_top`    : the cyclotomic level set has finite area.
* `le_volume_levelSet`        : `π · r² ≤ area {|Φ_n| < C}` for `(r+1)^{φ(n)} < C`.
* `volume_levelSet_sandwich`  : both bounds together, the disc-area squeeze.

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ01
import Proofs.CyclotomicPolynomialsOQ02OQ02

open Complex Polynomial MeasureTheory

namespace CyclotomicPolynomialsOQ02OQ03

/-- **Outer area bound.**
The planar Lebesgue measure of the cyclotomic level set `{|Φ_n| < C}` is at most the
area `π · (1 + C^{1/φ(n)})²` of the sharp outer disc from
`CyclotomicPolynomialsOQ02OQ02.sublevel_subset_closedBall_sharp`. -/
theorem volume_levelSet_le (n : ℕ) (hn : n ≠ 0) (C : ℝ) :
    volume (Erdos1215.levelSet (cyclotomic n ℂ) C) ≤
      ENNReal.ofReal (1 + C ^ ((n.totient : ℝ)⁻¹)) ^ 2 * NNReal.pi := by
  calc volume (Erdos1215.levelSet (cyclotomic n ℂ) C)
      ≤ volume (Metric.closedBall (0 : ℂ) (1 + C ^ ((n.totient : ℝ)⁻¹))) :=
        measure_mono (CyclotomicPolynomialsOQ02OQ02.sublevel_subset_closedBall_sharp n hn C)
    _ = ENNReal.ofReal (1 + C ^ ((n.totient : ℝ)⁻¹)) ^ 2 * NNReal.pi :=
        Complex.volume_closedBall _ _

/-- **Finite area.**
The cyclotomic level set `{|Φ_n| < C}` has finite planar Lebesgue measure.  This is a
measure-theoretic strengthening of the qualitative boundedness proved in
`CyclotomicPolynomialsOQ02OQ01`: not only is the region contained in a ball, its area
is a genuine (finite) real number. -/
theorem volume_levelSet_lt_top (n : ℕ) (hn : n ≠ 0) (C : ℝ) :
    volume (Erdos1215.levelSet (cyclotomic n ℂ) C) < ⊤ := by
  refine lt_of_le_of_lt (volume_levelSet_le n hn C) ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.coe_lt_top

/-- **Inner area bound.**
For any radius `r ≥ 0` with `(r + 1)^{φ(n)} < C`, the area `π · r²` of the inner disc
of `CyclotomicPolynomialsOQ02OQ02.closedBall_subset_levelSet_cyclotomic` is a lower
bound for the area of the cyclotomic level set. -/
theorem le_volume_levelSet (n : ℕ) (hn : n ≠ 0) (C r : ℝ) (hr0 : 0 ≤ r)
    (hr : (r + 1) ^ n.totient < C) :
    ENNReal.ofReal r ^ 2 * NNReal.pi ≤
      volume (Erdos1215.levelSet (cyclotomic n ℂ) C) := by
  calc ENNReal.ofReal r ^ 2 * NNReal.pi
      = volume (Metric.closedBall (0 : ℂ) r) := (Complex.volume_closedBall _ _).symm
    _ ≤ volume (Erdos1215.levelSet (cyclotomic n ℂ) C) :=
        measure_mono
          (CyclotomicPolynomialsOQ02OQ02.closedBall_subset_levelSet_cyclotomic n hn C r hr0 hr)

/-- **The disc-area squeeze.**
Combining the inner and outer bounds: for `0 ≤ r` with `(r + 1)^{φ(n)} < C`, the area
of the cyclotomic level set `{|Φ_n| < C}` is trapped between the two disc areas

      π · r²  ≤  area {|Φ_n| < C}  ≤  π · (1 + C^{1/φ(n)})².

This is the measure-theoretic form of the two-sided ball containment of
`CyclotomicPolynomialsOQ02OQ02`. -/
theorem volume_levelSet_sandwich (n : ℕ) (hn : n ≠ 0) (C r : ℝ) (hr0 : 0 ≤ r)
    (hr : (r + 1) ^ n.totient < C) :
    ENNReal.ofReal r ^ 2 * NNReal.pi ≤ volume (Erdos1215.levelSet (cyclotomic n ℂ) C) ∧
      volume (Erdos1215.levelSet (cyclotomic n ℂ) C) ≤
        ENNReal.ofReal (1 + C ^ ((n.totient : ℝ)⁻¹)) ^ 2 * NNReal.pi :=
  ⟨le_volume_levelSet n hn C r hr0 hr, volume_levelSet_le n hn C⟩

end CyclotomicPolynomialsOQ02OQ03
