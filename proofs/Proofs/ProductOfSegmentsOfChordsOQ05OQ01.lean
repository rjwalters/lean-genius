import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Proofs.ProductOfSegmentsOfChordsOQ05

/-!
# Segment Lengths of the Chord Product: the Unsigned Power (OQ-05-OQ-01)

This file answers `product-of-segments-of-chords-oq-05-oq-01`, the first open
question raised by the parent *Power of a Point via Vieta* entry
(`ProductOfSegmentsOfChordsOQ05`):

> "External secant–secant case in named form: for `P` outside the sphere,
> package `|t₁|·|t₂| = ‖P − O‖² − r²` (the unsigned power) as a corollary,
> mirroring OQ-01's interior statement but on the exterior branch."

## From signed Vieta product to geometric segment lengths

The parent proves the **signed** identity `t₁ · t₂ = power O r P` for the two
intersection parameters of a secant line through `P` in a **unit** direction `d`.
Because `‖d‖ = 1`, the parameter `tᵢ` is the *signed* distance from `P` to the
intersection point `P + tᵢ • d`, so the **actual** (unsigned) distance is `|tᵢ|`:

`dist P (P + tᵢ • d) = |tᵢ| · ‖d‖ = |tᵢ|`.

Hence the geometric **product of the two segment lengths** is

`dist P (P + t₁ • d) · dist P (P + t₂ • d) = |t₁| · |t₂| = |t₁ · t₂| = |power O r P|`,

the **unsigned power** of the point. This is what the classical "product of
segments of chords" measures: a product of honest lengths, always nonnegative.

Splitting on the sign of the power recovers the two classical geometric
statements as named corollaries:

* `secant_secant_exterior` — for `P` strictly **outside** the sphere the product
  of the two secant segments is `‖P − O‖² − r²`.
* `intersecting_chords_interior` — for `P` strictly **inside** the sphere the
  product of the two chord segments is `r² − ‖P − O‖²`.

Both hold in an arbitrary real inner product space, so — as in the parent — the
same proof terms witness the planar circle, the 3D sphere, and the
infinite-dimensional Hilbert sphere.

0 axioms, 0 sorries.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

open ProductOfSegmentsOfChordsOQ05 (power chord_product_eq_power)

namespace ProductOfSegmentsOfChordsOQ05OQ01

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The distance from `P` to a point on the line `t ↦ P + t • d` is `|t| · ‖d‖`.**
For a unit direction this is exactly `|t|`, so the parameter `t` is the signed
distance and its absolute value is the honest segment length. -/
theorem dist_along_line (P d : E) (t : ℝ) : dist P (P + t • d) = |t| * ‖d‖ := by
  rw [dist_eq_norm]
  have hsub : P - (P + t • d) = (-t) • d := by
    rw [neg_smul]; abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg]

/-- **The unsigned chord product is the unsigned power of the point.**
If a line through `P` in unit direction `d` meets the sphere at the two distinct
parameters `t₁ ≠ t₂`, then the product of the two honest segment lengths is the
absolute value of the power of `P`:
`dist P (P + t₁ • d) · dist P (P + t₂ • d) = |power O r P|`.

This is the geometric "product of segments of chords" — a product of genuine
lengths — as opposed to the signed Vieta product `t₁ · t₂` of the parent. -/
theorem chord_segment_product_eq_abs_power (O P d : E) (r t₁ t₂ : ℝ) (hd : ‖d‖ = 1)
    (hne : t₁ ≠ t₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0) :
    dist P (P + t₁ • d) * dist P (P + t₂ • d) = |power O r P| := by
  rw [dist_along_line, dist_along_line, hd, mul_one, mul_one, ← abs_mul,
    chord_product_eq_power O P d r t₁ t₂ hd hne h₁ h₂]

/-- **Direction-independence of the unsigned segment product.**
Two secant lines through `P`, in unit directions `d` and `d'`, each meeting the
sphere at two distinct parameters, give the **same** product of segment lengths.
Both equal `|power O r P|`. -/
theorem chord_segment_product_direction_independent
    (O P d d' : E) (r t₁ t₂ s₁ s₂ : ℝ)
    (hd : ‖d‖ = 1) (hd' : ‖d'‖ = 1) (hne : t₁ ≠ t₂) (hne' : s₁ ≠ s₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0)
    (g₁ : power O r (P + s₁ • d') = 0) (g₂ : power O r (P + s₂ • d') = 0) :
    dist P (P + t₁ • d) * dist P (P + t₂ • d)
      = dist P (P + s₁ • d') * dist P (P + s₂ • d') := by
  rw [chord_segment_product_eq_abs_power O P d r t₁ t₂ hd hne h₁ h₂,
    chord_segment_product_eq_abs_power O P d' r s₁ s₂ hd' hne' g₁ g₂]

/-- **External secant–secant case (the headline of this open question).**
For `P` strictly **outside** the sphere of nonnegative radius `r`
(`r < ‖P − O‖`), the product of the two secant segment lengths is the (positive)
power of the point, with no absolute value:
`dist P (P + t₁ • d) · dist P (P + t₂ • d) = ‖P − O‖² − r²`. -/
theorem secant_secant_exterior (O P d : E) (r t₁ t₂ : ℝ) (hr : 0 ≤ r) (hd : ‖d‖ = 1)
    (hout : r < ‖P - O‖) (hne : t₁ ≠ t₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0) :
    dist P (P + t₁ • d) * dist P (P + t₂ • d) = ‖P - O‖ ^ 2 - r ^ 2 := by
  have hp : (0 : ℝ) < ‖P - O‖ ^ 2 - r ^ 2 := by nlinarith [norm_nonneg (P - O)]
  have hpow : power O r P = ‖P - O‖ ^ 2 - r ^ 2 := rfl
  rw [chord_segment_product_eq_abs_power O P d r t₁ t₂ hd hne h₁ h₂, hpow, abs_of_pos hp]

/-- **Interior intersecting-chords case.**
For `P` strictly **inside** the sphere (`‖P − O‖ < r`), the product of the two
chord segment lengths is `r² − ‖P − O‖²` — the classical intersecting-chords
theorem, on the interior branch. -/
theorem intersecting_chords_interior (O P d : E) (r t₁ t₂ : ℝ) (hd : ‖d‖ = 1)
    (hin : ‖P - O‖ < r) (hne : t₁ ≠ t₂)
    (h₁ : power O r (P + t₁ • d) = 0) (h₂ : power O r (P + t₂ • d) = 0) :
    dist P (P + t₁ • d) * dist P (P + t₂ • d) = r ^ 2 - ‖P - O‖ ^ 2 := by
  have hp : power O r P < 0 := by
    unfold power; nlinarith [norm_nonneg (P - O)]
  rw [chord_segment_product_eq_abs_power O P d r t₁ t₂ hd hne h₁ h₂, abs_of_neg hp]
  unfold power; ring

end ProductOfSegmentsOfChordsOQ05OQ01
