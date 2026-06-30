import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Power of a Point: Intersecting Chords, Secants, and the Power Invariant

This file assembles a coordinate-free **Power of a Point** package, working in an
arbitrary real inner-product space (any dimension, via `NormedAddTorsor`), and built
on Mathlib's `EuclideanGeometry.Sphere.power` API.

For a point `P` and a sphere, the *power* of `P` is `dist P center ^ 2 - radius ^ 2`.
The central fact is that for **any** line through `P` meeting the sphere at two points
`A, B`, the product `PA · PB` equals `|power|` — in particular it is independent of the
chosen line.  This single invariant unifies several classical theorems:

* **Intersecting Chords** (Wiedijk / Freek No. 55): two chords of a circle crossing at an
  interior point `P` satisfy `PA · PB = PC · PD`.
* **Intersecting Secants**: two secants from an exterior point `P` satisfy the same.
* **Tangent–Secant**: the squared tangent length equals the secant product.
* **Equal Tangents**: the two tangent segments from an exterior point have equal length.

## Relation to the existing gallery

The gallery already contains Ptolemy's theorem (the *additive* relation
`AC·BD = AB·CD + AD·BC`, via `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`) and a
2-dimensional coordinate (`Vec2`) proof of the chord product in
`ProductOfSegmentsOfChords`.  This file is distinct on both counts: it uses the
*product / power* family of Mathlib lemmas (`mul_dist_eq_mul_dist_of_cospherical_*`,
`Sphere.mul_dist_eq_abs_power`, `Sphere.IsTangentAt.power_eq_dist_sq`), all of which were
previously **unused** anywhere in the gallery, and it works coordinate-free in any
dimension.

## Main results

* `intersecting_chords`, `intersecting_secants` — the two classical product theorems.
* `mul_dist_eq_abs_power` — the unifying invariant `PA · PB = |power P|`.
* `mul_dist_eq_mul_dist_of_mem_sphere` — line-independence of the product (derived).
* `mul_dist_eq_power_outside`, `mul_dist_eq_neg_power_inside` — signed forms.
* `tangent_sq_eq_secant_product` — the tangent–secant relation.
* `dist_tangent_eq_of_tangent` — the equal-tangents theorem (derived).
* `concrete_intersecting_chords` — a worked instance: two perpendicular diameters of the
  unit circle in `ℂ` crossing at the centre.

All results are fully verified with no axioms and no `sorry`.
-/

open scoped EuclideanGeometry RealInnerProductSpace Real
open EuclideanGeometry

namespace PowerOfPointOQ04

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-! ## The classical product theorems -/

/-- **Intersecting Chords Theorem** (Freek No. 55).  If `A, B, C, D` are cospherical and
the point `P` lies *between* `A, B` and between `C, D` (both straight angles), then the
products of the two chord segments agree. -/
theorem intersecting_chords {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P))
    (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p :=
  mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h hapb hcpd

/-- **Intersecting Secants Theorem**.  If `A, B, C, D` are cospherical and `P` lies on the
two secant lines on the *same side* (both zero angles), the products agree. -/
theorem intersecting_secants {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d)
    (hapb : ∠ a p b = 0) (hcpd : ∠ c p d = 0) :
    dist a p * dist b p = dist c p * dist d p :=
  mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero h hab hcd hapb hcpd

/-! ## The power invariant -/

/-- The **power invariant**: for any line through `P` meeting the sphere `s` at `A, B`, the
product of the segment lengths equals the absolute value of the power of `P`. -/
theorem mul_dist_eq_abs_power {s : Sphere P} {p a b : P}
    (hp : p ∈ line[ℝ, a, b]) (ha : a ∈ s) (hb : b ∈ s) :
    dist p a * dist p b = |s.power p| :=
  Sphere.mul_dist_eq_abs_power hp ha hb

/-- **Line-independence of the power of a point.**  Any two lines through `P`, each meeting
the sphere `s` in two points, yield the same product of segment lengths.  This is the
sphere-based form of the chord/secant product, derived from the power invariant applied
to each line. -/
theorem mul_dist_eq_mul_dist_of_mem_sphere {s : Sphere P} {p a b c d : P}
    (hab : p ∈ line[ℝ, a, b]) (hcd : p ∈ line[ℝ, c, d])
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) :
    dist p a * dist p b = dist p c * dist p d := by
  rw [Sphere.mul_dist_eq_abs_power hab ha hb, Sphere.mul_dist_eq_abs_power hcd hc hd]

/-- For an exterior (or boundary) point, the secant product equals the (nonnegative) power. -/
theorem mul_dist_eq_power_outside {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius) (hp : p ∈ line[ℝ, a, b]) (ha : a ∈ s) (hb : b ∈ s)
    (hle : s.radius ≤ dist p s.center) :
    dist p a * dist p b = s.power p :=
  Sphere.mul_dist_eq_power_of_radius_le_dist_center hr hp ha hb hle

/-- For an interior (or boundary) point, the chord product equals the negative of the
(nonpositive) power. -/
theorem mul_dist_eq_neg_power_inside {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius) (hp : p ∈ line[ℝ, a, b]) (ha : a ∈ s) (hb : b ∈ s)
    (hle : dist p s.center ≤ s.radius) :
    dist p a * dist p b = -s.power p :=
  Sphere.mul_dist_eq_neg_power_of_dist_center_le_radius hr hp ha hb hle

/-! ## Tangents -/

/-- **Tangent–Secant Theorem**.  The squared tangent length from `P` equals the product of
the two secant segments. -/
theorem tangent_sq_eq_secant_product {a b t p : P} {s : Sphere P}
    (ha : a ∈ s) (hb : b ∈ s) (hp : p ∈ line[ℝ, a, b])
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    dist p t ^ 2 = dist p a * dist p b :=
  Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant ha hb hp h_tangent

/-- **Equal Tangents Theorem.**  The two tangent segments drawn from a common external
point `P` to a sphere have equal length.  Both squared lengths equal the power of `P`, and
distances are nonnegative.  (Derived; this statement is not a single Mathlib lemma.) -/
theorem dist_tangent_eq_of_tangent {s : Sphere P} {t₁ t₂ p : P}
    (h₁ : s.IsTangentAt t₁ (line[ℝ, p, t₁]))
    (h₂ : s.IsTangentAt t₂ (line[ℝ, p, t₂])) :
    dist p t₁ = dist p t₂ := by
  have hsq : dist p t₁ ^ 2 = dist p t₂ ^ 2 := by
    rw [← h₁.power_eq_dist_sq, ← h₂.power_eq_dist_sq]
  exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp hsq

/-! ## A concrete witness

The unit circle in the Euclidean plane `ℂ`, with the two perpendicular diameters
`[1, -1]` and `[I, -I]` crossing at the centre `0`.  Each segment has length `1`, so both
products equal `1`. -/

/-- The four points `1, -1, I, -I` lie on the unit circle (centre `0`, radius `1`). -/
theorem cospherical_unit : Cospherical ({1, -1, Complex.I, -Complex.I} : Set ℂ) := by
  refine ⟨0, 1, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h <;> subst h <;> simp

/-- The centre `0` lies on the diameter `[1, -1]`. -/
theorem center_mem_diam_re : (0 : ℂ) ∈ line[ℝ, (1 : ℂ), -1] := by
  have h : (0 : ℂ) = AffineMap.lineMap (1 : ℂ) (-1 : ℂ) (1 / 2 : ℝ) := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    push_cast; ring
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- The centre `0` lies on the diameter `[I, -I]`. -/
theorem center_mem_diam_im : (0 : ℂ) ∈ line[ℝ, Complex.I, -Complex.I] := by
  have h : (0 : ℂ) = AffineMap.lineMap Complex.I (-Complex.I) (1 / 2 : ℝ) := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    push_cast; ring
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- **Concrete intersecting chords**: the two perpendicular diameters of the unit circle in
`ℂ` give equal products `1 · 1 = 1 · 1`. -/
theorem concrete_intersecting_chords :
    dist (1 : ℂ) 0 * dist (-1 : ℂ) 0 = dist Complex.I 0 * dist (-Complex.I) 0 :=
  mul_dist_eq_mul_dist_of_cospherical cospherical_unit center_mem_diam_re center_mem_diam_im

end PowerOfPointOQ04
