/-
# Feuerbach's Theorem Defs OQ-04: Mathlib Sphere Reformulation

## The Open Question

`FeuerbachsTheoremDefs.lean` uses a custom coordinate API:
- `Point := ℝ × ℝ` (points as ordered pairs)
- `dist2 P Q = Real.sqrt ((Q.1-P.1)²+(Q.2-P.2)²)` (Euclidean distance)
- Theorems stated as `dist2 N P = r` (P lies on circle of center N, radius r)

This file **bridges** that API to Mathlib's abstract geometric types:
- `EuclideanSpace ℝ (Fin 2)` (points as ℝ²-vectors)
- `Metric.sphere center radius` (circles as metric spheres)
- `dist` (distance from Mathlib's metric space)

## What This File Proves

### Bridge Infrastructure
- `toEuclidean : Point → EuclideanSpace ℝ (Fin 2)` — embedding function
- `toEuclidean_dist` — bridge lemma: `dist (toEuclidean P) (toEuclidean Q) = dist2 P Q`

### Nine-Point Circle Membership (Mathlib Sphere Formulation)
Each of the nine points lies on `Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius`:
1. midpoint of BC (`midpoint_a`)
2. midpoint of CA (`midpoint_b`)
3. midpoint of AB (`midpoint_c`)
4. midpoint of AH (`midpoint_AH`)
5. midpoint of BH (`midpoint_BH`)
6. midpoint of CH (`midpoint_CH`)
7. foot of altitude from A (`foot_a`)
8. foot of altitude from B (`foot_b`)
9. foot of altitude from C (`foot_c`)

### Combined Theorem
`ninePoints_all_on_sphere` — all nine points lie on the Mathlib sphere simultaneously.

## Mathematical Significance

This reformulation aligns the gallery's Feuerbach formalization with Mathlib's preferred
geometry types, enabling potential Mathlib contribution. The bridge lemma shows the two
distance functions agree, making all prior results immediately available in the Mathlib
framework.

Status: 12 theorems, 0 sorries (bridge lemma + 9 membership + combined)
-/

import Mathlib
import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ04

open FeuerbachsTheorem Real EuclideanGeometry

-- ============================================================
-- PART I: Bridge Infrastructure
-- ============================================================

/-- Embed a `Point` (= ℝ × ℝ) into `EuclideanSpace ℝ (Fin 2)`.
    Maps `(x, y)` to the vector `![x, y]`. -/
def toEuclidean (P : Point) : EuclideanSpace ℝ (Fin 2) := ![P.1, P.2]

/-- **Bridge Lemma**: the Mathlib `dist` on `EuclideanSpace ℝ (Fin 2)` agrees
    with the custom `dist2` distance function.

    Proof: unfold via `EuclideanSpace.norm_eq`, split the sum over `Fin 2`,
    reduce vector components, and use `ring` for the sign symmetry
    `(P.i - Q.i)² = (Q.i - P.i)²`. -/
theorem toEuclidean_dist (P Q : Point) :
    dist (toEuclidean P) (toEuclidean Q) = dist2 P Q := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, dist2]
  congr 1
  rw [Fin.sum_univ_two]
  simp only [toEuclidean, Pi.sub_apply, Real.norm_eq_abs, sq_abs,
             Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
             Matrix.head_fin_const]
  ring

/-- Corollary: `toEuclidean P` lies in `Metric.sphere center r` iff
    `dist2 (toEuclidean⁻¹ center) P = r` (i.e., the nine-point membership
    condition is preserved by the embedding). -/
theorem mem_sphere_iff_dist2 (P C : Point) (r : ℝ) :
    toEuclidean P ∈ Metric.sphere (toEuclidean C) r ↔ dist2 C P = r := by
  simp [Metric.mem_sphere, dist_comm, toEuclidean_dist]

-- ============================================================
-- PART II: Nine-Point Circle Membership (Mathlib Sphere)
-- ============================================================

/-- The midpoint of BC lies on the Mathlib nine-point sphere. -/
theorem midpoint_a_on_sphere (T : Triangle) :
    toEuclidean T.midpoint_a ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact midpoint_a_on_ninePointCircle T

/-- The midpoint of CA lies on the Mathlib nine-point sphere. -/
theorem midpoint_b_on_sphere (T : Triangle) :
    toEuclidean T.midpoint_b ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact midpoint_b_on_ninePointCircle T

/-- The midpoint of AB lies on the Mathlib nine-point sphere. -/
theorem midpoint_c_on_sphere (T : Triangle) :
    toEuclidean T.midpoint_c ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact midpoint_c_on_ninePointCircle T

/-- The midpoint of AH lies on the Mathlib nine-point sphere. -/
theorem midpoint_AH_on_sphere (T : Triangle) :
    toEuclidean T.midpoint_AH ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact midpoint_AH_on_ninePointCircle T

/-- The midpoint of BH lies on the Mathlib nine-point sphere. -/
theorem midpoint_BH_on_sphere (T : Triangle) :
    toEuclidean T.midpoint_BH ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact midpoint_BH_on_ninePointCircle T

/-- The midpoint of CH lies on the Mathlib nine-point sphere. -/
theorem midpoint_CH_on_sphere (T : Triangle) :
    toEuclidean T.midpoint_CH ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact midpoint_CH_on_ninePointCircle T

/-- The foot of the altitude from A lies on the Mathlib nine-point sphere. -/
theorem foot_a_on_sphere (T : Triangle) :
    toEuclidean T.foot_a ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact foot_a_on_ninePointCircle T

/-- The foot of the altitude from B lies on the Mathlib nine-point sphere. -/
theorem foot_b_on_sphere (T : Triangle) :
    toEuclidean T.foot_b ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact foot_b_on_ninePointCircle T

/-- The foot of the altitude from C lies on the Mathlib nine-point sphere. -/
theorem foot_c_on_sphere (T : Triangle) :
    toEuclidean T.foot_c ∈
      Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  rw [mem_sphere_iff_dist2]
  exact foot_c_on_ninePointCircle T

-- ============================================================
-- PART III: Combined Nine-Point Circle Theorem (Mathlib)
-- ============================================================

/-- **Nine-Point Circle Theorem (Mathlib formulation)**:
    All nine special points of a triangle lie on a single Mathlib `Metric.sphere`.

    This is the abstract reformulation of `ninePoints_all_on_circle`, expressed
    using Mathlib's standard geometric types. The sphere has:
    - center: `toEuclidean T.ninePointCenter` in `EuclideanSpace ℝ (Fin 2)`
    - radius: `T.ninePointRadius = T.circumradius / 2`

    The nine points are the three side midpoints, three altitude feet, and three
    midpoints of vertex-to-orthocenter segments. -/
theorem ninePoints_all_on_sphere (T : Triangle) :
    ∀ p ∈ [toEuclidean T.midpoint_a, toEuclidean T.midpoint_b, toEuclidean T.midpoint_c,
           toEuclidean T.foot_a,     toEuclidean T.foot_b,     toEuclidean T.foot_c,
           toEuclidean T.midpoint_AH, toEuclidean T.midpoint_BH, toEuclidean T.midpoint_CH],
    p ∈ Metric.sphere (toEuclidean T.ninePointCenter) T.ninePointRadius := by
  intro p hp
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact midpoint_a_on_sphere T
  · exact midpoint_b_on_sphere T
  · exact midpoint_c_on_sphere T
  · exact foot_a_on_sphere T
  · exact foot_b_on_sphere T
  · exact foot_c_on_sphere T
  · exact midpoint_AH_on_sphere T
  · exact midpoint_BH_on_sphere T
  · exact midpoint_CH_on_sphere T

end FeuerbachsTheoremDefsOQ04

end
