/-
# Erdős–Mordell (OQ-01): an elementary reduction of the chord identity

`ErdosMordellInequalityOQ01.lean` reduces the whole Erdős–Mordell inequality to a
single planar-geometry fact, the **chord identity at vertex `A`**:

    (PA · sin A)² = db² + dc² + 2 · db · dc · cos A,           (★)

where `A = ∠BAC`, `db = lineDist P C A` and `dc = lineDist P A B` are the
distances from the interior point `P` to the two sides meeting at `A`.

The strategy note `research/erdos-mordell-chord-identity-strategy.md` derives (★)
from the *inscribed-angle theorem* on the pedal circle of diameter `PA` (the
`oangle` / `two_zsmul` machinery in `Mathlib.Geometry.Euclidean.Angle.Sphere`).
That route is heavy: oriented-angle bookkeeping and a factor-of-two inscribed
angle.

This file records a strictly **more elementary route** that avoids the pedal
circle and the inscribed-angle theorem entirely, isolating its geometry-free
algebraic heart as a proved, reusable lemma.

## The elementary route

Write the vertex angle as the sum of the two *sub-angles* cut by the ray `AP`:

    α := ∠ C A P,   β := ∠ B A P,        A = ∠ B A C.

Two elementary right-triangle facts and one additivity fact reduce (★) to pure
trigonometry:

  (i)   `db = PA · sin α`  — distance from `P` to line `CA` equals
        `PA · sin(∠CAP)` (the perpendicular leg of the right triangle `A F_b P`,
        equivalently `PA · sin` of the angle between `AP` and the side);
  (ii)  `dc = PA · sin β`  — the same at the other side `AB`;
  (iii) `α + β = A`        — the ray `AP` lies between the rays `AB`, `AC`
        (true because `P` is interior to the triangle), so the two sub-angles
        add to the vertex angle.

Given (i)–(iii), identity (★) is a **trigonometric identity** in `α, β, PA`
(`chord_identity_of_half_angles` below): expand `sin(α+β)`, `cos(α+β)` and use
`sin²+cos²=1`.

## What is proved here

* `chord_identity_of_half_angles` — the geometry-free trigonometric core: from
  (i), (ii), (iii) it derives (★).  **Proved, no axioms, no sorry.**
* `lineDist_eq_dist_orthogonalProjection` — the pedal distance equals the
  distance to the orthogonal-projection foot, the bridge that turns (i)/(ii)
  into right-triangle statements.  **Proved.**

## Remaining obligations (both strictly more elementary than the inscribed angle)

* (i)/(ii): `lineDist P C A = dist P A · Real.sin (∠ C A P)`.  Route: the foot
  `F_b = orthogonalProjection (affineSpan ℝ {C, A}) P` gives a right angle
  `∠ P F_b A = π/2`; the planar law of sines
  `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`
  (`Triangle.lean:255`, alias `law_sin`) in `△ A F_b P` yields
  `dist P F_b = dist P A · sin (∠ F_b A P)`; and `F_b` collinear with `C, A`
  forces `sin (∠ F_b A P) = sin (∠ C A P)` (equal-or-supplementary).
* (iii): `∠ C A P + ∠ B A P = ∠ B A C` for `P` interior.  Route: oriented-angle
  additivity `EuclideanGeometry.oangle_add` (`Oriented/Affine.lean:271`) is
  unconditional; the interiority of `P` fixes the common sign of the three
  oriented angles (`Sbtw.oangle_sign_eq`, `Oriented/Affine.lean:720`), letting
  the unoriented sum be read off.

Neither obligation needs the circle/inscribed-angle theorem; both are
right-triangle / betweenness facts.  This is the payoff of the route.

## References
- P. Erdős, *Problem 3740*, Amer. Math. Monthly 42 (1935), 396.
- L. J. Mordell & D. F. Barrow, *Solution to 3740*, Amer. Math. Monthly 44 (1937).
-/

import Mathlib

namespace ErdosMordellOQ01Chord

open EuclideanGeometry

/-- Perpendicular distance from a point `P` to the line through two points
`X Y` (matching `ErdosMordellInequalityOQ01.lineDist`). -/
noncomputable def lineDist (P X Y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Metric.infDist P (affineSpan ℝ {X, Y})

/-- The pedal distance to the line `XY` is realised by the orthogonal-projection
foot: `lineDist P X Y = dist P (foot)`.  This is the bridge that lets the
right-triangle sine relations (obligations (i)/(ii)) speak about `lineDist`. -/
theorem lineDist_eq_dist_orthogonalProjection
    (P X Y : EuclideanSpace ℝ (Fin 2)) :
    lineDist P X Y
      = dist P (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {X, Y}) P) := by
  rw [lineDist, ← EuclideanGeometry.dist_orthogonalProjection_eq_infDist]

/-- **Geometry-free trigonometric core of the chord identity.**

Let `α = ∠CAP`, `β = ∠BAP` be the two sub-angles at the vertex `A` cut by the
ray `AP`, with `A = α + β` the vertex angle.  If the two pedal distances satisfy
the right-triangle relations `db = PA · sin α`, `dc = PA · sin β`, then the chord
identity

    (PA · sin A)² = db² + dc² + 2 · db · dc · cos A

holds.  Proof: substitute, expand `sin (α+β)`, `cos (α+β)`, and reduce with
`sin² + cos² = 1`.

This isolates the *entire* trigonometric content of the chord identity, reducing
it to the three elementary geometric inputs `db = PA·sin α`, `dc = PA·sin β`,
`A = α + β` — no inscribed-angle theorem, no pedal circle. -/
theorem chord_identity_of_half_angles
    {PA db dc α β A : ℝ}
    (hA : A = α + β)
    (hdb : db = PA * Real.sin α)
    (hdc : dc = PA * Real.sin β) :
    (PA * Real.sin A) ^ 2
      = db ^ 2 + dc ^ 2 + 2 * db * dc * Real.cos A := by
  subst hA hdb hdc
  rw [Real.sin_add, Real.cos_add]
  have hα := Real.sin_sq_add_cos_sq α
  have hβ := Real.sin_sq_add_cos_sq β
  linear_combination (PA ^ 2 * Real.sin α ^ 2) * hβ + (PA ^ 2 * Real.sin β ^ 2) * hα

end ErdosMordellOQ01Chord
