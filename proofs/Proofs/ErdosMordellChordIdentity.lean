/-
# Erdős–Mordell: the pedal-feet chord identity (companion decomposition)

`ErdosMordellInequalityOQ01.lean` reduces the full Erdős–Mordell inequality to a
single geometry-bearing obligation, `chord_identity` (consumed by the per-vertex
key lemma `key_inequality_A` via the proved scalar lemma
`key_inequality_of_chord_and_sines`), which needs exactly two facts about the
concrete `EuclideanSpace ℝ (Fin 2)` configuration:

* the **law of sines**, already in Mathlib
  (`EuclideanGeometry.dist_div_sin_angle_eq_two_mul_circumradius`); and
* the **pedal-feet chord identity** `chord_identity` below.

This companion file isolates that remaining obligation as standalone, well-typed
statements in raw Mathlib primitives, so they can be attacked (or submitted to
Aristotle) independently of the clean, shipped main file. It deliberately does
**not** touch `ErdosMordellInequalityOQ01.lean` and is not registered in
`Proofs.lean`.

Structure (see `research/erdos-mordell-chord-identity-strategy.md`):

* `lineDist_eq_dist_pedalFoot` — `lineDist`↔orthogonal-projection bridge. **Proved.**
* `angle_pedalFoot_eq_pi_div_two` (+ the `…_XY_at_X` / `…_ZX_at_X` specialisations) —
  the Thales cornerstone `∠ P F W = π/2`: each pedal foot sees `XP` at a right angle.
  **Proved** from `angle_self_orthogonalProjection`; this is the shared geometric
  primitive that both remaining `sorry`s are built on.
* `chord_length_eq` — sine side: `dist F_b F_c = dist X P · sin∠YXZ` (law of sines
  on the pedal triangle). `sorry`.
* `angle_at_P` — the single residual cosine-side geometric subfact:
  `∠ F_b P F_c = π − ∠YXZ` (supplementary angle in the cyclic quadrilateral). `sorry`.
* `chord_length_sq_eq_of_angle_at_P` — cosine side **reduced to `angle_at_P`** via the
  pure law of cosines + bridge + `cos_pi_sub`. **Proved** (no `sorry`).
* `chord_length_sq_eq` — cosine side: `dist F_b F_c ² = db² + dc² + 2·db·dc·cos∠YXZ`.
  **Proved** from `angle_at_P` and the reduction above.
* `chord_identity` — geometry-free combine of the two chord lemmas. **Proved**
  modulo the two helpers.

So the original single obligation is now split into exactly **two** residual
geometric facts — the sine side `chord_length_eq` and the cosine-side
supplementary angle `angle_at_P` — each cleanly isolated and independently
attackable, joined by fully-proved algebraic reductions. NOTE: the
`orthogonalProjection`-based `pedalFoot` def and the bridge lemma both supply the
required `Nonempty ↥(affineSpan …)` instance explicitly (no global instance exists).
-/
import Mathlib

open EuclideanGeometry Metric

namespace ErdosMordellChord

/-- Perpendicular distance from `P` to the line through `X` and `Y` (matches the
`lineDist` of the main file: distance to the affine span). -/
noncomputable def lineDist (P X Y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Metric.infDist P (affineSpan ℝ {X, Y})

/-- The pedal foot: orthogonal projection of `P` onto line `XY`.

`EuclideanGeometry.orthogonalProjection` takes a `[Nonempty ↥s]` instance argument,
and there is no global `Nonempty` instance for an `affineSpan` (it is empty for `∅`),
so we supply it explicitly here from `X ∈ affineSpan ℝ {X, Y}`. -/
noncomputable def pedalFoot (P X Y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  haveI : Nonempty (↥(affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))))) :=
    ⟨⟨X, subset_affineSpan ℝ {X, Y} (by simp)⟩⟩
  (orthogonalProjection (affineSpan ℝ {X, Y}) P : EuclideanSpace ℝ (Fin 2))

/-- **Bridge lemma (step 1 of the decomposition).** The perpendicular distance to
the line `XY` equals the distance from `P` to its pedal foot. This rewrites the
`infDist`-based `lineDist` into the projection form needed to reason about the
right angles at the feet. Fully proved from
`EuclideanGeometry.dist_orthogonalProjection_eq_infDist`. -/
theorem lineDist_eq_dist_pedalFoot (P X Y : EuclideanSpace ℝ (Fin 2)) :
    lineDist P X Y = dist P (pedalFoot P X Y) := by
  haveI : Nonempty (↥(affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))))) :=
    ⟨⟨X, subset_affineSpan ℝ {X, Y} (by simp)⟩⟩
  unfold lineDist pedalFoot
  exact (dist_orthogonalProjection_eq_infDist _ _).symm

/-- **Right angle at the pedal foot (the Thales cornerstone).**

The segment from `P` to its pedal foot `F = pedalFoot P X Y` on line `XY` is
perpendicular to that line: for any point `W` lying on the line, the angle `∠ P F W`
at the foot is a right angle. This is the single geometric primitive underlying both
remaining obligations — each foot `F_b = pedalFoot P Z X`, `F_c = pedalFoot P X Y`
sees the segment `XP` at a right angle (take `W = X`, which lies on both lines `ZX`
and `XY`), so by Thales the two feet are concyclic with `X` and `P` on the circle of
diameter `XP`. From that one circle both `chord_length_eq` (law of sines) and
`angle_at_P` (inscribed/supplementary angle) follow. Fully proved from
`EuclideanGeometry.angle_self_orthogonalProjection`. -/
theorem angle_pedalFoot_eq_pi_div_two
    (P X Y W : EuclideanSpace ℝ (Fin 2))
    (hW : W ∈ affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∠ P (pedalFoot P X Y) W = Real.pi / 2 := by
  haveI : Nonempty (↥(affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))))) := ⟨⟨W, hW⟩⟩
  unfold pedalFoot
  exact angle_self_orthogonalProjection P hW

/-- Specialisation of `angle_pedalFoot_eq_pi_div_two` to the shared vertex `X`: the
foot `F_c = pedalFoot P X Y` sees `XP` at a right angle (`X` is the first generator of
its line). -/
theorem angle_pedalFoot_XY_at_X (P X Y : EuclideanSpace ℝ (Fin 2)) :
    ∠ P (pedalFoot P X Y) X = Real.pi / 2 :=
  angle_pedalFoot_eq_pi_div_two P X Y X (subset_affineSpan ℝ {X, Y} (by simp))

/-- Specialisation to the other side meeting at `X`: the foot `F_b = pedalFoot P Z X`
also sees `XP` at a right angle (`X` is the second generator of line `ZX`). Together
with `angle_pedalFoot_XY_at_X` this places `F_b`, `F_c` on the circle of diameter
`XP`. -/
theorem angle_pedalFoot_ZX_at_X (P Z X : EuclideanSpace ℝ (Fin 2)) :
    ∠ P (pedalFoot P Z X) X = Real.pi / 2 :=
  angle_pedalFoot_eq_pi_div_two P Z X X (subset_affineSpan ℝ {Z, X} (by simp))

/-- **Chord length (the "sine side", law of sines).**

The chord joining the two pedal feet has length `dist X P · sin∠YXZ`. Proof path
(see `research/erdos-mordell-chord-identity-strategy.md`, cycle-5 pin): the feet
`F_b = pedalFoot P Z X` and `F_c = pedalFoot P X Y` see segment `XP` at a right
angle, so by Thales they lie on `Sphere.ofDiameter X P` (circumradius `dist X P /2`).
The law of sines on `△(X, F_b, F_c)` then gives
`dist F_b F_c = 2·circumradius · sin(∠ F_b X F_c) = dist X P · sin(∠ F_b X F_c)`,
and `∠ F_b X F_c = ∠ Y X Z` because each foot lies on the *positive ray* from `X`
toward the adjacent vertex (interior point ⟹ foot on the open side; collapses via
`InnerProductGeometry.angle_smul_left/right_of_pos`). Mathlib:
`dist_div_sin_angle_eq_two_mul_circumradius`, `thales_theorem`,
`eq_circumcenter_of_dist_eq`. -/
theorem chord_length_eq
    (X Y Z P : EuclideanSpace ℝ (Fin 2))
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hP : P ∈ interior (convexHull ℝ {X, Y, Z})) :
    dist (pedalFoot P Z X) (pedalFoot P X Y) = dist X P * Real.sin (∠ Y X Z) := by
  sorry

/-- **The single residual geometric subfact of the cosine side.**

The angle subtended at `P` by the two pedal feet is supplementary to the
triangle's angle at `X`. Geometrically: `F_b, F_c` and `X` are concyclic with `P`
on the circle of diameter `XP` (Thales — both feet see `XP` at a right angle), and
in that cyclic quadrilateral the angle at `P` and the angle at `X` are supplementary.
This is the *only* geometric obligation remaining on the cosine side; everything
else (`chord_length_sq_eq_of_angle_at_P` below) is the algebraic law of cosines.

Isolated here as a standalone, Aristotle-submittable target. -/
theorem angle_at_P
    (X Y Z P : EuclideanSpace ℝ (Fin 2))
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hP : P ∈ interior (convexHull ℝ {X, Y, Z})) :
    ∠ (pedalFoot P Z X) P (pedalFoot P X Y) = Real.pi - ∠ Y X Z := by
  sorry

/-- **Cosine side, modulo the supplementary-angle fact (fully proved reduction).**

Given only `angle_at_P` (the supplementary-angle fact `∠ F_b P F_c = π − ∠YXZ`),
the squared chord length is `db² + dc² + 2·db·dc·cos∠YXZ`. This is the pure law of
cosines in the pedal triangle `△(F_b, P, F_c)` (apex at `P`), combined with the
bridge lemma `lineDist_eq_dist_pedalFoot` (to turn `dist P F_•` into `lineDist`) and
`Real.cos_pi_sub` (to flip the sign of the cosine). No remaining `sorry`. Mathlib:
`dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle` (law of
cosines, angle-at-point form, `dist·dist`), `Real.cos_pi_sub`. -/
theorem chord_length_sq_eq_of_angle_at_P
    (X Y Z P : EuclideanSpace ℝ (Fin 2))
    (hAngle : ∠ (pedalFoot P Z X) P (pedalFoot P X Y) = Real.pi - ∠ Y X Z) :
    dist (pedalFoot P Z X) (pedalFoot P X Y) ^ 2
      = (lineDist P Z X) ^ 2 + (lineDist P X Y) ^ 2
        + 2 * (lineDist P Z X) * (lineDist P X Y) * Real.cos (∠ Y X Z) := by
  have hlc := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (pedalFoot P Z X) P (pedalFoot P X Y)
  rw [lineDist_eq_dist_pedalFoot P Z X, lineDist_eq_dist_pedalFoot P X Y, hlc, hAngle,
    Real.cos_pi_sub, dist_comm (pedalFoot P Z X) P, dist_comm (pedalFoot P X Y) P]
  ring

/-- **Chord length squared (the "cosine side", law of cosines).**

With `db = lineDist P Z X = dist P F_b` and `dc = lineDist P X Y = dist P F_c`
(the bridge lemma `lineDist_eq_dist_pedalFoot`), the law of cosines in the pedal
triangle `△(P, F_b, F_c)` gives `dist F_b F_c ² = db² + dc² + 2·db·dc·cos∠YXZ`.
Now obtained by feeding the isolated `angle_at_P` fact into the proved reduction
`chord_length_sq_eq_of_angle_at_P` — so the only `sorry` left on the cosine side is
`angle_at_P` itself. -/
theorem chord_length_sq_eq
    (X Y Z P : EuclideanSpace ℝ (Fin 2))
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hP : P ∈ interior (convexHull ℝ {X, Y, Z})) :
    dist (pedalFoot P Z X) (pedalFoot P X Y) ^ 2
      = (lineDist P Z X) ^ 2 + (lineDist P X Y) ^ 2
        + 2 * (lineDist P Z X) * (lineDist P X Y) * Real.cos (∠ Y X Z) :=
  chord_length_sq_eq_of_angle_at_P X Y Z P (angle_at_P X Y Z P hXYZ hP)

/-- **Pedal-feet chord identity (the single remaining geometric obligation).**

For `P` interior to the nondegenerate triangle `X Y Z`, let `db = lineDist P Z X`
and `dc = lineDist P X Y` be the perpendicular distances from `P` to the two sides
meeting at `X`. Equating the two expressions for the squared chord length between
the pedal feet (`chord_length_eq` ⟹ sine side, `chord_length_sq_eq` ⟹ cosine side):

    (dist P X · sin∠YXZ)² = db² + dc² + 2·db·dc·cos∠YXZ.

This is exactly the `hchord` hypothesis of `key_inequality_of_chord_and_sines`.
Proving it discharges the last `sorry` of the Erdős–Mordell formalization. The
combine below is geometry-free: it just composes the two chord lemmas. -/
theorem chord_identity
    (X Y Z P : EuclideanSpace ℝ (Fin 2))
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hP : P ∈ interior (convexHull ℝ {X, Y, Z})) :
    (dist P X * Real.sin (∠ Y X Z)) ^ 2
      = (lineDist P Z X) ^ 2 + (lineDist P X Y) ^ 2
        + 2 * (lineDist P Z X) * (lineDist P X Y) * Real.cos (∠ Y X Z) := by
  have hlen := chord_length_eq X Y Z P hXYZ hP
  rw [dist_comm P X, ← hlen]
  exact chord_length_sq_eq X Y Z P hXYZ hP

end ErdosMordellChord
