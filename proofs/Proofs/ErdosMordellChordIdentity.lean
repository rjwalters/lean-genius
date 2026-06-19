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
* `pedalFoot_eq` — the foundational coordinate bridge `pedalFoot P X Y =
  (⟪P−X,Y−X⟫/‖Y−X‖²)•(Y−X) + X`, rewriting the abstract projection into the explicit
  `F = X + (p/a)•u` form both residual identities are stated in. `sorry` (complete
  named-lemma proof recipe in its docstring; `coe_orthogonalProjection_eq_iff_mem`).
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

**Cycle-35 sharpening (researcher-9), numerically confirmed (acute/obtuse,
interior/exterior P).** Reducing both residual facts to coordinates
(`a=‖u‖², b=‖v‖², c=⟪u,v⟫, p=⟪w,u⟫, q=⟪w,v⟫, r=‖w‖²` with `u=Y-X, v=Z-X, w=P-X`,
projections `F_b=X+(q/b)•v`, `F_c=X+(p/a)•u`) shows precisely how the difficulty
splits:

* `chord_length_eq` (sine side) is, after squaring, a **HYPOTHESIS-FREE** pure
  `ring` identity in the six coordinates — the 2D Gram determinant
  `r·(a·b−c²) = a·q² + b·p² − 2·c·p·q` (three vectors in dim 2 are dependent). It
  needs neither `hXYZ` nor `hP`. → fully mechanizable.
* `angle_at_P` (cosine side) ⇔ the scalar identity `db·dc·cos∠YXZ = −⟪P−F_b,P−F_c⟫`,
  whose **square** is again hypothesis-free `ring`, leaving the **sign as the SOLE
  place `hP` is used in the whole Erdős–Mordell proof** (it fails for exterior `P`).

So Erdős–Mordell is now `ring`-mechanical except for one scalar sign that the
interior hypothesis must supply.
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

/-- **Explicit coordinate form of the pedal foot — the foundational bridge
(cycle-37, researcher-9).**

The orthogonal projection of `P` onto line `XY` is `X` displaced along `Y − X` by
the scalar `⟪P−X, Y−X⟫ / ‖Y−X‖²`:

    pedalFoot P X Y = (⟪P−X, Y−X⟫ / ‖Y−X‖²) • (Y − X) + X.

This is the **single concrete bridge** that turns the abstract,
`orthogonalProjection`-based `pedalFoot` into the six-coordinate form
`F_c = X + (p/a)•u` (`u = Y−X`, `p = ⟪P−X,Y−X⟫`, `a = ‖u‖²`) on which *both*
residual `ring` identities `chord_length_eq` and `angle_at_P` are phrased — once
`pedalFoot P Z X` and `pedalFoot P X Y` are rewritten by this lemma, every remaining
obligation is a polynomial identity in the `Fin 2` components of `u, v, w`, closable
by `ring` (sine side, hypothesis-free) or `ring` + the sign `(♦)` (cosine side).

**PROOF RECIPE (fully grounded; drop in when the build/Aristotle gate opens).**
Apply the affine projection's characteristic property
`EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem`
(`orthogonalProjection s p = q ↔ q ∈ s ∧ p −ᵥ q ∈ s.directionᗮ`) with
`q = (⟪P−X,Y−X⟫/‖Y−X‖²)•(Y−X) + X =: t•(Y−X) + X`. Two goals:

* **Membership** `t•(Y−X) + X ∈ affineSpan ℝ {X, Y}`: by
  `AffineSubspace.vadd_mem_of_mem_direction` with base `X ∈ s` and
  `t•(Y−X) ∈ s.direction`; the direction is `ℝ ∙ (X − Y)` via
  `direction_affineSpan` + `vectorSpan_pair`, and `t•(Y−X) = (−t)•(X−Y) ∈ ℝ∙(X−Y)`
  (`Submodule.mem_span_singleton`).
* **Perpendicular residual** `P −ᵥ (t•(Y−X)+X) ∈ s.directionᗮ`: rewrite the direction
  as `ℝ ∙ (X − Y)` and use
  `Submodule.mem_orthogonal_singleton_iff_inner_left` to reduce to
  `⟪(P−X) − t•(Y−X), X − Y⟫ = 0`. Expand with `inner_sub_left`, `inner_smul_left`,
  `inner_neg_right`, `real_inner_self_eq_norm_sq`:
  `⟪P−X, X−Y⟫ − t·⟪Y−X, X−Y⟫ = −⟪P−X,Y−X⟫ + t·‖Y−X‖² = 0`
  since `t·‖Y−X‖² = ⟪P−X,Y−X⟫` (`field_simp` with `‖Y−X‖² ≠ 0` from `hY`).

The hypothesis `Y ≠ X` keeps the line a genuine 1-space (so `‖Y−X‖² ≠ 0`); for the
two feet of an interior point both side directions are nonzero (from `hXYZ`). -/
theorem pedalFoot_eq (P X Y : EuclideanSpace ℝ (Fin 2)) (hY : Y ≠ X) :
    pedalFoot P X Y
      = (inner ℝ (P - X) (Y - X) / ‖Y - X‖ ^ 2) • (Y - X) + X := by
  haveI : Nonempty (↥(affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))))) :=
    ⟨⟨X, subset_affineSpan ℝ {X, Y} (by simp)⟩⟩
  have hu : ‖Y - X‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hY))
  set t : ℝ := inner ℝ (P - X) (Y - X) / ‖Y - X‖ ^ 2 with ht
  unfold pedalFoot
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨?_, ?_⟩
  · -- membership: `t • (Y - X) + X ∈ affineSpan ℝ {X, Y}`
    have hX : X ∈ affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))) :=
      subset_affineSpan ℝ {X, Y} (by simp)
    have hdir : t • (Y - X) ∈
        (affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2)))).direction := by
      rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_span_singleton]
      exact ⟨-t, by rw [vsub_eq_sub]; module⟩
    have h := AffineSubspace.vadd_mem_of_mem_direction hdir hX
    simpa using h
  · -- perpendicular residual: `P −ᵥ (t • (Y - X) + X) ∈ directionᗮ`
    rw [direction_affineSpan, vectorSpan_pair, mem_orthogonal_singleton_iff_inner_left]
    have key : (P -ᵥ (t • (Y - X) + X) : EuclideanSpace ℝ (Fin 2))
        = (P - X) - t • (Y - X) := by
      rw [vsub_eq_sub]; abel
    rw [key, vsub_eq_sub, inner_sub_left, real_inner_smul_left]
    have hXY : (X - Y : EuclideanSpace ℝ (Fin 2)) = -(Y - X) := by abel
    rw [hXY, inner_neg_right, inner_neg_right, real_inner_self_eq_norm_sq, ht]
    field_simp
    ring

/-- **Chord length (the "sine side", law of sines).**

The chord joining the two pedal feet has length `dist X P · sin∠YXZ`.

**COORDINATE ROUTE (cycle-35, researcher-9 — preferred; HYPOTHESIS-FREE).**
This identity is, after squaring, a *pure algebraic identity* in the six real
coordinates of `u = Y - X`, `v = Z - X`, `w = P - X` — it needs **neither** `hXYZ`
**nor** `hP` (numerically confirmed for arbitrary `P`, incl. exterior and obtuse;
only `X ≠ Y`, `X ≠ Z` enter, to keep the projections defined). Writing
`a = ‖u‖², b = ‖v‖², c = ⟪u,v⟫, p = ⟪w,u⟫, q = ⟪w,v⟫, r = ‖w‖²`, the projections
are `F_b = X + (q/b)•v`, `F_c = X + (p/a)•u`, so

    dist F_b F_c ² = q²/b + p²/a − 2·p·q·c/(a·b)             (direct expansion)
    (dist X P · sin∠YXZ)² = r·(a·b − c²)/(a·b)               (sin² = 1 − cos², cos = c/√(ab))

and these are equal because the **3×3 Gram determinant of `u, v, w` vanishes** (three
vectors in a 2-dimensional space are linearly dependent):

    r·(a·b − c²) = a·q² + b·p² − 2·c·p·q.

In components (`Fin 2`, two reals each) this Gram relation is a one-line `ring`
identity. The unsquared equality then follows since both sides are `≥ 0`
(`Real.sin ∠ ≥ 0` on `[0,π]`, `dist ≥ 0`) via `Real.sqrt_inj` / `pow_left_injective`.

**SYNTHETIC ROUTE (alternative).** The feet `F_b, F_c` see segment `XP` at a right
angle, so by Thales they lie on `Sphere.ofDiameter X P` (circumradius `dist X P /2`);
law of sines on `△(X, F_b, F_c)` gives `dist F_b F_c = dist X P · sin(∠ F_b X F_c)`,
and `∠ F_b X F_c = ∠ Y X Z` via positive-ray collapse
(`InnerProductGeometry.angle_smul_left/right_of_pos`). Mathlib:
`dist_div_sin_angle_eq_two_mul_circumradius`, `thales_theorem`. -/
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

**WHERE `hP` ENTERS — the whole proof's only sign (cycle-35, researcher-9).**
By the inner-product definition of `EuclideanGeometry.angle`, this statement is
equivalent to the scalar identity

    (lineDist P Z X)·(lineDist P X Y)·cos∠YXZ = −⟪P − F_b, P − F_c⟫            (★)

(`db·dc·cos = −⟨P−F_b,P−F_c⟩`). The **square** of (★) is hypothesis-free pure
algebra: with the notation of `chord_length_eq`, `db²·dc² = (r−q²/b)(r−p²/a)`,
`cos² = c²/(a·b)`, and `⟪P−F_b,P−F_c⟫ = r − p²/a − q²/b + p·q·c/(a·b)`, and one
checks `(db·dc·cos)² = ⟪P−F_b,P−F_c⟫²` by `ring` in coordinates. The **sign** of (★)
is the *only* place the interior hypothesis `hP` is used in the entire Erdős–Mordell
formalization: `db, dc ≥ 0`, so `sign(db·dc·cos) = sign(cos) = sign ⟪u,v⟫`, and (★)
demands `sign(−⟪P−F_b,P−F_c⟫) = sign ⟪u,v⟫`. This sign FAILS for exterior `P`
(numerically confirmed), so it genuinely requires `hP`.

**The sign as a SINGLE ring identity (cycle-36, researcher-9).** Write `u = Y−X`,
`v = Z−X`, `w = P−X` and let `[a,b] := a₀b₁ − a₁b₀` be the 2D cross product. The
perpendicular feet components are exactly `P − F_c = ([u,w]/‖u‖²)·rot90 u` and
`P − F_b = ([v,w]/‖v‖²)·rot90 v` (pure `ring` in `Fin 2` coords, since `rot90 u ⟂ u`
and `⟪rot90 u, rot90 v⟫ = ⟪u,v⟫`). Hence
`⟪P−F_b,P−F_c⟫ = [u,w]·[v,w]·⟪u,v⟫ / (‖u‖²‖v‖²)` while
`db·dc·cos∠YXZ = |[u,w]|·|[v,w]|·⟪u,v⟫ / (‖u‖²‖v‖²)`, so (★) ⇔
`|[u,w]·[v,w]| = −[u,w]·[v,w]`, i.e. **`[u,w]·[v,w] ≤ 0`** — the two cross products
have opposite signs. Feeding `hP`'s barycentric witness `w = s·u + t·v`, `s,t > 0`,
`s+t < 1` collapses this to the one-line identity

    [u,w]·[v,w] = −s·t·[u,v]²                                                    (♦)

(`[u,u]=[v,v]=0`, `[u,v]=−[v,u]`), manifestly `< 0` for `s,t>0` and nondegenerate
`[u,v]≠0` (from `hXYZ`). **So the cosine side's entire dependence on `hP` is the
ring identity (♦) plus `s,t>0`** — Erdős–Mordell is now `ring`-mechanical end to end.
Both (♦) and the squared identity are numerically confirmed to ~1e-14.

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
