# Erdős–Mordell: closing `key_inequality_A/B/C` via the chord identity

## Status

`ErdosMordellInequalityOQ01.lean` is a complete reduction modulo one geometric
fact, isolated three ways:

- `erdos_mordell_reduction` — AM–GM assembly of the three key inequalities into
  the full Erdős–Mordell bound. **Proved.**
- `key_inequality_trig_core` — `sin B·dc + sin C·db ≤ √(db²+dc²+2·db·dc·cos A)`,
  collapsing to the perfect square `(db·cos C − dc·cos B)² ≥ 0`. **Proved.**
- `key_inequality_of_chord_and_sines` — geometry-free *assembly*: given the
  angle sum, sign conditions, the law of sines (`a=2R sinA`, …), and the **chord
  identity** `(PA·sin A)² = db² + dc² + 2·db·dc·cos A`, derives the key
  inequality `b·dc + c·db ≤ a·PA`. **Proved.**

The three cyclic `key_inequality_A/B/C` have now been **collapsed to a single
shared lemma** `key_inequality_vertex (X Y Z P)` — the others are its
`(X,Y,Z)=(A,B,C),(B,C,A),(C,A,B)` instantiations, derived by pure relabeling
(`affineIndep_rotate`, `mem_interior_hull_rotate`: affine independence and the
triangle-hull interior are invariant under cyclic permutation). So the **only**
remaining sorry is `key_inequality_vertex`: supply, for the concrete Euclidean
configuration, (i) the law of sines and (ii) the chord identity.

Update: the law of sines (i) is **already in Mathlib** —
`EuclideanGeometry.dist_div_sin_angle_eq_two_mul_circumradius`
(`Angle/Sphere.lean:430`) gives `dist /sin = 2R`. So the genuinely missing fact
is just the **chord identity** (ii). This note records the Mathlib path for it.

## The chord identity, geometrically

Let `F_b = orthogonalProjection line[C,A] P` and `F_c = orthogonalProjection
line[A,B] P` be the pedal feet; `db = dist P F_b = lineDist P C A`,
`dc = dist P F_c = lineDist P A B`. Then:

1. **Right angles at the feet.** `∠ A F_b P = ∠ A F_c P = π/2`
   (`EuclideanGeometry.angle_orthogonalProjection_...`, the projection is the
   foot of the perpendicular).
2. **Concyclicity (Thales).** Points seeing segment `AP` at a right angle lie on
   the circle of diameter `AP`. So `A, F_b, F_c, P` are concyclic.
   - Lemma: `EuclideanGeometry.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter`
     (aliased `thales_theorem`), `Mathlib/Geometry/Euclidean/Angle/Sphere.lean:103`.
3. **Chord length = `PA·sin A`.** In the circle of diameter `AP`, the chord
   `F_b F_c` subtends the inscribed angle `∠ F_b A F_c = ∠ A = A`, and the
   diameter is `PA`, so `dist F_b F_c = PA · sin A` (extended law of sines /
   inscribed-angle theorem).
   - Inscribed-angle machinery (oriented form): `two_zsmul_oangle_eq`,
     `Cospherical.two_zsmul_oangle_eq`, `oangle_eq_pi_sub_two_zsmul_oangle_center_*`
     in `Angle/Sphere.lean`. Bridge oriented→unoriented via `oangle`→`∠` and
     `Real.Angle` sin, then `EuclideanGeometry`'s diameter-chord relation.
4. **Law of cosines in `△ P F_b F_c`.** `∠ F_b P F_c = π − A` (cyclic-quad angle
   sum, since the two right angles at the feet account for the rest), so
   `dist F_b F_c ² = db² + dc² − 2·db·dc·cos(π−A) = db² + dc² + 2·db·dc·cos A`.
   - Lemma: `EuclideanGeometry.law_cos`
     (`dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`,
     `Triangle.lean:242`), plus `Real.cos_pi_sub`.

Combining 3 and 4: `(PA·sin A)² = dist F_b F_c ² = db²+dc²+2·db·dc·cos A`. ∎

## Law of sines for the configuration

Take `R` = circumradius of `△ABC` (`EuclideanGeometry.circumradius`,
`Circumcenter.lean`). Mathlib's `dist_div_sin_angle...` / extended law of sines
gives `a = 2R·sin A`, etc. (search `circumradius`, `sin_angle`, `Sphere` for the
exact name; if absent, derive from the inscribed-angle theorem applied to the
circumcircle, same machinery as step 3).

## 2026-06-19 update — de-risked, name-checked decomposition (no oangle needed)

All required Mathlib lemmas were located by source grep and the heaviest
(inscribed-angle / `oangle`) step has been **eliminated** by reusing the law of
sines on the *pedal* triangle instead of chasing inscribed angles. Confirmed
API (file:line in `proofs/.lake/packages/mathlib`):

| Need | Lemma | Location |
|------|-------|----------|
| `lineDist = dist P (foot)` | `dist_orthogonalProjection_eq_infDist` | `Geometry/Euclidean/Projection.lean:300` |
| Thales (right angle ⟺ on diameter sphere) | `thales_theorem` / `angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter` | `Angle/Sphere.lean:82,107` |
| `Sphere.ofDiameter` (center=midpoint, radius=AP/2) | `Sphere.ofDiameter` | `Sphere/Basic.lean:304` |
| circumcenter uniqueness | `eq_circumcenter_of_dist_eq` | `Circumcenter.lean:261` |
| **law of sines** (used TWICE) | `dist_div_sin_angle_eq_two_mul_circumradius` | `Angle/Sphere.lean:430` |
| law of cosines | `law_cos` | `Triangle.lean:252` |

### Key simplification: chord length without inscribed angles

Previously step 3 (`dist F_b F_c = PA·sin A`) was the riskiest — it called for
oriented-angle / `two_zsmul` factor-of-two bookkeeping. **Replace it** by the law
of sines applied to the pedal triangle `△(A, F_b, F_c)`:

1. `F_b, F_c` see `AP` at a right angle ⟹ (Thales) both lie on
   `Sphere.ofDiameter A P` (center `m = midpoint A P`, radius `dist A P / 2`).
2. `A, P` also lie on that sphere trivially. So `dist m A = dist m F_b =
   dist m F_c = dist A P / 2`. By `eq_circumcenter_of_dist_eq`, `m` is the
   circumcenter of `△(A, F_b, F_c)` and its **circumradius is `dist A P / 2`**.
3. Law of sines on `△(A, F_b, F_c)`:
   `dist F_b F_c / sin(∠ F_b A F_c) = 2 · circumradius = dist A P`,
   i.e. `dist F_b F_c = PA · sin(∠ F_b A F_c)`.
4. `∠ F_b A F_c = ∠ B A C = A` because `F_b ∈ line CA` (ray from `A` toward `C`)
   and `F_c ∈ line AB` (ray from `A` toward `B`) — the feet lie on the two sides
   meeting at `A`, so the angle subtended at `A` is the triangle's angle `A`.
   (This collinearity/ray step is the one remaining genuinely geometric fact;
   for an interior point the feet land on the open segments, so same ray.)

Then step 4 (law of cosines in `△ P F_b F_c`, `∠ F_b P F_c = π − A`) gives
`dist F_b F_c² = db² + dc² + 2·db·dc·cos A`, and combining with step 3 yields the
chord identity `(PA·sin A)² = db² + dc² + 2·db·dc·cos A` feeding
`key_inequality_of_chord_and_sines`.

Net: the proof now needs **only the same `dist_div_sin_angle_eq_two_mul_circumradius`
lemma applied twice** (once to `△ABC` for `a=2R sinA`, once to the pedal triangle
for the chord), plus Thales + circumcenter-uniqueness + law of cosines — all
confirmed present. No `oangle` / `two_zsmul` machinery.

### Remaining genuine work (build session, fleet quiet)

1. `lineDist` ↔ `orthogonalProjection` rewrite (bridge lemma, ~10 lines).
2. Right angle at the feet ⟹ membership on `Sphere.ofDiameter A P` (Thales).
3. circumradius of pedal triangle `= dist A P / 2` via `eq_circumcenter_of_dist_eq`.
4. `∠ F_b A F_c = ∠ B A C` — feet on the rays from `A` (needs interior ⟹ foot on
   the open segment; the only step still lacking a pinned-down Mathlib lemma).
5. Assemble chord identity, hand to `key_inequality_of_chord_and_sines`.
6. Affine independence of the pedal triangle (needed to form `Triangle ℝ P`):
   holds unless `db` or `dc` is zero, i.e. `P` on a side — excluded by interior.

Estimated 150–300 lines; step 4 is the residual risk. Build in a **separate
companion file first** (do not re-add sorries to the clean shipped file).

### 2026-06-19 (cycle 5) — step 4 now pinned to named lemmas

The residual-risk step 4 (`∠ F_b X F_c = ∠ Y X Z`) is no longer unpinned. The
affine angle unfolds to the vector angle
`∠ F_b X F_c = InnerProductGeometry.angle (F_b -ᵥ X) (F_c -ᵥ X)`
(`EuclideanGeometry.angle` def, `Angle/Unoriented/Affine.lean`), and the two
scaling lemmas

| Need | Lemma | Location |
|------|-------|----------|
| `angle (r•x) y = angle x y`, `r>0` | `InnerProductGeometry.angle_smul_left_of_pos`  | `Angle/Unoriented/Basic.lean:140` |
| `angle x (r•y) = angle x y`, `r>0` | `InnerProductGeometry.angle_smul_right_of_pos` | `Angle/Unoriented/Basic.lean:133` |

collapse it to a single arithmetic fact: **`F_b -ᵥ X = t · (Y -ᵥ X)` with
`t > 0`** (and `F_c -ᵥ X = s · (Z -ᵥ X)`, `s > 0`). I.e. each pedal foot lies on
the *positive ray* from `X` toward the adjacent vertex. Concretely:

1. `F_b := orthogonalProjection (affineSpan ℝ {X,Y}) P` lies on `line[X,Y]`, so
   `F_b -ᵥ X ∈ span ℝ {Y -ᵥ X}` ⟹ `F_b -ᵥ X = t · (Y -ᵥ X)` for some real `t`.
2. `t > 0`: for `P` interior to the triangle, the foot of the perpendicular to a
   side lands on the **open** segment (the side's supporting line separates the
   apex from nothing; the interior projects strictly inside). So `Sbtw ℝ X F_b Y`,
   giving `0 < t < 1`. (`Sbtw`/`Wbtw` → scalar in `(0,1)`; search
   `Wbtw`/`affineSegment`/`lineMap` for the `t`-extraction lemma.)

So the angle equality is now **fully named** modulo "foot of an interior point's
perpendicular to a side lies strictly inside that side" — an `Sbtw` membership
fact, no longer an angle mystery. This removes the last *qualitative* gap; what
remains is routine (if laborious) `EuclideanSpace`/`Sbtw` plumbing.

### 2026-06-19 (cycle 5) — why still no code

Aristotle MCP **still down** (`prove` returns `"Resource not found"`, same as
cycles 3–4). Fleet busy: **8** `lean-build` containers live (load ~22) — far
above the OOM-safe container gate (`ctrs<3`), so a heavy multi-iteration
`EuclideanSpace` build cannot be started safely. This cycle's progress is the
step-4 pin above (a genuine de-risk: the last unpinned subfact now has named
Mathlib lemmas), not a code change. The clean 1-sorry file remains shipped
(PR #26033 **merged** 07:23Z). Next quiet-fleet session: build the companion
file from this fully-named decomposition; retry Aristotle first (it may recover).

## Why not done this session (2026-06-19)

Aristotle MCP down ("Resource not found"); fleet at load ~18 with 5 lean
containers (OOM-risk per container-count gate). A heavy multi-iteration
`EuclideanSpace` build is unsafe to start now. The clean 1-sorry file is shipped
(PR #26033, OPEN+MERGEABLE). This session's progress is the de-risked,
fully name-checked decomposition above (the oangle elimination is a real
structural simplification of the remaining obligation), not a code change.
