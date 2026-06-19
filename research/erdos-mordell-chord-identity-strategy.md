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
   - Lemma: `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`
     (`Triangle.lean:242`; **NB** there is no lemma named `law_cos` — verified
     2026-06-19; the lemma is stated with `dist·dist`, not `^2`), plus `Real.cos_pi_sub`.

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
| law of cosines | `dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle` | `Triangle.lean:242` |

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

### 2026-06-19 (cycle 6) — chord identity split into sine/cosine helpers

The companion file `proofs/Proofs/ErdosMordellChordIdentity.lean` (previously
untracked) is now committed on branch `research/erdos-mordell-oq01-step4-pin`
(commit `819f04d`, no PR — unbuilt). The single `chord_identity` sorry is split
into two cleaner, independently attackable obligations joined by a **verified**
geometry-free combine:

| Lemma | Statement | Status |
|-------|-----------|--------|
| `lineDist_eq_dist_pedalFoot` | `lineDist P X Y = dist P (pedalFoot P X Y)` | **proved** |
| `chord_length_eq` | `dist F_b F_c = dist X P · sin∠YXZ` (law of sines on pedal △) | `sorry` |
| `chord_length_sq_eq` | `dist F_b F_c ² = db² + dc² + 2·db·dc·cos∠YXZ` (law of cosines) | `sorry` |
| `chord_identity` | combine: `rw [dist_comm, ← chord_length_eq]; exact chord_length_sq_eq` | **proved** modulo helpers |

This cleanly separates the law-of-sines machinery (Thales + circumradius + ray
angle, the step-4-pinned part) from the law-of-cosines machinery (π−A cyclic-quad
angle), so each can go to Aristotle or a focused build independently.

**Not built this cycle**: Aristotle MCP still `"Resource not found"`; fleet at
7 `lean-build` containers (load ~19), far above the OOM-safe gate (`ctrs<3`). The
two helper statements are name-checked but unverified. Next quiet-fleet session:
build the companion file (verifies the bridge lemma + combine + that the two
helper statements typecheck), then attack `chord_length_eq` / `chord_length_sq_eq`
individually (Aristotle first if it recovers).

### 2026-06-19 (cycle 7) — Mathlib pin verification (read-only)

Aristotle MCP still `"Resource not found"` (7th cycle down); fleet at 6
`lean-build` containers (load ~13), above the OOM-safe gate, so no build. Spent
the cycle verifying every pinned Mathlib lemma actually exists with the assumed
shape against `proofs/.lake/packages/mathlib`. Result — all confirmed **except
the law of cosines**:

| Pinned lemma | Status |
|--------------|--------|
| `dist_orthogonalProjection_eq_infDist` (`Projection.lean:300`) | ✓ exists |
| `dist_div_sin_angle_eq_two_mul_circumradius` (`Angle/Sphere.lean:430`) | ✓ exists (Triangle ℝ P, Fin 3) |
| `thales_theorem` (`Angle/Sphere.lean:107`, alias) | ✓ exists |
| `eq_circumcenter_of_dist_eq` (`Circumcenter.lean:261`) | ✓ exists |
| `Sphere.ofDiameter` / `isDiameter_ofDiameter` (`Sphere/Basic.lean:307`) | ✓ exists |
| `angle_smul_left_of_pos` / `angle_smul_right_of_pos` (`Angle/Unoriented/Basic.lean:140/133`) | ✓ exists |
| `Real.cos_pi_sub` (`Trigonometric/Basic.lean:331`) | ✓ exists |
| ~~`law_cos`~~ | ✗ **does not exist** → real name below |

**Correction:** there is no `EuclideanGeometry.law_cos`. The law of cosines is
`EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`
(`Triangle.lean:242`), and it is stated with `dist p₁ p₃ * dist p₁ p₃` (products),
**not** `^2`: `dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ *
dist p₃ p₂ - 2 * dist p₁ p₂ * dist p₃ p₂ * cos (∠ p₁ p₂ p₃)`. The
`chord_length_sq_eq` proof must therefore bridge `^2` ↔ `*` (e.g. `sq`/`pow_two`)
when applying it. Fixed the wrong pin in both the companion docstring and the
table above. This catch saves a guaranteed-red build cycle.

## Why not done this session (2026-06-19)

Aristotle MCP down ("Resource not found"); fleet at load ~18 with 5 lean
containers (OOM-risk per container-count gate). A heavy multi-iteration
`EuclideanSpace` build is unsafe to start now. The clean 1-sorry file is shipped
(PR #26033, OPEN+MERGEABLE). This session's progress is the de-risked,
fully name-checked decomposition above (the oangle elimination is a real
structural simplification of the remaining obligation), not a code change.

## Cosine-side reduction (2026-06-19, cycle 11)

Re-pinned everything against the live source at `~/GitHub/mathlib4`.
**Correction to the previous "does not exist" note:** `EuclideanGeometry.law_cos`
*does* exist — it is an `alias` of
`dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`
(`Triangle.lean:252`). The canonical long name is still preferred for stability,
but `law_cos` is a legal reference. The `*`-vs-`^2` caveat above stands.

The cosine side `chord_length_sq_eq` now splits cleanly into **algebra (provable)**
+ **one geometric subfact (the only residual obligation on this branch)**:

Apply the law of cosines at the pedal triangle with apex `P`, i.e.
`p₁ := pedalFoot P Z X` (=F_b), `p₂ := P`, `p₃ := pedalFoot P X Y` (=F_c):

    dist F_b F_c * dist F_b F_c
      = dist F_b P * dist F_b P + dist F_c P * dist F_c P
        − 2 * dist F_b P * dist F_c P * cos (∠ F_b P F_c).

Three rewrites turn this into the stated goal, each mechanical:
1. `^2 ↔ *` on all three squared distances (`pow_two` / `sq`);
2. `dist F_b P = lineDist P Z X` and `dist F_c P = lineDist P X Y` via the
   **proved** bridge `lineDist_eq_dist_pedalFoot` + `dist_comm`;
3. `cos (∠ F_b P F_c) = − cos (∠ Y X Z)` via `Real.cos_pi_sub`, **provided**
   the residual geometric subfact

       angle_at_P :  ∠ (pedalFoot P Z X) P (pedalFoot P X Y) = π − ∠ Y X Z.

So the whole cosine side reduces to `angle_at_P` alone (cyclic-quadrilateral angle
sum: `X F_b P F_c` is cyclic on `Sphere.ofDiameter X P` since both feet subtend a
right angle at `XP`, and opposite angles of a cyclic quadrilateral sum to π).
This is the natural next `sorry` to isolate as its own lemma and hand to Aristotle
once the backend recovers — a single, self-contained planar-angle fact with no
`infDist`/projection machinery left in it.

**Not executed in code this cycle:** Aristotle still 404 (11th consecutive cycle),
fleet at load ~20 (build gate `load<16` closed). Introducing an unverifiable
multi-step proof body would risk turning the known-buildable companion red when
the build watcher fires. The companion is left in its known-good 2-sorry state;
the watcher ships it as a typechecked PR on the next quiet window.
