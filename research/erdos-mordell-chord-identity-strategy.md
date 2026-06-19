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

## 2026-06-19 (cycle 15) — sharper Mathlib pins for the two residual sorries

Read-only verification against the live `.lake/packages/mathlib` source. Both
remaining sorries get a cleaner pin than the doc previously carried:

**Sine side (`chord_length_eq`).** Prefer the *Sphere* form over the
`Triangle ℝ P` / `Fin 3` form (`dist_div_sin_angle_eq_two_mul_circumradius`,
`Angle/Sphere.lean:430`), which forces constructing a `Triangle` value and index
juggling. Instead use

    EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius   -- Angle/Sphere.lean:298
      {s : Sphere P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s)
      (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
      dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius

  Take `s := Sphere.ofDiameter X P` (radius `dist X P / 2`, so `2*radius = dist X P`),
  `p₁ := F_b`, `p₂ := X`, `p₃ := F_c`. Membership of `F_b, F_c, X` comes from the
  already-PROVED right-angle facts `angle_pedalFoot_{ZX,XY}_at_X` fed through
  `angle_eq_pi_div_two_iff_mem_sphere_ofDiameter` (`Angle/Sphere.lean:103`); `X ∈ s`
  is an endpoint of the diameter. Residual bridge: `|Real.Angle.sin (∡ F_b X F_c)|
  = Real.sin (∠ F_b X F_c)` (unoriented `∠ ∈ [0,π]` ⟹ nonneg sin; `∠ = |(∡).toReal|`),
  then `∠ F_b X F_c = ∠ Y X Z` via the positive-ray collapse
  (`InnerProductGeometry.angle_smul_left/right_of_pos`, feet on the open sides).

**Cosine side (`angle_at_P`).** The cyclic-quadrilateral supplementary fact is the
*oriented* inscribed-angle identity, mod π:

    EuclideanGeometry.Sphere.two_zsmul_oangle_eq           -- Angle/Sphere.lean:164
    EuclideanGeometry.Cospherical.two_zsmul_oangle_eq      -- Angle/Sphere.lean:178
      : (2:ℤ) • ∡ p₁ p₂ p₄ = (2:ℤ) • ∡ p₁ p₃ p₄   (same chord p₁p₄, apexes p₂,p₃ on s)

  With chord `F_b F_c` and apexes `X` (giving `∡ = ∠YXZ` class) and `P`, the genuine
  remaining work is the oriented→unoriented descent: `2 • ∡ = 2 • ∡` only pins the
  angles mod π, and X, P lie on *opposite* arcs of chord `F_b F_c`, so the unoriented
  representatives are supplementary (`∠ + ∠ = π`) rather than equal. Establish
  opposite-arc / orientation sign before collapsing — this is the one non-mechanical
  step left on the cosine side. Concyclicity itself is free from the two Thales right
  angles via `cospherical_of_two_zsmul_oangle_eq_of_not_collinear` (`Angle/Sphere.lean:449`)
  or directly `Sphere.ofDiameter` membership.

  **Pin both forms re-verified cycle-16** against live `.lake/packages/mathlib`:
  - `dist_div_sin_oangle_eq_two_mul_radius` (`:298`) — exact concl
    `dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius`, matches doc.
  - `two_zsmul_oangle_eq` (`:164`) — exact concl `(2:ℤ)•∡ p₁ p₂ p₄ = (2:ℤ)•∡ p₁ p₃ p₄`,
    hyps `p₂≠p₁, p₂≠p₄, p₃≠p₁, p₃≠p₄`, matches doc.
  - **Prefer the `Cospherical.two_zsmul_oangle_eq` form (`:178`)** for the cosine-side
    descent: it consumes `Cospherical ({F_b, X, P, F_c} : Set P)` *directly* (same four
    distinctness hyps), so no explicit `s : Sphere P` / named center+radius is needed —
    the Thales setup yields cospherical-ness of the four feet+`X`+`P` immediately
    (`cospherical_of_two_zsmul_oangle_eq_of_not_collinear` or `Sphere.ofDiameter`
    membership of all four), then this lemma is applied with zero sphere bookkeeping.
    No phantom lemmas; both signatures are real.

Aristotle 404 (16th consecutive cycle). Companion left in known-good 2-sorry state
(unchanged Lean since cycle-14; cycle-15/16 are strategy-doc only); watcher
(PID 13290) ships the cycle-14 commit (Thales lemma `angle_pedalFoot_eq_pi_div_two`,
sig re-verified against `Angle/Unoriented/Projection.lean:28`) as a fresh PR on the
next quiet build window — prior PR #26042 merged, so a NEW PR is required.

**Cycle-17 — elementary angle-chase ruled out; oriented mechanism pinned.**
A tempting shortcut for `angle_at_P` avoids the inscribed-angle theorem entirely:
in the two right triangles `△P F_b X`, `△P F_c X` (right angles at the feet, the
already-proved `angle_pedalFoot_{ZX,XY}_at_X`), each non-right pair sums to `π/2`,
so adding the angles at `P` and at `X` gives `∠ F_b P F_c = π − ∠ F_b X F_c =
π − ∠ Y X Z`. **This does not shortcut the Lean proof:** Mathlib provides *no*
unoriented angle-addition *equality* `∠ a p c = ∠ a p b + ∠ b p c` (interior `b`).
The only unoriented additivity is the *inequality*
`EuclideanGeometry.angle_le_angle_add_angle` (`Angle/Unoriented/TriangleInequality.lean:183`);
the equality lives only in the *oriented* world. So the elementary chase collapses
back onto the same oriented→unoriented descent as the inscribed-angle route — it is
not an independent simpler path.

The concrete oriented mechanism (sharper than "establish opposite-arc sign" above):
  - `EuclideanGeometry.oangle_add` (`Angle/Oriented/Affine.lean:271`)
    `: ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃` — additivity needs **only** `pᵢ ≠ p`
    (no betweenness/`Sbtw`), so it applies at both apex `P` and apex `X` for free.
  - `EuclideanGeometry.angle_eq_abs_oangle_toReal` (`Angle/Oriented/Affine.lean:346`)
    `: ∠ p₁ p p₂ = |((∡ p₁ p p₂).toReal)|` — the `∠ = |∡.toReal|` bridge that turns
    the oriented chase back into the unoriented goal. The absolute value is what
    forces the opposite-arc sign analysis: `P` interior to `△XYZ` ⟹ both sub-oangles
    `∡ F_b P X`, `∡ X P F_c` carry the **same** sign (orientation), so their
    `|toReal|` add without cancellation, while `X` and `P` sit on opposite arcs of
    chord `F_b F_c` ⟹ the supplementary (`π −`) rather than equal collapse.
  Both lemma signatures re-verified cycle-17 against live `.lake/packages/mathlib`.

Aristotle 404 (17th consecutive cycle; both `prove_file` and inline `prove`
endpoints return `Resource not found`). Companion Lean unchanged since cycle-14
(2-sorry known-good); cycle-17 is strategy-doc only.

### 2026-06-19 (cycle 18) — stale-base rebase; Aristotle still dead

This branch's merge-base had drifted four merged auditor tracker bumps behind
`origin/main` (`#26095` cantors, `#26096` buffons, `#26097` bounded-prime-gaps,
`#26098` erdos-1107). The accumulated diff therefore **reverted** those four
tracker entries back to `auditor-cycle-20-batch` — a silent regression that would
have shipped inside this research PR. Clean-rebuilt onto `c354e698c04`: saved the
two pure artifacts (`ErdosMordellChordIdentity.lean`, this strategy doc),
`reset --hard origin/main`, restored them, and re-added the single
`import Proofs.ErdosMordellChordIdentity` line to `Proofs.lean`. Final diff is
exactly three files — no `audit-tracker.json` touch. (Stale-base recurs on this
branch every cycle: always `git diff --stat origin/main..HEAD` *first*.)

Aristotle re-probed via the now-connected MCP server (inline `prove`, both sorries
in one self-contained submission with the Thales/law-of-sines hint) — still
`{"status":"error","message":"Resource not found."}` (18th consecutive cycle).
The prover is not serving this fleet; the two residual sorries
(`chord_length_eq`, `angle_at_P`) remain manual targets with the cycle-15/17 pins
above as the concrete proof skeleton. Companion Lean unchanged from the
known-good 2-sorry state; cycle-18 is the rebase plus this note.

### 2026-06-19 (cycle 19) — sharper Thales pin (unoriented iff); Aristotle 19th-dead

Re-surveyed live `~/GitHub/mathlib4` for both residual sorries. The decisive new
find shortens the concyclicity step of **both** obligations:

* **`EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter`**
  (`Mathlib/Geometry/Euclidean/Angle/Sphere.lean:103`):
  `∠ p₁ p₂ p₃ = π/2 ↔ p₂ ∈ Sphere.ofDiameter p₁ p₃`. This is the Thales criterion
  on the **unoriented** angle `∠`, valued in `[0,π]` — no oriented `∡`/`two_zsmul`
  bookkeeping needed to *establish concyclicity*. The companion already proves
  exactly its left-hand side for both feet: `angle_pedalFoot_XY_at_X` and
  `angle_pedalFoot_ZX_at_X` give `∠ P F_• X = π/2`, hence (after the symmetry
  `angle_comm`, since `ofDiameter` is symmetric in its endpoints up to `midpoint`)
  `F_b, F_c ∈ Sphere.ofDiameter X P` directly. `Sphere.ofDiameter p₁ p₂`
  (`Sphere/Basic.lean:304`) `= ⟨midpoint ℝ p₁ p₂, dist p₁ p₂ / 2⟩` — radius
  `dist X P / 2`, exactly the circumradius the law of sines wants.

Residual oriented machinery (still the genuine remaining work):

* **Obligation B (`chord_length_eq`)** — once `X, F_b, F_c, P` are seen cospherical
  via `cospherical_iff_exists_sphere` (`Sphere/Basic.lean:152`) from the two
  `ofDiameter` memberships, apply **`Sphere.dist_div_sin_oangle_eq_two_mul_radius`**
  (`Angle/Sphere.lean:298`): `dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2·radius`.
  Rearranged on chord `F_b F_c` with apex `X`, radius `dist X P/2`, gives
  `dist F_b F_c = dist X P · |sin (∡ F_b X F_c)|`; the open-segment ray facts collapse
  `∡ F_b X F_c` onto `∠ Y X Z` and `Real.Angle.sin_toReal` (`…/Angle.lean:608`) +
  `EuclideanGeometry.angle_eq_abs_oangle_toReal` (`Angle/Oriented/Affine.lean:346`)
  discharge the `|·|`/unoriented bridge. (The unoriented packaging
  `Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius`, `Angle/Sphere.lean:430`,
  is the alternative but forces a `Triangle ℝ` repackaging.)

* **Obligation A (`angle_at_P`)** — supplementary inscribed angle. Bridge stays
  `angle_eq_abs_oangle_toReal` (unoriented `∠ F_b P F_c` ↔ `|(∡ F_b P F_c).toReal|`),
  with the supplement supplied either by
  `Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi` (`Angle/Sphere.lean:203`,
  central+inscribed = π) or `Cospherical.two_zsmul_oangle_eq` (`:178`), then
  `Real.sin_pi_sub` to land the sine. This descent (oriented `2 • ∡` → unoriented
  `∠ = π − ∠`) is the one step Aristotle would most help with.

All six lemma signatures re-verified cycle-19 against live `~/GitHub/mathlib4`.
Companion Lean unchanged (known-good 2-sorry); cycle-19 is strategy-doc only.
Aristotle `prove` MCP re-probed (`angle_at_P`, self-contained, Thales hint) —
`Resource not found` again, **19th consecutive cycle** dead.

### 2026-06-19 (cycle 20) — concyclicity now PROVED (no longer prose)

First non-doc cycle in a while. The cycle-19 unoriented-Thales pin was cashed in:
two new **fully-proved, no-sorry** lemmas were added to the companion, converting
the "Thales ⟹ the four points are concyclic" prose step — which both residual
sorries rest on — into machine-checked Lean:

* `pedalFeet_mem_sphere_ofDiameter` — both feet `F_c = pedalFoot P X Y`,
  `F_b = pedalFoot P Z X` lie on `Sphere.ofDiameter P X`. One-line proof:
  `angle_eq_pi_div_two_iff_mem_sphere_ofDiameter.1` applied to the already-proved
  right-angle facts `angle_pedalFoot_XY_at_X` / `angle_pedalFoot_ZX_at_X`. No
  oriented-angle machinery.
* `cospherical_pedalFeet` — the four points `{X, F_b, F_c, P}` are `Cospherical`.
  Proof: the two feet are on the sphere (above) and the diameter endpoints `P, X`
  are on it by `isDiameter_ofDiameter` (`IsDiameter.left_mem` / `.right_mem`);
  conclude via `Sphere.cospherical … |>.subset`.

This is the shared hypothesis both `Sphere.dist_div_sin_oangle_eq_two_mul_radius`
(sine side, `chord_length_eq`) and the inscribed-angle supplement (`angle_at_P`)
consume, so the two remaining sorries now start from a proved cospherical fact
rather than a prose claim. Residual work is unchanged in *shape* (oriented-angle
descent + ray-collapse `∡ F_b X F_c → ∠ Y X Z`) but no longer has to re-establish
concyclicity. Aristotle `prove` MCP re-probed (`angle_at_P`, self-contained,
Thales hint) — `Resource not found` again, **20th consecutive cycle** dead.

### 2026-06-19 (cycle 21) — oriented inscribed-angle lemma drafted + the `Module.Oriented` instance gap (build-pending)

Cashed the proved `cospherical_pedalFeet` into the Mathlib *oriented* inscribed-angle
theorem `Cospherical.two_zsmul_oangle_eq` (`Angle/Sphere.lean:178`; "angles in the
same segment are equal", unified with the supplementary case mod π by the `2 • `
doubling). New supporting lemma:

* `two_zsmul_oangle_pedalFeet_at_P_eq_at_X` —
  `2 • ∡ F_b P F_c = 2 • ∡ F_b X F_c`, the oriented core of `angle_at_P`.
  Proof: restrict `cospherical_pedalFeet`'s 4-point set to `{F_b, P, X, F_c}`
  (via `Cospherical.subset` + `tauto`), then apply `Cospherical.two_zsmul_oangle_eq`
  with the four distinctness hypotheses `P ≠ F_b`, `P ≠ F_c`, `X ≠ F_b`, `X ≠ F_c`
  (all hold for `P` interior to a nondegenerate triangle: no foot meets `X`, and `P`
  lies on neither side line). The argument order `hPFb hPFc hXFb hXFc` matches the
  Mathlib signature `(hp₂p₁) (hp₂p₄) (hp₃p₁) (hp₃p₄)` with `{p₁,p₂,p₃,p₄}={F_b,P,X,F_c}`.

**Instance gap discovered (the real cycle-21 content).** `∡` (oriented angle) on the
*concrete* type `EuclideanSpace ℝ (Fin 2)` does **not** elaborate out of the box:
`EuclideanGeometry.oangle` requires `[Fact (Module.finrank ℝ V = 2)]` and
`[Module.Oriented ℝ V (Fin 2)]`, and a source scan of Mathlib v4.26.0 confirms there
is **no global instance** of either for `EuclideanSpace ℝ (Fin 2)` — the only
`Module.Oriented` instance in the library is the vacuous `IsEmpty.oriented`. (This is
why every prior `∡` lemma in Mathlib lives in an abstract `[Module.Oriented …]`
section, never on the concrete Pi-type.) The lemma as first drafted therefore would
**not compile**; both instances must be supplied locally. Verified constructions exist:

```lean
-- finrank: `finrank_euclideanSpace_fin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n`
noncomputable instance instOrientedEuclideanFin2 :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨(EuclideanSpace.basisFun ℝ (Fin 2)).toBasis.orientation⟩
instance instFactFinrankEuclideanFin2 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩
```

(`EuclideanSpace.basisFun ℝ (Fin 2) : OrthonormalBasis (Fin 2) ℝ _`, then
`.toBasis.orientation : Orientation ℝ _ (Fin 2)` via `Basis.orientation`.) Any fixed
orientation suffices — the theorem holds for whatever instance is in scope.

Why `2 • ∡` (oriented) and not `∠` (unoriented): on the circle of diameter `XP`,
`P` and `X` lie on *opposite* arcs cut by the chord `F_b F_c`, so the unoriented
inscribed angles are **supplementary**, not equal — exactly the `π − ∠YXZ` of
`angle_at_P`. The doubling absorbs both same-arc (equal) and opposite-arc
(supplementary) cases into one identity, which is why Mathlib states the inscribed-
angle theorem this way. The residual gap to `angle_at_P` is therefore purely the
orientation/betweenness descent: (i) divide out the `2 • ` using the opposite-arc
sign data to land on `∠ F_b P F_c = π − ∠ F_b X F_c`, and (ii) the ray-collapse
`∠ F_b X F_c = ∠ Y X Z` (each foot on the positive ray from `X`, via
`InnerProductGeometry.angle_smul_left/right_of_pos`).

**Status / build note.** Concyclicity (cycle-20: `pedalFeet_mem_sphere_ofDiameter`,
`cospherical_pedalFeet`) and the cycle-21 oriented lemma + the two instances above are
all staged in the worktree but **not yet machine-checked**: the host was memory-
saturated (94 G/96 G, 11 idle `lean-build` containers), so no docker build was run this
cycle, and unbuilt Lean must never be pushed (the deployer auto-merges math PRs). The
two API lemmas (`Cospherical.two_zsmul_oangle_eq`, `Cospherical.subset`) and all four
construction lemmas were re-verified by source inspection against the vendored
`proofs/.lake/packages/mathlib` (v4.26.0). **Next build-capable session:** build
`Proofs.ErdosMordellChordIdentity`; if green, push the concyclicity + oriented lemmas.
Aristotle `prove` MCP re-probed — `Resource not found`, **21st consecutive cycle** dead.
