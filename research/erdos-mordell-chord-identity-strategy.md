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

The only remaining sorries are `key_inequality_A/B/C` — the obligation to supply,
for the concrete Euclidean configuration, (i) the law of sines and (ii) the chord
identity. This note records the Mathlib path for that final step.

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

## Open risk / cost

- Steps 2–3 are the heaviest: oriented-angle (`oangle`) bookkeeping and the
  `Real.Angle`/`two_zsmul` factor-of-two are fiddly; budget several build
  iterations.
- `∠ F_b P F_c = π − A` (step 4) needs the cyclic-quadrilateral angle identity;
  may be cleaner via `oangle_center_add...` than chasing unoriented angles.
- Each of `key_inequality_B/C` is the cyclic image of `A`; once `A` is done,
  `B/C` should follow by relabeling (consider a single private lemma parametrized
  by the vertex/feet, instantiated three times).

## Why not done now (inscribed-angle route)

Heavy `EuclideanSpace` geometry needs many compile iterations; deferred while the
fleet is saturated (OOM risk). The reduction + trig core + assembly are committed
and build-green; this is the documented remaining geometric obligation.

## 2026-06-19 — an *elementary* route avoiding the inscribed-angle theorem

The pedal-circle / inscribed-angle derivation above (steps 2–3) is the heaviest
part (oriented `oangle`, `two_zsmul` factor of two). It can be **avoided
entirely**. Write the vertex angle as a sum of the two sub-angles cut by `AP`:

    α := ∠ C A P,   β := ∠ B A P,   so   A = ∠ B A C = α + β   (P interior).

Then the chord identity `(PA·sinA)² = db²+dc²+2·db·dc·cosA` follows from three
elementary facts:

  (i)   `db = PA · sin α`   (perpendicular leg of right triangle `A F_b P`);
  (ii)  `dc = PA · sin β`   (same at side `AB`);
  (iii) `α + β = A`         (`AP` between rays `AB, AC`, from interiority).

Given (i)–(iii) the identity is **pure trigonometry** (expand `sin(α+β)`,
`cos(α+β)`, use `sin²+cos²=1`).

**Implemented** in `proofs/Proofs/ErdosMordellChordReduction.lean`:
- `chord_identity_of_half_angles` — the geometry-free core: (i)+(ii)+(iii) ⟹ (★).
  **Proved (`linear_combination`), no sorry.**
- `lineDist_eq_dist_orthogonalProjection` — `lineDist P X Y = dist P (foot)`,
  the bridge turning (i)/(ii) into right-triangle statements. **Proved.**

**Remaining (both strictly more elementary than the inscribed-angle theorem):**
- (i)/(ii) `lineDist P C A = dist P A · sin (∠ C A P)`: foot `F_b` gives right
  angle `∠ P F_b A = π/2`; `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`
  (`Triangle.lean:255`, `law_sin`) on `△ A F_b P` gives
  `dist P F_b = dist P A · sin (∠ F_b A P)`; `F_b ∈ line CA` collinear ⟹
  `sin (∠ F_b A P) = sin (∠ C A P)` (equal-or-supplementary, `angle_smul_left`).
- (iii) `∠ C A P + ∠ B A P = ∠ B A C`, P interior: `EuclideanGeometry.oangle_add`
  (`Oriented/Affine.lean:271`) is unconditional in oriented angles; interiority
  fixes the common sign via `Sbtw.oangle_sign_eq` (`Oriented/Affine.lean:720`),
  letting the unoriented sum be read off.

This route removes the circle entirely; what remains are right-triangle and
betweenness facts. Next session: prove (i)/(ii) via `law_sin`, then (iii).
