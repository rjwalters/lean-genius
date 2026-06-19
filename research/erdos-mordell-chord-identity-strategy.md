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

## Open risk / cost

- Steps 2–3 are the heaviest: oriented-angle (`oangle`) bookkeeping and the
  `Real.Angle`/`two_zsmul` factor-of-two are fiddly; budget several build
  iterations.
- `∠ F_b P F_c = π − A` (step 4) needs the cyclic-quadrilateral angle identity;
  may be cleaner via `oangle_center_add...` than chasing unoriented angles.
- Each of `key_inequality_B/C` is the cyclic image of `A`; once `A` is done,
  `B/C` should follow by relabeling (consider a single private lemma parametrized
  by the vertex/feet, instantiated three times).

## Why not done now

Heavy `EuclideanSpace` geometry needs many compile iterations; deferred while the
fleet is saturated (OOM risk). The reduction + trig core + assembly are committed
and build-green; this is the documented remaining geometric obligation.
