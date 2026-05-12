# Knowledge — spherical-law-of-cosines-oq-05

## Mathematical landscape

### Haversine ≡ algebraic-half-angle restatement of SLC

The haversine formula is mathematically equivalent to the spherical
law of cosines, related by the half-angle identity
`hav(θ) = (1 − cos θ) / 2`. The conversion is pure linear arithmetic
plus the planar subtraction formula `cos(a − b) = cos a · cos b +
sin a · sin b`:

LHS:  2·hav(c)     = 1 − cos c
RHS:  2·hav(a−b) + 2·sin a · sin b · hav C
    = (1 − cos(a−b))   + sin a · sin b · (1 − cos C)
    = (1 − cos a · cos b − sin a · sin b)
        + sin a · sin b − sin a · sin b · cos C
    = 1 − cos a · cos b − sin a · sin b · cos C
    = 1 − cos c           (by SLC)

So `hav c = hav(a − b) + sin a · sin b · hav C` ↔ SLC, by linear
arithmetic in the half-angle coordinates.

### Numerical stability — the practical content

For small great-circle distance `c`, the SLC computes

  c = arccos(cos a · cos b + sin a · sin b · cos C),

where the argument is `1 − O(c²)`. In double precision (53-bit
mantissa, machine epsilon ≈ 2.2 × 10⁻¹⁶), `arccos` near `1` loses
half its relative precision per factor of `100` in `c²`. Concretely:

  c = 1 km on Earth (R = 6371 km)
  ⇒ c/R = 1.57 × 10⁻⁴ radians
  ⇒ cos(c/R) = 1 − 1.23 × 10⁻⁸
  ⇒ arccos(1 − 1.23 × 10⁻⁸) loses ~4 decimal digits
       (precision ~10⁻¹² ≪ machine epsilon · domain bound)

The haversine formula instead computes

  hav(c) = sin²(c/2) ∈ [0, 1],

which preserves full relative precision for all `c ∈ (0, π)`. Combined
with the inverse formula `c = 2 · arcsin(√hav(c))`, where `arcsin`
near `0` is well-conditioned, the entire pipeline is numerically
stable end-to-end.

## Parent gallery API

From `proofs/Proofs/SphericalLawOfCosines.lean`:

* `abbrev Vec3 := EuclideanSpace ℝ (Fin 3)` (line 42)
* `def IsUnitVec (v : Vec3) : Prop := ‖v‖ = 1` (line 45)
* `noncomputable def arcLength (u v : Vec3) : ℝ := Real.arccos ⟨u, v⟩` (line 81)
* `theorem arcLength_nonneg`, `arcLength_le_pi`, `cos_arcLength`,
  `arcLength_self`, `arcLength_comm` (lines 84–112)
* `structure SphericalTriangle` (line 120) — three unit vectors + hypotheses
* `noncomputable def SphericalTriangle.sideA/B/C` (lines 129–138)
* `theorem cos_sideA/B/C` (lines 141–153) — connect side lengths to inner products
* `noncomputable def projectPerp (v n : Vec3) : Vec3 := v - ⟨v, n⟩ • n` (line 166)
* `noncomputable def SphericalTriangle.angleC` (line 170) — `arccos`
  of cosine between perpendicular projections, fallback `0` in
  degenerate case
* `theorem inner_decomposition` (line 193) — the algebraic SLC for
  arbitrary unit vectors
* `theorem norm_projectPerp_eq_sin` (line 228) — `‖projectPerp u n‖ =
  sin (arcLength u n)` for unit vectors
* `theorem spherical_law_of_cosines_trig` (line 262) —
  `cos t.sideC = cos t.sideB · cos t.sideA + ⟨projectPerp t.A t.C,
  projectPerp t.B t.C⟩`

## Mathlib API used in S1

All in pinned `4.26.0`:

* `Real.cos_two_mul : cos (2*x) = 2 * cos x ^ 2 - 1` — for the
  half-angle identity proof.
* `Real.sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1` — companion
  for `cos_two_mul`.
* `Real.cos_sub : cos (a - b) = cos a · cos b + sin a · sin b` — for
  `haversine_formula_algebraic`.
* `Real.cos_neg : cos (-θ) = cos θ` — for `haversine_neg`.
* `Real.cos_pi : cos π = -1` — for `haversine_pi`.
* `Real.cos_zero : cos 0 = 1` — for `haversine_zero` (via `simp`).
* `Real.sin_zero : sin 0 = 0` — for `haversine_zero` (via `simp`).
* `Real.neg_one_le_cos : -1 ≤ cos x` — for `haversine_le_one`.
* `sq_nonneg : 0 ≤ x ^ 2` — for `haversine_nonneg`.

All exercised elsewhere in the gallery (e.g.
`LawOfCosinesOQ01OQ04.lean` line 73 uses `Real.cos_two_mul`).

## Mathlib gaps

* No direct `Real.sin_sq_half` or `Real.haversine` lemmas; the
  half-angle identity is derived via `cos_two_mul` + Pythagoras.
* No `Real.haversine` function in Mathlib at v4.26.0.

## S1 deliverables

* `proofs/Proofs/SphericalLawOfCosinesOQ05.lean` (new, 297 lines,
  12 thms + 1 sorry, 1 def, 0 axioms).
* `src/data/proofs/spherical-law-of-cosines-oq-05/` (new — meta.json,
  annotations.json, index.ts).
* `research/problems/spherical-law-of-cosines-oq-05/` (this dir).
* `src/data/research/problems/spherical-law-of-cosines-oq-05.json` (new).
* `proofs/Proofs.lean` — single-line import.

## Insights

* The haversine formula is algebraically equivalent to SLC; closing
  it (S2) is a pure projection-to-angle conversion question with no
  new spherical-geometric content.
* The S1 split into `haversine_formula_algebraic` (proved) +
  `haversine_formula` (sorry) cleanly factors the open content: only
  the parent's `arccos`-with-fallback `angleC` definition needs
  case analysis.
* The non-degenerate branch of `angleC` (both projections nonzero)
  coincides exactly with `sin(sideA) · sin(sideB) ≠ 0`, so the
  conversion `⟨projectPerp A C, projectPerp B C⟩ = sin · sin · cos`
  case-splits naturally on the same dichotomy.
* The Mathlib half-angle proof `Real.cos_two_mul +
  Real.sin_sq_add_cos_sq + ring` is the canonical pattern (used in
  `LawOfCosinesOQ01OQ04.lean`).

## Next steps

* **S2**: prove `haversine_formula` from `haversine_formula_algebraic`
  by case-splitting on `‖projectPerp t.A t.C‖ = 0 ∨ ‖projectPerp t.B
  t.C‖ = 0`. Use `norm_projectPerp_eq_sin` on the non-degenerate
  branch. The degenerate branch reduces to one of: `sideA ∈ {0, π}`
  ⇒ `sin sideA = 0` ⇒ cross-term vanishes ⇒ `hav sideC =
  hav(sideB ± sideA)` (case analysis via `cos sideA = ±1`).
* **S3**: numerical-stability application — explicit error bounds
  for the haversine vs `arccos` evaluation paths, possibly in the
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` namespace.
