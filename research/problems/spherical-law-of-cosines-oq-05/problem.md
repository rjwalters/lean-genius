# Spherical Law of Cosines OQ-05: the Haversine Formula

## Problem statement

Formalise the **haversine formula** for a spherical triangle with arc-length
sides `a, b, c` (on the unit sphere) and dihedral angle `C` at the vertex
opposite side `c`:

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C)

where `hav(θ) := sin²(θ/2) = (1 − cos θ) / 2` is the haversine function.

## Why this matters

The haversine formula is the **numerically stable** reformulation of the
spherical law of cosines used in great-circle distance computations
(navigation, GPS, geodesy). The standard `arccos`-based formula

  c = arccos(cos a · cos b + sin a · sin b · cos C)

suffers from catastrophic cancellation when `c` is small: the argument is
close to `1`, and `arccos` loses precision drastically there. The haversine
form computes `sin²(c/2)` directly, which remains well-conditioned because
`sin` is well-behaved near `0`.

For example, at a great-circle distance of `1` kilometre on Earth (radius
≈ 6371 km), the argument of `arccos` is `1 − 1.23 × 10⁻⁸`, well beyond
the resolution of double-precision floating point near `1`. The haversine
form preserves resolution throughout the small-distance regime.

The formula was first published by James Inman in 1835 for navigation
tables; modern GPS and geographic information system libraries continue
to use it.

## Parent context

The parent gallery entry `spherical-law-of-cosines` (file
`proofs/Proofs/SphericalLawOfCosines.lean`, 341 lines, 0 sorries,
0 axioms, 24 proved theorems) establishes:

1. The structure `SphericalTriangle` with three unit-vector vertices
   `A, B, C : Vec3` and unit-norm hypotheses `hA, hB, hC`.
2. Side definitions `t.sideA, t.sideB, t.sideC` as `arcLength` (=
   `arccos` of inner product) between the appropriate vertex pairs.
3. The dihedral angle `t.angleC` defined as `arccos` of the cosine
   between the perpendicular projections `projectPerp t.A t.C` and
   `projectPerp t.B t.C`, with a fallback to `0` in the degenerate
   case where either projection has zero norm.
4. The **spherical law of cosines** in two forms:
   - `spherical_law_of_cosines_algebraic`: `⟨A, B⟩ = ⟨A, C⟩⟨B, C⟩ +
     ⟨projectPerp A C, projectPerp B C⟩` for unit vectors.
   - `spherical_law_of_cosines_trig`: the same with `cos sideC =
     cos sideB · cos sideA + ⟨projectPerp t.A t.C, projectPerp t.B t.C⟩`.
5. Key identity `norm_projectPerp_eq_sin`: `‖projectPerp u n‖ =
   sin (arcLength u n)` for unit vectors `u, n`.

## The OPEN content

The parent's `spherical_law_of_cosines_trig` uses the
*projection-inner-product* form `⟨projectPerp A C, projectPerp B C⟩`
rather than the trigonometric form `sin(a) · sin(b) · cos(C)`. The
bridge between these is

  ⟨projectPerp A C, projectPerp B C⟩
    = ‖projectPerp A C‖ · ‖projectPerp B C‖ · cos(angleC)
    = sin(sideB) · sin(sideA) · cos(angleC),

valid only when both projections are nonzero (the non-degenerate branch
of `angleC`'s definition). The degenerate branch is exactly the locus
where `sin(sideA) · sin(sideB) = 0`, so the cross-term vanishes
uniformly there.

Closing this conversion gap is the substantive content of OQ-05.

## Roadmap

* **S1 (this iteration, researcher-5)**: scaffold — define `haversine`,
  prove the half-angle identity, prove the *pure algebraic* form
  `haversine_formula_algebraic` (haversine identity from SLC as a
  real-number hypothesis), record the `SphericalTriangle` version as
  the open `sorry`.
* **S2**: discharge `haversine_formula` from
  `haversine_formula_algebraic` by case-splitting on the degenerate
  branch of `angleC` and applying `norm_projectPerp_eq_sin`.
* **S3**: navigation/GPS applications — Mercator and ECEF conversion
  lemmas, great-circle distance via haversine with explicit
  numerical-stability bounds.

## References

* Inman, J. (1835), *Navigation and Nautical Astronomy, for the use of
  British Seamen* — first published haversine tables.
* Sinnott, R. W. (1984), "Virtues of the Haversine", *Sky and
  Telescope*, vol. 68, no. 2, p. 158.
* Todhunter, I. (1886), *Spherical Trigonometry* — classical reference
  for the spherical law of cosines and its reformulations.
* https://en.wikipedia.org/wiki/Haversine_formula
