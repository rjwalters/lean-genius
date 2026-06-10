import Proofs.EhrhartPolynomials
import Proofs.PicksTheorem

/-
# Pick's Theorem Derived from Ehrhart Polynomial Existence
# (ehrhart-cube-proven-oq-05, S2 ACT scaffold)

## What This Will Prove

The standalone `picks_theorem` axiom in `PicksTheorem.lean` is
*redundant* given the three Ehrhart axioms already declared in
`EhrhartPolynomials.lean`:

* `ehrhart_theorem`              — existence of a degree-d polynomial
                                    counting lattice points in dilations,
* `ehrhart_leading_coeff_volume` — leading coefficient = volume of P
                                    (per-polytope, pinned by `P.volume`),
* `ehrhart_macdonald_reciprocity`— interior count = (-1)^d L_P(-n).

The target identity is Pick's formula `A = i + b/2 - 1` for any
simple lattice polygon, derived purely from the three Ehrhart axioms
+ the gallery's already-proven conditional `picks_from_ehrhart`
(line 237 of `EhrhartPolynomials.lean`).

## S2 ACT Scope (this file)

This scaffold introduces three theorem stubs corresponding to stages
S3, S4, S5 of the R1 (conditional Pick's theorem via Ehrhart) route:

| Stub                                    | Future Stage | Approx. discharge |
|-----------------------------------------|--------------|------------------|
| `ehrhartPoly_2d_explicit`               | S3          | ~200 lines     |
| `simpleLatticePolygon_to_latticePolygon`| S4          | ~150 lines     |
| `picks_theorem_derived`                 | S5          | ~80 lines      |

Each stub is closed by `sorry` in this scaffold; the discharges are
the subject of later iterations.

## Status

- 3 sorries (one per stub, each marking a future stage's deliverable).
- 0 new axioms; 3 inherited Ehrhart axioms from `EhrhartPolynomials`.
- 0 new structures.

After all three stubs discharge to `0 sorries`, the deliverable is a
**conditional Pick's theorem**: 3 inherited Ehrhart axioms, no new
axioms — a meaningful axiom-dependency reduction in the gallery.

## References

- S2 PREP blueprint: `research/problems/ehrhart-cube-proven-oq-05/knowledge.md`
  §"Lean Skeleton Sketch for S2".
- AXIOM-FIX (PR #22648, merged 2026-06-09): added the
  `LatticePolytope.volume`, `LatticePolytope.volume_pos`, and
  `LatticePolygon.interior_at_one` fields that the discharges in
  S3-S5 will rely on.
-/

namespace EhrhartCubeProvenOQ05

open EhrhartPolynomials Polynomial

/-- **Q1 / S3 target**: the Ehrhart polynomial of a 2D lattice polygon
has the explicit closed form `A·n² + (b/2)·n + 1`, where `A = P.area`
and `b = P.boundaryPoints`.

The S3 discharge will:
1. Use `ehrhart_leading_coeff_volume` to pin the leading coefficient
   to `P.area` (after identifying `P.volume = P.area` for 2D polygons).
2. Use `ehrhart_constant_term` (already proved) for the constant term `1`.
3. Use `ehrhart_macdonald_reciprocity` at `n = -1` together with
   `P.interior_at_one` to extract the linear coefficient as `b/2`,
   via the 4-line algebraic argument in knowledge.md §"The Q1 Polynomial
   Identity". -/
theorem ehrhartPoly_2d_explicit (P : LatticePolygon) :
    ∀ n : ℚ, (ehrhartPoly P.toLatticePolytope).eval n =
      P.area * n ^ 2 + (P.boundaryPoints : ℚ) / 2 * n + 1 := by
  sorry

/-- **Q2 / S4 target**: every `PicksTheorem.SimpleLatticePolygon`
arises from a `LatticePolygon`. The bridge identifies the two
parallel polygon structures.

`SimpleLatticePolygon` carries `(interior_count, boundary_count, area)`;
`LatticePolygon` carries the same data plus the underlying
`LatticePolytope 2` (lattice point count function, volume, ...).

The S4 discharge will construct the underlying counting function via
the existential supplied by `ehrhart_theorem` and verify the structure
laws (`nonempty`, `count_zero`, `total_eq`, `interior_at_one`) from
the corresponding Ehrhart axioms. -/
noncomputable def simpleLatticePolygon_to_latticePolygon
    (P : PicksTheorem.SimpleLatticePolygon) : LatticePolygon :=
  sorry

/-- **Q2 close / S5 target**: Pick's formula `A = i + b/2 - 1` for
any simple lattice polygon, derived from the three Ehrhart axioms.

The S5 discharge will:
1. Apply `simpleLatticePolygon_to_latticePolygon` to obtain the
   companion `LatticePolygon`.
2. Apply `ehrhartPoly_2d_explicit` at `n = 1` to obtain
   `L_P(1) = A + b/2 + 1`.
3. Combine with `LatticePolygon.total_eq` (`L_P(1) = i + b`) and the
   conditional `picks_from_ehrhart` (line 237 of `EhrhartPolynomials.lean`)
   to conclude `A = i + b/2 - 1`. -/
theorem picks_theorem_derived (P : PicksTheorem.SimpleLatticePolygon) :
    P.area = (P.interior_count : ℚ) + (P.boundary_count : ℚ) / 2 - 1 := by
  sorry

end EhrhartCubeProvenOQ05
