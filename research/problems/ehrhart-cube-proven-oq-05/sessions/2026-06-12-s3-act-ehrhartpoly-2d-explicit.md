# S3 ACT — discharge `ehrhartPoly_2d_explicit` (Q1)

**Researcher**: researcher-2
**Date**: 2026-06-12
**Phase**: ACT (S3)
**Branch**: research/ehrhart-oq05-s3-ehrhartpoly-2d
**Base**: origin/main @ 84a9a65db11

## Goal

Discharge the S3 stub `ehrhartPoly_2d_explicit` — the Q1 main technical
content of OQ-05: for any `LatticePolygon` P, the Ehrhart polynomial of
its underlying `LatticePolytope 2` has the explicit closed form

    L_P(n) = A·n² + (b/2)·n + 1

where `A = P.area` and `b = P.boundaryPoints`. This is the
unconditional linear-term identity that, combined with the
already-proven conditional `picks_from_ehrhart`, yields Pick's theorem.

## What landed

### 1. `EhrhartPolynomials.lean` — `volume_eq_area` field

The Ehrhart leading-coefficient axiom `ehrhart_leading_coeff_volume`
pins `(ehrhartPoly P).leadingCoeff = P.volume`. The target identity
needs the coefficient of `n²` to be `P.area`. For a 2D lattice polytope
the normalized volume *is* the area, but the `LatticePolygon` structure
carried `volume` (inherited from `LatticePolytope 2`) and `area`
(its own field) without any link between them.

Added a definitional-bridge field, consistent with the existing
assumption-carrying fields `total_eq` / `interior_at_one`:

```lean
/-- For a 2D lattice polytope the normalized volume coincides with the
    polygon's area. ... -/
volume_eq_area : volume = area
```

Ripple check: `grep` for `LatticePolygon where` / `: LatticePolygon :=`
/ `extends LatticePolygon` across `proofs/Proofs/` returns **no concrete
instances** (only `PicksTheorem.SimpleLatticePolygon`, a distinct
structure, and the still-`sorry` S4 bridge). So adding the field breaks
nothing.

### 2. `EhrhartCubeProvenOQ05.lean` — proof

Three-point determination of the degree-2 polynomial
`p := ehrhartPoly P.toLatticePolytope`:

- `hdeg : p.natDegree = 2` from `ehrhartPoly_degree`.
- `hexp : ∀ x, p.eval x = c0 + c1·x + c2·x²` from
  `Polynomial.eval_eq_sum_range`, rewriting `natDegree → 2`, then
  `Finset.sum_range_succ` / `Finset.sum_range_zero` + `ring`.
- `hc0 : c0 = 1` from `ehrhart_constant_term` (p.eval 0 = 1) via `hexp 0`.
- `hc2 : c2 = P.area` from `ehrhart_leading_coeff_volume`
  (`unfold Polynomial.leadingCoeff`, `rw [hdeg]` → `p.coeff 2 = P.volume`)
  + `volume_eq_area`.
- `heval1 : p.eval 1 = i + b` from `ehrhartPoly_eval` + `total_eq` + `push_cast`.
- `heval_neg1 : p.eval (-1) = i` from `ehrhart_macdonald_reciprocity` (d=2):
  obtain the interior-count function `ic`, `interior_at_one` gives
  `ic 1 = P.interiorPoints`, and `interiorCount` at n=1 gives
  `(ic 1 : ℚ) = (-1)² · p.eval(-1) = p.eval(-1)`.
- `hc1 : c1 = b/2` from `hexp 1` (= i + b) and `hexp (-1)` (= i):
  subtracting, `b = 2·c1`, by `linarith`.
- Conclude `intro n; rw [hexp n, hc0, hc1, hc2]; ring`.

The two key evaluation points are `n = 1` (total lattice points, via
`total_eq`) and `n = -1` (interior count, via Macdonald reciprocity);
together with leading coefficient = area and constant term = 1 they
over-determine the degree-2 polynomial, pinning the linear term to b/2.

## Verification

```
./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ05
```

Build completed successfully (3060 jobs), exit 0. `Proofs.EhrhartPolynomials`
built (9.0s), `Proofs.EhrhartCubeProvenOQ05` built (5.4s) with only the
two expected remaining `sorry` warnings (S4 `simpleLatticePolygon_to_latticePolygon`,
S5 `picks_theorem_derived`).

## Status delta

- `EhrhartCubeProvenOQ05.lean`: 3 → 2 sorries; ~110 → 162 LOC.
- `EhrhartPolynomials.lean`: +1 structure field (`volume_eq_area`).
- Axioms: 0 new; 3 inherited Ehrhart axioms unchanged.
- Phase ACT; iteration 5 → 6.

## Next

**S4 ACT** — construct the `simpleLatticePolygon_to_latticePolygon`
bridge (must now also supply the new `volume_eq_area` field; trivial,
since a `SimpleLatticePolygon` carries `area` and the chosen `volume`
can be set equal to it). Then **S5 ACT** composes the bridge +
`ehrhartPoly_2d_explicit` (at n=1) + `picks_from_ehrhart` to derive
Pick's identity, completing the conditional Pick's theorem
(3 inherited Ehrhart axioms, 0 new axioms, 0 sorries).
