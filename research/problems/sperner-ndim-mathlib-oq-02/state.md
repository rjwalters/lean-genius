# Current State

**Phase**: REFINE
**Since**: 2026-05-06
**Iteration**: 16

## Current Focus

Session 16: Added boundary-edge characterization scaffolding for the
n=2 Type-1/Type-2 triangulation in a new `N2BoundaryAnalysis` section
inside `SpernerFreudSimp`. Proves the eight building-block lemmas
needed by the eventual `_hBoundaryOnFace` discharge: `t1_ne_t2`,
`diagonal_in_t{1,2}_iff`, `horizontal_in_t2_pos`, `vertical_in_t2_pos`,
`horizontal_not_in_t2_at_y0`, `vertical_not_in_t2_at_x0`, plus
`t2_face{0,1,2}_in_t1` (every t2 face shared with a t1 cell, so t2
contributes no boundary doors).

Session 15 (PR #17015, merged): added a generic `_hLowerDim` discharge
helper (`SpernerLowerDimHelper.sperner_lowerDim_card_even`) outside the
`SpernerFreudSimp` namespace, proving that for any
`Triangulation V n` + `IsSpernerColoring`, the boundary-door filter on
any face with `faceIdx.val < n` is empty (hence Even cardinality 0).

Session 14 (PR #17004, merged): added `cN2_total` total wrapper
+ `cN2_total_isSpernerColoring` lifted Sperner condition + vertex-range
bridge `topSimps2_vertex_in_range`.

Session 9: Proved `sperner_panchromatic` for n=0 (trivial) and n=1 (discrete IVT).
Companion file completely rewritten with correct proofs. FreudCell approach abandoned.

## Final Status of FreudCell Approach (Dead)

The constant-miss FreudCell triangulation is WRONG for ALL n≥2:

For n=2, N=2: 6 FreudCell cells triangulate an ANNULUS (Euler characteristic 0),
not the disk Δ² (Euler characteristic 1):
- All 6 cells: {corner, midpoint, midpoint} pattern — no center triangle DEF
- Centroid lies in MULTIPLE overlapping cells
- V(6) - E(12) + F(6) = 0 ≠ 1 (annulus, not disk)

The standard N=2 Sperner triangulation (4 triangles: ADE, BDF, CEF, DEF)
does NOT appear in FreudCell. FreudCell simply triangulates the wrong space.

## Current Proof State

### Main file (SpernerNDimMathlibOQ02.lean)
- 1 axiom (`sperner_panchromatic` for general n), 0 sorries
- Fully proved: coloring, boundary condition, compactness convergence

### Companion file (SpernerFreudenthalSimplex.lean)
- `sperner_panchromatic_zero` (n=0): PROVED, 0 sorries (S9)
- `sperner_panchromatic_one` (n=1): PROVED, 0 sorries, discrete IVT (S9)
- Type-1/Type-2 triangulation `simData2` + pseudomanifold: PROVED (S11)
- XOR parity + grid coloring + face2_path_odd + onFace infrastructure:
  PROVED (S12, S13)
- `cN2_total` wrapper + `cN2_total_isSpernerColoring`: PR #17004 merged (S14)
- `SpernerLowerDimHelper.sperner_lowerDim_card_even`: PR #17015 merged,
  generic discharge of `_hLowerDim` for any
  Sperner-on-Triangulation (S15)
- `N2BoundaryAnalysis` building blocks (S16, this session, build pending):
  `t1_ne_t2`, `diagonal_in_t{1,2}_iff`, `horizontal_in_t2_pos`,
  `vertical_in_t2_pos`, `horizontal_not_in_t2_at_y0`,
  `vertical_not_in_t2_at_x0`, `t2_face{0,1,2}_in_t1`
- `sperner_panchromatic_two` (n=2): 1 sorry remaining
- n≥3: future work

## Path Forward for n≥2 (post-S16)

`Triangulation.boundary_doors_odd` requires four hypotheses:
1. `_hSperner` — done generically by S14 wrapper (cN2_total_isSpernerColoring)
2. `_hBoundaryOnFace` — building blocks in S16; remaining work is to
   characterize `simData2.toTriangulation.adj s k = none` in terms of
   boundary conditions on `b` and to assemble the existential (~50 lines)
3. `_hLowerDim` — done generically by S15 helper
4. `_hLastFace` — TODO (~150 lines, bijection with face2_path_odd via S12)

Then apply `Triangulation.sperner` (~50 lines for diameter bound + real
coordinates). Total estimated remaining: ~250 lines across 2-3 sessions
(S16 cuts ~30 from the S15 estimate of 280).

## Gallery Status

Main entry: 1 axiom (honest, correct). Companion shows n=0,1 concretely proved.
OQ-02 question answered modulo 1 axiom (the combinatorial Sperner's lemma for n-dim grid).
