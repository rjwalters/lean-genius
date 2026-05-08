# Current State

**Phase**: REFINE
**Since**: 2026-05-06
**Last Updated**: 2026-05-08 (Iteration 17, researcher-12)
**Iteration**: 17

## Current Focus

Session 17 (this session): Extended the `N2BoundaryAnalysis` section
with the **base ↔ topSimps2 bridge**: 13 new lemmas converting between
arithmetic conditions on `(b, c)` and concrete edge containment in
`topSimps2 N`. Specifically:

1. **Base-membership iffs** (`t1Bases_mem_iff`, `t2Bases_mem_iff`): rewrite
   `b ∈ t{1,2}Bases N` to clean arithmetic predicates.
2. **topSimps2 membership** (`t1_in_topSimps2_of_base`,
   `t2_in_topSimps2_of_base`, `topSimps2_mem_iff`): bridge from base
   membership to top-simplex membership, including the canonical
   case-split form `s ∈ topSimps2 N ↔ (∃ b ∈ t1Bases N, t1 b = s) ∨
   (∃ b ∈ t2Bases N, t2 b = s)`.
3. **t2 → t1 base translations** (`t2Bases_self_in_t1Bases`,
   `t2Bases_right_in_t1Bases`, `t2Bases_top_in_t1Bases`): for
   `b ∈ t2Bases N`, all three "face-mate" t1 bases — `b`, `(b.1+1, b.2)`,
   `(b.1, b.2+1)` — are in `t1Bases N`. Combined with S16's
   `t2_face{0,1,2}_in_t1`, this proves all t2 faces are shared with
   another top simplex, hence **t2 cells contribute no boundary doors**.
4. **t1 → t2 base translations** (`t1Bases_horizontal_neighbor_in_t2Bases`,
   `t1Bases_vertical_neighbor_in_t2Bases`,
   `t1Bases_diagonal_neighbor_in_t2Bases`): existential side of the
   neighbor analysis for t1 cells.
5. **The missing diagonal-boundary case** (`diagonal_not_in_t2_at_diagonal`):
   counterpart to S16's `horizontal_not_in_t2_at_y0` and
   `vertical_not_in_t2_at_x0`. When `b ∈ t1Bases N` saturates the
   diagonal `b.1 + b.2 + 1 ≥ N`, no t2 cell with base in `t2Bases N`
   contains the diagonal of t1(b).
6. **Top-level diagonal classification** (`diagonal_neighbor_topSimps2`):
   the existential at topSimps2 level — the diagonal of `t1 b` is
   contained in *some other* simplex of `topSimps2 N` iff
   `b.1 + b.2 + 1 < N`, in which case that other simplex is `t2 b`.

This is exactly the form S18's `containersOf`-based assembly of
`_hBoundaryOnFace` will consume.

Session 16 (PR #17051, merged): Added boundary-edge characterization
scaffolding for the n=2 Type-1/Type-2 triangulation in a new
`N2BoundaryAnalysis` section inside `SpernerFreudSimp`. Proves the
eight building-block lemmas needed by the eventual `_hBoundaryOnFace`
discharge: `t1_ne_t2`, `diagonal_in_t{1,2}_iff`, `horizontal_in_t2_pos`,
`vertical_in_t2_pos`, `horizontal_not_in_t2_at_y0`,
`vertical_not_in_t2_at_x0`, plus `t2_face{0,1,2}_in_t1` (every t2 face
shared with a t1 cell, so t2 contributes no boundary doors).

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
- `N2BoundaryAnalysis` building blocks (S16, PR #17051 merged):
  `t1_ne_t2`, `diagonal_in_t{1,2}_iff`, `horizontal_in_t2_pos`,
  `vertical_in_t2_pos`, `horizontal_not_in_t2_at_y0`,
  `vertical_not_in_t2_at_x0`, `t2_face{0,1,2}_in_t1`
- `N2BoundaryAnalysis` base ↔ topSimps2 bridge (S17, this session,
  build pending): 13 new lemmas converting base membership to
  topSimps2 containment, plus the missing diagonal-boundary case
  `diagonal_not_in_t2_at_diagonal` and the top-level classification
  `diagonal_neighbor_topSimps2`.
- `sperner_panchromatic_two` (n=2): 1 sorry remaining
- n≥3: future work

## Path Forward for n≥2 (post-S17)

`Triangulation.boundary_doors_odd` requires four hypotheses:
1. `_hSperner` — done generically by S14 wrapper (cN2_total_isSpernerColoring)
2. `_hBoundaryOnFace` — S16 supplies edge-containment building blocks;
   S17 supplies the base ↔ topSimps2 bridge (membership iffs +
   neighbor classification). **S18 next**: walk through the abstract
   `adjFn` in `simData2.toTriangulation` to translate
   `adjFn s k = none` ↔ `containersOf (faceOf s k) = {s}` ↔ (by S17
   `topSimps2_mem_iff` case split + S16 edge lemmas) the concrete
   boundary conditions on (b, k); then assemble the existential
   `∃ faceIdx, ...` using the existing `onFaceΔ2` predicate (~80 lines).
3. `_hLowerDim` — done generically by S15 helper
4. `_hLastFace` — TODO (~120 lines, bijection with face2_path_odd via S12)

Then apply `Triangulation.sperner` (~50 lines for diameter bound + real
coordinates). Total estimated remaining: ~200 lines across 2 sessions
(S17 cuts ~30 from the post-S16 estimate of 250).

## Gallery Status

Main entry: 1 axiom (honest, correct). Companion shows n=0,1 concretely proved.
OQ-02 question answered modulo 1 axiom (the combinatorial Sperner's lemma for n-dim grid).
