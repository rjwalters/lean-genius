# Current State

**Phase**: REFINE
**Since**: 2026-05-06
**Last Updated**: 2026-05-08 (Iteration 19, researcher-5)
**Iteration**: 19

## Current Focus

Session 19 (this session, build pending): Added 3 new generic
`private` lemmas in a new `S19AdjBridge` section (appended after
`end SpernerFreudSimp`) that translate the abstract
`D.toTriangulation.adj ⟨s, hs⟩ k = none` hypothesis of
`Triangulation.boundary_doors_odd` to the concrete
container-cardinality condition built up in S16-S18:

1. `adjFn_eq_none_iff_card_le_one`: pure dite-unfolding —
   `D.adjFn ⟨s, hs⟩ k = none ↔ (D.containersOf (D.faceOf s hs k)).card ≤ 1`.
   Holds for any `AbstractSimplicialData V n` (no pseudomanifold
   needed). Three-branch dispatch through the nested `dite` of
   `adjFn`: boundary branch trivial; interior happy-path
   contradicts `none`; the would-be third branch (card > 1, but
   `cs.erase s` empty) is impossible because `s ∈ containers`.
2. `adjFn_eq_none_iff_card_eq_one`: pseudomanifold-strengthened
   form. Combines (1) with `Finset.card_pos.mpr ⟨s, self_mem_containersOf⟩`
   to upgrade `card ≤ 1` to `card = 1`.
3. `toTriangulation_adj_eq_none_iff`: same restated for
   `D.toTriangulation.adj` (definitionally equal to `D.adjFn`,
   so the proof is by direct application of (2)).

This is the **last abstract bridge piece** before S20 can wire
the S16/S17/S18.1/S18.2 building-block table into the existential
`∃ faceIdx, ∀ j ≠ k, onFaceΔ2 (vertex s j) faceIdx` required by
`_hBoundaryOnFace`. The S20 case-split now reads:

```
intro s k h_adj
rw [toTriangulation_adj_eq_none_iff] at h_adj
-- h_adj : (containers (faceOf s k)).card = 1
obtain ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩ := topSimps2_mem_iff.mp s.2
-- t1 b case: containers card = 1 ↔ boundary edge (S18.1)
-- t2 c case: containers card ≥ 2 (S18.2 t2-share, PR #17150) → False
```

Session 18 part 2 (PR #17149, merged): Added 5 new `private`
existential lemmas in a new `N2BoundaryInteriorNeighbors`
section (appended after `end SpernerFreudSimp`) that
complement S18 part 1 (PR #17133, merged) by covering the
**interior** side of `_hBoundaryOnFace`:

1. `horizontal_neighbor_topSimps2`: for `b ∈ t1Bases N` with
   `b.2 ≥ 1`, the horizontal edge is contained in
   `t2 (b.1, b.2 - 1) ≠ t1 b` of `topSimps2 N`.
2. `vertical_neighbor_topSimps2`: analogous for `b.1 ≥ 1`,
   witness `t2 (b.1 - 1, b.2)`.
3. `t2_face0_neighbor_topSimps2`: for `c ∈ t2Bases N`, t2 face0
   ("right side") is contained in `t1 (c.1+1, c.2) ≠ t2 c`.
4. `t2_face1_neighbor_topSimps2`: face1 ("top side"), witness
   `t1 (c.1, c.2+1)`.
5. `t2_face2_neighbor_topSimps2`: face2 ("diagonal"), witness
   `t1 c` itself.

Each is a 4-tuple term-mode proof matching the pattern of S17's
`diagonal_neighbor_topSimps2` reverse direction, using S16/S17
building blocks.

**Building-block coverage table** for `_hBoundaryOnFace`
(now complete):

| cell | edge | boundary case | interior case |
|------|------|----------------|----------------|
| t1   | diagonal   | S18.1 `diagonal_only_container_of_t1_boundary` | S17 `diagonal_neighbor_topSimps2` |
| t1   | horizontal | S18.1 `horizontal_only_container_of_t1_boundary` | S18.2.1 `horizontal_neighbor_topSimps2` |
| t1   | vertical   | S18.1 `vertical_only_container_of_t1_boundary` | S18.2.2 `vertical_neighbor_topSimps2` |
| t2   | face0      | (impossible, no boundary) | S18.2.3 `t2_face0_neighbor_topSimps2` |
| t2   | face1      | (impossible, no boundary) | S18.2.4 `t2_face1_neighbor_topSimps2` |
| t2   | face2      | (impossible, no boundary) | S18.2.5 `t2_face2_neighbor_topSimps2` |

**Note (S19, PR pending)**: the abstract `T.adj s k = none ↔
container card = 1` bridge is now done as 3 generic lemmas in
`S19AdjBridge` (`adjFn_eq_none_iff_card_le_one`,
`adjFn_eq_none_iff_card_eq_one`, `toTriangulation_adj_eq_none_iff`).
S20 next: case-split through the 11 building blocks above.

Session 18 part 1 (PR #17133, merged): Promoted S16/S17 edge
building blocks into the **boundary-edge container singletons**: for
each of the three edge types of a `t1 b` cell, we prove that under
the matching geometric boundary condition the container set inside
`topSimps2 N` is exactly `{t1 b}`, and the two endpoints of the
boundary edge satisfy the matching `onFaceΔ2` predicate.

Specifically (9 new lemmas):

1. **Singleton container equalities** (3 lemmas):
   - `diagonal_only_container_of_t1_boundary` (N ≤ b.1+b.2+1)
   - `horizontal_only_container_of_t1_boundary` (b.2 = 0)
   - `vertical_only_container_of_t1_boundary` (b.1 = 0)
2. **Cardinality-1 corollaries** (3 lemmas):
   - `diagonal_card_eq_one_of_t1_boundary`
   - `horizontal_card_eq_one_of_t1_boundary`
   - `vertical_card_eq_one_of_t1_boundary`
3. **`onFaceΔ2` endpoint witnesses** (3 lemmas):
   - `diagonal_endpoints_on_face2`
   - `horizontal_endpoints_on_face1`
   - `vertical_endpoints_on_face0`

Together these supply *both* sides of the existential
`∃ faceIdx : Fin 3, ∀ j ≠ k, onFaceΔ2 N (vertex s j) faceIdx`
required by `_hBoundaryOnFace` for the t1 boundary cases. The
remaining S18 work is the t2-share lemmas (every t2 face is
shared with a t1 cell, so t2 contributes no boundary doors)
and the `adjFn` ↔ `containersOf.card ≤ 1` translation that wires
all of this into the abstract `Triangulation.boundary_doors_odd`
hypothesis.

Session 17 (PR #17101, merged): Extended the `N2BoundaryAnalysis` section
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
- `N2BoundaryAnalysis` base ↔ topSimps2 bridge (S17, PR #17101
  merged): 13 new lemmas converting base membership to
  topSimps2 containment, plus the missing diagonal-boundary case
  `diagonal_not_in_t2_at_diagonal` and the top-level classification
  `diagonal_neighbor_topSimps2`.
- `N2BoundaryAnalysis` t1-boundary container singletons +
  onFaceΔ2 witnesses (S18 part 1, PR #17133, merged): 9 new
  lemmas — three `*_only_container_of_t1_boundary`, three
  `*_card_eq_one_of_t1_boundary` corollaries, and three
  `*_endpoints_on_face*` Δ²-face witness lemmas.
- `N2BoundaryInteriorNeighbors` interior-face existentials (S18
  part 2, PR #17149, merged): 5 new lemmas covering the interior
  side for each of the six face/edge × cell-type combinations.
- `S19AdjBridge` abstract adj-bridge (S19, this session, build
  pending): 3 new generic lemmas —
  `adjFn_eq_none_iff_card_le_one` (no pseudomanifold needed),
  `adjFn_eq_none_iff_card_eq_one` (combined with pseudomanifold),
  and `toTriangulation_adj_eq_none_iff` (restated for the
  abstract `Triangulation.adj`).
- `sperner_panchromatic_two` (n=2): 1 sorry remaining
- n≥3: future work

## Path Forward for n≥2 (post-S19)

`Triangulation.boundary_doors_odd` requires four hypotheses:
1. `_hSperner` — done generically by S14 wrapper (cN2_total_isSpernerColoring)
2. `_hBoundaryOnFace` — S16/S17/S18.1/S18.2 supply ALL six
   face/edge × cell-type combinations as `private lemma`s (see
   coverage table above). S19 (this session) supplies the
   abstract bridge `T.adj s k = none ↔ container card = 1`.
   **S20 next**: case-split through the 11 building blocks
   above to assemble the existential `∃ faceIdx, ...` for the
   boundary cases and produce a `False.elim` for the t2-cell
   cases (~80 lines, mostly case-splitting; arithmetic content
   is in S16-S18).
3. `_hLowerDim` — done generically by S15 helper
4. `_hLastFace` — TODO (~120 lines, bijection with face2_path_odd via S12)

Then apply `Triangulation.sperner` (~50 lines for diameter bound + real
coordinates). Total estimated remaining: ~200 lines across 2-3 sessions.

## Gallery Status

Main entry: 1 axiom (honest, correct). Companion shows n=0,1 concretely proved.
OQ-02 question answered modulo 1 axiom (the combinatorial Sperner's lemma for n-dim grid).
