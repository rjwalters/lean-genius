# Problem: n-Dimensional Sperner — Boundary-Door Oddness by Dimensional Induction

**Slug**: sperner-ndim-oq-02
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap
**Tier**: A
**Significance**: 8/10
**Tractability**: 6/10

## Problem Statement

### Formal Statement

The abstract Sperner parity theorem (`SpernerNDim.sperner`) is proved but requires the
Freudenthal grid triangulation to be realized as a `SpernerTriangulation` instance. The
open question is: can `boundary_doors_odd` be proved for a concrete triangulation,
and what is the correct statement for oriented vs unoriented simplices?

Specifically, prove that the number of boundary doors on the last face is odd for any
Sperner coloring of the Freudenthal grid, by induction on dimension.

### Plain Language

The n-dimensional Sperner lemma says: any Sperner-colored triangulation of the
standard n-simplex has an odd number of fully-colored simplices. The abstract version
(`SpernerNDim.lean`) is already proved. The gap is connecting this abstract theorem
to the concrete Freudenthal grid triangulation (`SpernerGrid.lean`).

**Key obstacle discovered (2026-04-22)**: `boundary_doors_odd` as stated in
`SpernerGrid.lean` is **false** for oriented simplices — each geometric simplex appears
twice (both orientations), making all counts even. The fix requires either:
- **Option A**: Canonical-orientation sub-complex (choose one orientation per geometric simplex)
- **Option B**: Direct reversal-pairs argument (count = 2 × geometric count = 2 × odd ≥ 2)
- **Option C**: Define a `SpernerTriangulation` instance for the Freudenthal grid using
  unoriented simplices and apply the existing abstract theorem (**recommended**)

### Why This Matters

- Completes the `sperner_grid` theorem with 0 sorries
- Demonstrates the Freudenthal grid satisfies the abstract `SpernerTriangulation` axioms
- Creates a template for connecting concrete triangulations to the abstract framework
- Downstream: Brouwer's fixed point theorem, Kuhn path-following algorithm formalization

## Source

Open question 1 from `src/data/proofs/sperner-ndim/meta.json`:
> "Prove boundary-door-oddness by induction on dimension for concrete triangulations —
> the face-d restriction of the Freudenthal triangulation is a lower-dimensional
> Freudenthal grid"

## Related Files

- `proofs/Proofs/SpernerNDim.lean` — abstract parity theorem (complete)
- `proofs/Proofs/SpernerGrid.lean` — concrete grid, has sorries including false `boundary_doors_odd`
- `src/data/proofs/sperner-ndim/meta.json` — gallery entry

## Approach

**Recommended: Option C — SpernerTriangulation instance for Freudenthal grid**

Define an unoriented version of the Freudenthal grid complex and prove it satisfies
the `SpernerTriangulation` axioms from `SpernerNDim.lean`. Apply `SpernerNDim.sperner`
to conclude. This is cleanest because the orientation problem is bypassed entirely.

**Key implementation steps:**
1. Define `FreudenthalComplex d N` using unoriented (vertex-set) simplices
2. Prove the three `SpernerTriangulation` axioms:
   a. Every interior simplex has exactly 2 doors (interior pairing)
   b. Boundary simplices on face k < d have 0 doors (non-last-face boundary vanishes)
   c. Boundary simplices on face d have exactly 1 door (last face has odd = 1 door)
3. Apply `SpernerNDim.sperner` to get the panchromatic count ≡ 1 (mod 2)

## Sorries in SpernerGrid.lean

| Sorry | Line | Status | Notes |
|-------|------|--------|-------|
| `boundary_doors_odd` | ~1175 | FALSE as stated | Requires architectural fix |
| `boundary_verts_on_face` | ~1239 | FALSE (auxiliary) | Used only for false theorem |
| `gridAdj_symm` | ~1154 | Provable | Case analysis on orientation |
| `gridAdj_vertex` | ~1163 | Partially provable | Interior case clear |
| `sperner_grid` | ~1270 | Blocked by above | Final conclusion |
