# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27
**Iteration**: 5

## Current Focus
n=1 Tucker line COMPLETE (combinatorial core `SpernerTuckerOneDim` + continuous
1-D Borsuk–Ulam capstone `SpernerTuckerBorsukUlamOneDim`). This session isolated
the **abstract path-following engine** for n≥2 as
`proofs/Proofs/SpernerTuckerPathFollowing.lean` (103 LOC, 0 sorries, 0 axioms).

## Active Approach
Abstract graph-theoretic core (no geometry): in a finite graph of max degree 2
(a union of paths and cycles) the degree-one vertices (path ends) are even in
number; a boundary/interior split then forces an interior end when the boundary
ends are odd (`exists_interior_degree_one`). This is the path-following analogue
of the parent's `door_count_parity`.

## Attempt Count
- Total attempts: 3
- Approaches tried: 3 (engine-reusability assessment → 1-D direct parity →
  abstract path-following engine for n≥2)

## Blockers
- Docker containerd I/O error (verified instead via `lake env lean`).
- n≥2 Tucker still needs the GEOMETRIC instantiation of the engine
  (almost-complementary-simplex graph, max-degree-2 proof, odd boundary ends).

## Next Action
- Build the almost-complementary-simplex graph on antipodally symmetric
  triangulated B^n, prove max degree ≤ 2 and odd boundary ends, then apply
  `exists_interior_degree_one` to obtain n≥2 Tucker.
- General-n Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness.
