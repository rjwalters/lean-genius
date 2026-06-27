# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 3

## Current Focus

Option C locked. Session 2 (2026-06-27) produced the concrete inductive proof
structure for the Phase-2 oddness and a field-by-field plan for the Phase-1
`SpernerTriangulation` instance. The abstract `SpernerNDim.sperner_ndim`
(0-sorry, line 654) is the finish line; it needs an unoriented Freudenthal
`SpernerTriangulation d N` instance plus an odd last-face-door count.

## Active Approach

**Option C: SpernerTriangulation instance + inductive door-oddness**
- (step 0) Prove `BaryPoint d N ≃ Vertex d N` bridge (small, verifiable first PR)
- (Phase 1) Define `freudenthal d N : SpernerTriangulation d N` — unoriented Kuhn
  cells, one per geometric simplex; discharge 8 structure fields
- (Phase 2) Prove last-face-door-oddness by induction on d via the
  door ↔ panchromatic-(d−1)-simplex bijection (see knowledge.md Session 2)
- Apply `sperner_ndim`; retire false `boundary_doors_odd`/`boundary_verts_on_face`

## Attempt Count
- Total attempts: 2 (both analysis/planning; no proof code written yet)
- Current approach attempts: 0 implementation
- Approaches tried: 1 (Option C; A/B documented as alternatives)

## Blockers
- Not mathematically blocked: path is concrete and the abstract finish line exists.
- **Infra-gated**: large (~400–650 line) build; needs healthy build infra to verify.
  At session 2 the root FS was at 97% (~420 MiB free) with 2 stale lean-build
  containers — unsafe to launch a fresh Mathlib docker build.

## Next Action

1. **(small, do first)** Prove `BaryPoint d N ≃ Vertex d N` in a bridge file; build it.
2. **(Phase 1)** Define `freudenthal d N : SpernerTriangulation d N` (unoriented Kuhn
   cells, one per geometric cell — no free orientation flag); prove the 8 fields.
3. **(Phase 2)** Prove last-face-door-oddness by induction on d; feed to `sperner_ndim`.
4. Reroute `sperner_grid` through the instance; delete the false lemmas.
