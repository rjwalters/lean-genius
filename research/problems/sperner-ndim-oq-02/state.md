# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 4

## Current Focus

Option C in progress. **Session 3 (2026-06-27) delivered step 0**: the
`BaryPoint d N ≃ Vertex d N` coordinate bridge as
`proofs/Proofs/SpernerNDimOQ02.lean` (`baryEquivVertex`, plus `onFace_toVertex`
and `isSperner_iff` correspondences). UNVERIFIED — build host down (FS 98%).
Next is Phase 1 (the `freudenthal` instance). The abstract
`SpernerNDim.sperner_ndim` (0-sorry, line 654) remains the finish line; it needs
an unoriented Freudenthal `SpernerTriangulation d N` instance plus an odd
last-face-door count.

## Active Approach

**Option C: SpernerTriangulation instance + inductive door-oddness**
- (step 0) ✅ DONE (Session 3, UNVERIFIED) — `BaryPoint d N ≃ Vertex d N` bridge
  in `SpernerNDimOQ02.lean` (`baryEquivVertex` + `onFace_toVertex` + `isSperner_iff`)
- (Phase 1) Define `freudenthal d N : SpernerTriangulation d N` — unoriented Kuhn
  cells, one per geometric simplex; discharge 8 structure fields
- (Phase 2) Prove last-face-door-oddness by induction on d via the
  door ↔ panchromatic-(d−1)-simplex bijection (see knowledge.md Session 2)
- Apply `sperner_ndim`; retire false `boundary_doors_odd`/`boundary_verts_on_face`

## Attempt Count
- Total attempts: 3 (2 analysis/planning + 1 implementation: step-0 bridge)
- Current approach attempts: 1 implementation (step 0 of Option C)
- Approaches tried: 1 (Option C; A/B documented as alternatives)

## Blockers
- Not mathematically blocked: path is concrete and the abstract finish line exists.
- **Infra-gated**: large (~400–650 line) build; needs healthy build infra to verify.
  At session 2 the root FS was at 97% (~420 MiB free) with 2 stale lean-build
  containers — unsafe to launch a fresh Mathlib docker build.

## Next Action

1. ✅ DONE — `BaryPoint d N ≃ Vertex d N` bridge written (`SpernerNDimOQ02.lean`,
   UNVERIFIED). **Verify it once build infra recovers.**
2. **(Phase 1)** Define `freudenthal d N : SpernerTriangulation d N` (unoriented Kuhn
   cells, one per geometric cell — no free orientation flag); prove the 8 fields.
   Use `baryEquivVertex`/`toVertex` for the `vertices` field.
3. **(Phase 2)** Prove last-face-door-oddness by induction on d; feed to `sperner_ndim`.
4. Reroute `sperner_grid` through the instance; delete the false lemmas.
