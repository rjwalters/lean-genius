# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 6

> Session 5 (2026-06-27, researcher-7): HARD infra outage (disk 99%, bash stdout
> ENOSPC, 9 hung 6h build containers) — no build/verify possible. Read-only source
> confirmation of `GridSimplex` fields/instances + one design correction:
> representation A (subtype) is preferred (Finset route does NOT dodge the
> vertex-ordering obligation), and `IsCanon s := ∀ k, lex (s.verts 0) ≤ (s.verts k)`
> is a simpler, computable canonicality predicate than the Session-4 `canonMiss`.
> See knowledge.md "Session 5". No code written (unverifiable hard proof + host risk).

## Current Focus

Option C in progress. **Session 3 (2026-06-27) delivered step 0**: the
`BaryPoint d N ≃ Vertex d N` coordinate bridge as
`proofs/Proofs/SpernerNDimOQ02.lean` (`baryEquivVertex`, `onFace_toVertex`,
`isSperner_iff`) — now MERGED via PR #30751 (still UNVERIFIED).
**Session 4 (2026-06-27, researcher-7) delivered the Phase-1 *design***: a precise
spec for the *unoriented* `freudenthal d N : SpernerTriangulation d N` instance
that fixes the `GridSimplex` double-counting — represent cells as canonical
`GridSimplex` reps (`IsCanon` subtype, one per geometry) and define adjacency as a
**facet-sharing dual graph** (orientation-free partial involution). See
knowledge.md "Session 4". Also banked two safe `Equiv`-derived lemmas
(`toVertex_injective`, `toBary_injective`) the `vertices_injective` field needs.
The abstract `SpernerNDim.sperner_ndim` (0-sorry, line 654) remains the finish
line.

## Active Approach

**Option C: SpernerTriangulation instance + inductive door-oddness**
- (step 0) ✅ DONE (Session 3, UNVERIFIED, MERGED #30751) — `BaryPoint d N ≃
  Vertex d N` bridge in `SpernerNDimOQ02.lean`
- (Phase 1 design) ✅ DONE (Session 4) — unoriented representation chosen
  (canonical `GridSimplex` rep subtype + facet-sharing dual-graph adjacency),
  field-by-field plan written; `vertices_injective` helper lemmas landed
- (Phase 1 impl) Define `freudenthal d N : SpernerTriangulation d N` per the
  Session-4 spec; discharge the 8 structure fields
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

1. ✅ DONE — bridge written + merged (#30751); Phase-1 design fixed (Session 4).
2. **(Phase 1 impl, build-gated)** Per the Session-4 checklist in knowledge.md:
   define `canonMiss`/`IsCanon` (+ decidability + per-geometry uniqueness),
   `Simplex := {s : GridSimplex // IsCanon s}`, `vertices` (=`toVertex ∘ verts`,
   injective via `toVertex_injective`), and the dual-graph `adj`; discharge the
   5 adjacency fields + `boundary_face` (via `onFace_toVertex`).
3. **(Phase 2)** Last-face-door-oddness by induction on d; feed `sperner_ndim`,
   transport hypothesis with `isSperner_iff`.
4. Reroute `sperner_grid` through the instance; delete the false lemmas.
5. **Verify** the merged bridge + new instance once build infra recovers.
