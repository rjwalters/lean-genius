# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 8

> Session 7 (2026-06-27, researcher-12): **Phase-1 foundation extracted +
> reconstruction lemmas (verified, 0-axiom)**. Factored the entire *clean* region
> of broken `SpernerGrid.lean` (SECTIONS III–V: `GridSimplex` + `DecidableEq`/
> `Fintype` + `verts_injective` + coordinate trackers, lines 241–513, all before
> the first error @679) into `SpernerGridBase.lean` (now 460 L), so the Phase-1
> instance can build `Simplex`/`vertices`/`vertices_injective` over a clean base.
> Added NEW SECTION VI reconstruction lemmas (`incDir_const_before`,
> `last_coord_non_miss`, `last_coord_miss`): every vertex is an explicit function
> of `(verts 0, miss, incDir)` — the backbone `IsCanon` needs. Build EXIT 0;
> `#print axioms` = `{propext, Classical.choice, Quot.sound}` only. knowledge.md
> "Session 7".

> Session 6 (2026-06-27, researcher-12): **VERIFIED the step-0 bridge (0-axiom)**
> and **decoupled it from broken `SpernerGrid.lean`**. Docker still corrupt
> (containerd meta.db I/O error) but disk recovered intermittently; used the
> local `LAKE_UNSAFE=1 ./bin/lake env lean` single-file fallback. Two findings:
> (1) `SpernerNDimOQ02.lean`'s proofs all type-check, 0 sorry, axioms =
> `{propext, Classical.choice, Quot.sound}` only → **verified, 0-axiom**.
> (2) `SpernerGrid.lean` is **un-buildable on main** — 15+ genuine compile errors
> (omega gaps, a syntax typo @1372, rewrite/type-mismatch, unknown-ident `hs'`)
> spanning the `gridAdj`/`boundaryFlip`/doors machinery (lines 679–1740), masked
> for ages by "build host down". Because the merged bridge `import`ed the broken
> file, it could not actually build. **Fix**: factored the clean coordinate
> primitives (`BaryPoint`/`onFace`/`IsSperner`, byte-for-byte) into a new
> `SpernerGridBase.lean` and re-pointed the bridge import at it. Both build clean
> end-to-end (real imports, no stubs). See knowledge.md "Session 6".

## Current Focus

Option C in progress. **Session 3 (2026-06-27) delivered step 0**: the
`BaryPoint d N ≃ Vertex d N` coordinate bridge as
`proofs/Proofs/SpernerNDimOQ02.lean` (`baryEquivVertex`, `onFace_toVertex`,
`isSperner_iff`) — MERGED via PR #30751, and **now VERIFIED (0-axiom) and made
buildable in Session 6** (imports the new clean `SpernerGridBase.lean` instead of
the broken `SpernerGrid.lean`).
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

0. ✅ DONE (Session 6) — bridge VERIFIED 0-axiom; `SpernerGridBase.lean` created
   so the bridge builds independently of the broken `SpernerGrid.lean`.
   **Phase 1 can now build its instance against the clean `SpernerGridBase`
   primitives** (`BaryPoint`/`onFace`/`IsSperner` are stable & verified there).
   Follow-up (mechanic/separate): repair or retire the 15+ errors in
   `SpernerGrid.lean` itself; Option C will delete most of that machinery anyway.
1. ✅ DONE — bridge written + merged (#30751); Phase-1 design fixed (Session 4).
2. **(Phase 1 impl)** Per the Session-4 checklist in knowledge.md:
   define `canonMiss`/`IsCanon` (+ decidability + per-geometry uniqueness),
   `Simplex := {s : GridSimplex // IsCanon s}`, `vertices` (=`toVertex ∘ verts`,
   injective via `toVertex_injective`), and the dual-graph `adj`; discharge the
   5 adjacency fields + `boundary_face` (via `onFace_toVertex`).
3. **(Phase 2)** Last-face-door-oddness by induction on d; feed `sperner_ndim`,
   transport hypothesis with `isSperner_iff`.
4. Reroute `sperner_grid` through the instance; delete the false lemmas.
5. **Verify** the merged bridge + new instance once build infra recovers.
