# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 8

> **Session 7 (2026-06-27, researcher-7): Phase-1 cell machinery landed + VERIFIED.**
> Built the self-contained, compiling cell foundation the Phase-1 `SpernerTriangulation`
> instance needs — everything *except* the orientation-free adjacency involution.
> Rebased onto the canonical clean foundation `Proofs/SpernerGridBase.lean` (the
> shared `BaryPoint` extraction that landed on main via #30779; my parallel
> `SpernerGridBary.lean` was retired as a duplicate of it).
> Two new files (both build clean via `lake env lean`, both 0 sorry / 0 extra axiom,
> deps only `propext`/`Classical.choice`/`Quot.sound`):
> - `Proofs/SpernerGridCell.lean` — a clean extraction of `SpernerGrid.lean`'s
>   SECTIONS III–V (`GridSimplex` structure + `DecidableEq`/`Fintype`, the chain
>   lemmas `verts_injective`/`incDir_const_after`/`miss_coord_at`/`base_miss_ge_d`/
>   `miss_coord_ge`/`incDir_surj_complement`, and `BaryPoint.transfer` + its 3
>   coord lemmas), reproduced strictly *before* the broken `gridAdj` block on the
>   compiling `SpernerGridBase.BaryPoint` foundation (namespace `SpernerGrid`,
>   import-disjoint from the broken file).
> - `Proofs/SpernerNDimOQ02Cell.lean` — the `vertices`-field bridge over cells:
>   `cellVertices := toVertex ∘ s.verts`, `cellVertices_injective`
>   (= `toVertex_injective ∘ verts_injective`), `onFace_cellVertices` (face
>   correspondence for `boundary_face`, from `onFace_toVertex`), and the
>   canonicality scaffold `BaryPoint.lexLe` / `IsCanon` (chain base is lex-least)
>   with `DecidablePred IsCanon`, the `CanonCell` subtype, its `DecidableEq` and
>   (noncomputable) `Fintype`, and `canonVertices`/`canonVertices_injective`.
> **Remaining for Phase 1**: the facet-sharing dual-graph `adj` + its 5 involution
> fields (`adj_symm`/`adj_vertices`/`adj_ne`/`adj_unique_facet`/`boundary_face`),
> plus the per-geometry uniqueness of `IsCanon`. See knowledge.md "Session 7".

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
- (step 0) ✅ DONE + **VERIFIED** (Session 6) — `BaryPoint d N ≃ Vertex d N` bridge
  in `SpernerNDimOQ02.lean`, now on the clean `Proofs/SpernerGridBase.lean`
  foundation (0 sorry, 0 extra axiom; `lake env lean` clean). The originally
  merged (#30751) version imported the broken `SpernerGrid` and could not build.
- (Phase 1 design) ✅ DONE (Session 4) — unoriented representation chosen
  (canonical `GridSimplex` rep subtype + facet-sharing dual-graph adjacency),
  field-by-field plan written; `vertices_injective` helper lemmas landed
- (Phase 1 impl, cell foundation) ✅ DONE + **VERIFIED** (Session 7) — clean cell
  machinery on the compiling foundation (`SpernerGridCell.lean`) + the `vertices`
  field bridge, face correspondence, and `CanonCell` subtype scaffold
  (`SpernerNDimOQ02Cell.lean`). 0 sorry, 0 extra axiom.
- (Phase 1 impl, adjacency) Define `adj` (facet-sharing dual graph) on `CanonCell`,
  discharge the 5 involution fields + `boundary_face` + `IsCanon` uniqueness, then
  assemble `freudenthal d N : SpernerTriangulation d N` (8 fields; 3 already in hand)
- (Phase 2) Prove last-face-door-oddness by induction on d via the
  door ↔ panchromatic-(d−1)-simplex bijection (see knowledge.md Session 2)
- Apply `sperner_ndim`; retire false `boundary_doors_odd`/`boundary_verts_on_face`

## Attempt Count
- Total attempts: 3 (2 analysis/planning + 1 implementation: step-0 bridge)
- Current approach attempts: 1 implementation (step 0 of Option C)
- Approaches tried: 1 (Option C; A/B documented as alternatives)

## Blockers
- Not mathematically blocked: path is concrete and the abstract finish line exists.
- **`SpernerGrid.lean` is broken** (21 compile errors in the oriented
  `GridSimplex`/`gridAdj` block). The Session-4 Phase-1 plan assumed it could reuse
  `SpernerGrid.GridSimplex` as the cell representation; that is no longer viable.
  Phase 1 must define its **own** canonical-cell type (on the clean
  `SpernerGridBase.BaryPoint` foundation) rather than subtyping `SpernerGrid.GridSimplex`.
- **Infra**: Docker build host still corrupt (containerd `meta.db` I/O errors,
  zombie containers). The standalone `lake env lean` fallback works for single files
  whose deps are cached/clean (used this session to verify the bridge).

## Next Action

0. ✅ DONE + VERIFIED (Session 6) — bridge on the clean `SpernerGridBase` foundation
   (0 sorry, 0 extra axiom; `SpernerGridBase.lean` landed on main via #30779 so the
   bridge builds independently of the broken `SpernerGrid.lean`). Phase-1 design
   fixed (Session 4). Follow-up (mechanic/separate): repair or retire the 15+ errors
   in `SpernerGrid.lean` itself; Option C deletes most of that machinery anyway.
1. ✅ DONE + VERIFIED (Session 7) — cell foundation on `SpernerGridBase.BaryPoint`:
   `SpernerGridCell.lean` (own `GridSimplex` + chain lemmas + `BaryPoint.transfer`)
   and `SpernerNDimOQ02Cell.lean` (`cellVertices` bridge, `onFace_cellVertices`,
   `CanonCell` subtype scaffold + `IsCanon`/`lexLe`). 0 sorry, 0 extra axiom.
2. **(Phase 1 impl, adjacency)** Define the facet-sharing dual-graph `adj` on
   `CanonCell` and discharge the 5 involution fields + `boundary_face` (via
   `onFace_cellVertices`), plus per-geometry uniqueness of `IsCanon`; then assemble
   `freudenthal d N : SpernerTriangulation d N` (8 fields; 3 already in hand).
3. **(Phase 2)** Last-face-door-oddness by induction on d; feed `sperner_ndim`,
   transport hypothesis with `isSperner_iff`.
4. **(End-goal caveat)** The original target — rerouting `SpernerGrid.sperner_grid`
   and deleting its false `boundary_doors_odd` — is blocked on `SpernerGrid.lean`
   itself compiling. The verified Option-C instance can instead be shipped as a
   standalone n-dim Sperner result over `BaryPoint`, independent of the broken file.
