# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 7

> **Session 6 (2026-06-27, researcher-7): VERIFIED the step-0 bridge + KEY DISCOVERY.**
> Build infra recovered enough for the standalone `lake env lean` fallback (Docker
> containerd still corrupt: `meta.db` I/O errors, zombie containers un-removable).
> Discovery: `SpernerNDimOQ02.lean` as merged (#30751) `import`s `Proofs.SpernerGrid`,
> which **does not compile** — 21 errors (omega failures, type mismatches, even a
> parse error) in the *oriented* `GridSimplex`/`gridAdj` machinery (lines 600–1556),
> plus 4 pre-existing sorries. That machinery is exactly what Option C **abandons**
> (its `boundary_doors_odd` is the false theorem this problem replaces), and it is
> not in `Proofs.lean`'s build aggregator, so the breakage went unnoticed while
> Docker was down. **Fix**: extracted `SpernerGrid`'s clean SECTION II (the
> `BaryPoint` API: structure, `DecidableEq`/`Fintype`, `onFace`, `IsSperner`) into a
> new self-contained module `Proofs/SpernerGridBary.lean` (namespace kept as
> `SpernerGrid`, import-disjoint from the broken file) and repointed
> `SpernerNDimOQ02.lean` at it. **Both files now build clean via `lake env lean`;
> `baryEquivVertex`/`onFace_toVertex`/`isSperner_iff`/`toVertex_injective` depend only
> on `propext`/`Classical.choice`/`Quot.sound` — 0 sorry, 0 extra axiom.** The bridge
> is now genuinely VERIFIED on a compiling foundation. See knowledge.md "Session 6".

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
- (step 0) ✅ DONE + **VERIFIED** (Session 6) — `BaryPoint d N ≃ Vertex d N` bridge
  in `SpernerNDimOQ02.lean`, now on the clean `Proofs/SpernerGridBary.lean`
  foundation (0 sorry, 0 extra axiom; `lake env lean` clean). The originally
  merged (#30751) version imported the broken `SpernerGrid` and could not build.
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
- **`SpernerGrid.lean` is broken** (21 compile errors in the oriented
  `GridSimplex`/`gridAdj` block). The Session-4 Phase-1 plan assumed it could reuse
  `SpernerGrid.GridSimplex` as the cell representation; that is no longer viable.
  Phase 1 must define its **own** canonical-cell type (on the clean
  `SpernerGridBary.BaryPoint` foundation) rather than subtyping `SpernerGrid.GridSimplex`.
- **Infra**: Docker build host still corrupt (containerd `meta.db` I/O errors,
  zombie containers). The standalone `lake env lean` fallback works for single files
  whose deps are cached/clean (used this session to verify the bridge).

## Next Action

1. ✅ DONE + VERIFIED (Session 6) — bridge on the clean `SpernerGridBary` foundation
   (0 sorry, 0 extra axiom). Phase-1 design fixed (Session 4).
2. **(Phase 1 impl)** Define the unoriented cell representation **from scratch** on
   `SpernerGridBary.BaryPoint` (do NOT subtype `SpernerGrid.GridSimplex` — that file
   is broken). Self-contained Kuhn cell = base `BaryPoint` + a permutation of the d
   increment directions, with a canonicality predicate selecting one rep per
   geometry. `vertices` (= `toVertex ∘ verts`, injective via `toVertex_injective`);
   discharge the 5 adjacency fields + `boundary_face` (via `onFace_toVertex`).
3. **(Phase 2)** Last-face-door-oddness by induction on d; feed `sperner_ndim`,
   transport hypothesis with `isSperner_iff`.
4. **(End-goal caveat)** The original target — rerouting `SpernerGrid.sperner_grid`
   and deleting its false `boundary_doors_odd` — is blocked on `SpernerGrid.lean`
   itself compiling. The verified Option-C instance can instead be shipped as a
   standalone n-dim Sperner result over `BaryPoint`, independent of the broken file.
