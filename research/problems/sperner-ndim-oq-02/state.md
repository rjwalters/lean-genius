# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 21

> **Session 21 (2026-07-07, researcher-9): top-facet (`Fin.last d`) pivot reciprocal base vertex + vertex-level reciprocity (VERIFIED 0-axiom, `docker-build.sh Proofs.SpernerNDimOQ02` exit 0, 7745 jobs).** Built the *dual* of `zeroPivotTop`/`zeroPivotCell`. Session 20 pinned the coordinate formula for `s`'s deleted apex; this session realizes it as a genuine `BaryPoint` and proves the vertex-level reciprocity. Added 7 declarations (+~150 L) to `SpernerNDimOQ02.lean` (3256 → ~3406 L):
> - **`lastIncDir u hd1`** — the direction increasing at `u`'s final chain step `d-1` (the increment the top-facet pivot reverses).
> - **`topPivotBottom u hd1 hfeas`** — the reciprocal base vertex: delete `u`'s apex, prepend a new base *below* `u.verts 0` by reversing the final increment (decrement `lastIncDir`, increment `miss`). A bona-fide `BaryPoint` (`sum_eq` proved by the same telescoping-correction argument as `zeroPivotTop`, with the +1/−1 roles swapped; feasible when the base's `lastIncDir` coordinate ≥ 1). Coordinate accessors `topPivotBottom_coords_lastIncDir` / `_coords_miss` / `_coords_other`.
> - **`zeroPivotCell_lastIncDir`** — the facet-`0` partner's last increment is `s`'s omitted `incDir 0` (deferred to the final step by the cyclic rotation `zeroPivotInc`, via `zeroPivotInc_last`).
> - **`zeroPivotCell_lastIncDir_feasible`** — the top-facet pivot is *always* feasible on the partner: `t.verts 0 = s.verts 1` has `incDir 0` coordinate `base+1 ≥ 1` (`step_inc` at step 0).
> - **`topPivotBottom_zeroPivotCell`** — capstone: `topPivotBottom (zeroPivotCell s) = s.verts 0`. The dual top-facet pivot applied to the facet-`0` partner recovers `s`'s deleted apex *exactly* (per-coordinate via `zeroPivotCell_base_recover`/`_incDir0`/`_miss_recover`). This is the reciprocal (downward) vertex the partial involution `adj` needs: the two pivots invert one another at the shared cross-chain facet `gridFacet s 0 = gridFacet t (Fin.last d)`.
> **Frontier NARROWED**: the reciprocal base *vertex* is now a first-class object and its recovery is proved. Remaining is assembling the full `topPivotCell` GridSimplex (verts = `topPivotBottom` prepended to `u`'s lower chain; incDir = reflected rotation) with all 7 chain fields, then lifting the vertex identity to `topPivotCell (zeroPivotCell s) = s`, then the cross-`miss` terminal partner for the extremal `base_miss = d` cell. PR: research/sperner-ndim-oq02-toppivot-reciprocity (off main HEAD).
>
> **Session 20 (2026-07-04, researcher-11): reciprocity base identity — the facet-`0` partner recovers `s`'s deleted apex by one downward step (VERIFIED 0-axiom, `docker-build.sh Proofs.SpernerNDimOQ02` exit 0, 7745 jobs; merged PR #34652).** Turned toward crux 1 (the top-facet `Fin.last d` pivot that must invert the facet-`0` pivot for `adj` to be a partial involution). Session 17 proved `s` and `t = zeroPivotCell s` meet exactly along the shared facet `gridFacet s 0 = gridFacet t (Fin.last d)`; Sessions 18–19 made the *upward* `base_miss` descent quantitative. Session 20 pins the **reciprocal downward move**: `s`'s deleted apex `s.verts 0` is exactly `t`'s base vertex `t.verts 0` (= `s.verts 1`, `zeroPivotCell_verts_of_lt`) moved one lattice step *back* along the omitted direction `incDir 0` — the exact inverse of `s`'s step-`0` chain move. Added 3 theorems (+~55 L) to `SpernerNDimOQ02.lean` (3187 → ~3242 L):
> - **`zeroPivotCell_base_recover`** — capstone: the full all-coordinate formula for `s.verts 0` in terms of `t.verts 0` — decrement `incDir 0`, increment `miss`, all others fixed (proved by `step_inc`/`step_dec`/`step_same` at `k = 0`). Completely pins the top-facet pivot's reintroduced vertex as `s`'s own apex.
> - `zeroPivotCell_base_incDir0` / `zeroPivotCell_base_miss_recover` — the two moving-coordinate specializations (down one in `incDir 0`, up one in `miss`), directly usable by the reciprocity/involution assembly.
> This is the coordinate core of crux 1: it shows the downward facet-`last` pivot on `t` reintroduces exactly `s`'s deleted apex, the reciprocity `adj` needs at the boundary facets. **Frontier NARROWED**: the reciprocal vertex is now pinned; remaining is assembling the `topPivotCell`/`lastPivot` GridSimplex (6 chain fields) and proving `topPivotCell (zeroPivotCell s) = s`, then the cross-`miss` terminal partner for the extremal `base_miss = d` cell. PR: research/sperner-ndim-oq02-recover-apex (stacked on merged S19 #34636).
>
> **Session 19 (2026-07-04, researcher-11): exact top-`miss` height of the facet-`0` partner + explicit descent length (VERIFIED 0-axiom, `docker-build.sh Proofs.SpernerNDimOQ02` exit 0, 7745 jobs).** Upgraded Session 18's *iff-form* pivot-feasibility lemmas to **exact coordinate formulas**, making the `base_miss` descent quantitative. Added 2 theorems (+43 L) to `SpernerNDimOQ02.lean`:
> - `zeroPivotCell_top_miss` — the partner cell's top vertex sits *exactly* `d + 1` below `s`'s base in the shared `miss` direction: `top miss = base_miss − (d + 1)`. Sharpens S18's iff-form `zeroPivotCell_feasible_iff_base_miss_ge` to a definite value; the whole partner is a `miss`-shifted copy of `s`'s upper chain capped one step lower.
> - `zeroPivotCell_extremal_iff_base_miss_eq` — the partner is *itself* the terminal boundary-door cell (own facet-`0` pivot infeasible) ⟺ `base_miss = d + 1`. With `zeroPivotCell_base_miss` (step −1) + `base_miss_ge_d` (floor `d`) this pins the descent length: from base `miss = m` the same-`miss` facet-`0` pivot fires exactly `m − d` times before halting at the extremal cell whose top vertex lies on the geometric `miss`-face — where the cross-`miss` partner (crux 2) must attach. **Frontier UNCHANGED** (dual top-facet pivot involution + cross-`miss` terminal partner). Docker channel RESTORED this session. File 3150 → 3193 L. PR #34636 (research/sperner-ndim-oq02-top-miss-exact, stacked on S18's #34635).
>
> **Session 18 (2026-07-04, researcher-11): facet-`0` pivot miss-descent + termination at boundary door (VERIFIED 0-axiom, docker exit 0, 7745 jobs).** 4 theorems characterizing the same-`miss` facet-`0` pivot as a finite monotone `base_miss` descent: `zeroPivotCell_base_miss` (partner base = `base_miss − 1`), `zeroPivotCell_base_miss_lt` (strict), `zeroPivot_infeasible_iff_base_miss_eq_d` (halts ⟺ `base_miss = d`), `zeroPivotCell_feasible_iff_base_miss_ge` (re-feasible ⟺ `base_miss ≥ d+2`). PR #34635 (research/sperner-ndim-oq02-miss-descent).
>
> **Session 17 (2026-07-04, researcher-11): facet-`0` gluing site proven to be a pseudomanifold-local TWO-CELL MEETING (VERIFIED 0-axiom, `docker-build.sh Proofs.SpernerNDimOQ02` exit 0, 7745 jobs).** Built directly on Session 16's `zeroPivotCell` (the facet-`0` cross-chain partner, feasible regime). Added 3 theorems (+~75 L) to `SpernerNDimOQ02.lean` proving `s` and `zeroPivotCell` intersect in EXACTLY the shared facet:
> - `gridVertices_zero_not_mem_zeroPivotCell_image` — `s`'s deleted apex `gridVertices s 0` is absent from the partner's whole vertex set (chain injectivity kills the reused lower vertices; `zeroPivotTop_not_mem_chain` kills the new apex).
> - `zeroPivotCell_apex_not_mem_s_image` — dually, the partner's apex (Kuhn image of `zeroPivotTop`) is absent from `s`'s vertex set.
> - **`zeroPivotCell_meet_eq_gridFacet_zero`** — capstone: `image(gridVertices s) ∩ image(gridVertices zeroPivotCell) = gridFacet s 0`. Two distinct cells (`zeroPivotCell_ne`), each contributing exactly one apex off the common facet, glue precisely along it — the defining LOCAL pseudomanifold condition, now realized at the facet-`0` site the within-chain `gridNeighbor` leaves unpaired (`gridNeighbor_zero_none_not_boundary_face`). **Frontier NARROWED**: the facet-`0` gluing is now a proven local two-cell meeting (feasible regime); remaining is the dual top-facet (`Fin.last d`) pivot on non-door cells + the cross-`miss` partner for base `miss = d`, then assembling the total `adj` involution. File 2999 → ~3074 L. PR #34629 (research/sperner-ndim-oq02-facet0-meet).
>
> **Session 16 (2026-07-01, researcher-6): FIRST explicit construction of the facet-`0` partner's new vertex + feasibility dichotomy (VERIFIED 0-axiom, `lake env lean` exit 0, `#print axioms` = [propext, Classical.choice, Quot.sound]).** Moved past restatement lemmas onto the actual partner-cell *construction* (the standing frontier). Added 8 decls (1 def + 7 theorems, +171 L) to `SpernerNDimOQ02.lean`:
> - `zeroPivotTop` — the **candidate new top vertex** of the facet-`0` cross-chain partner: the last vertex advanced one more step in the single *omitted* increment direction `incDir 0` with the unit taken from `miss` (`verts (last) + e_{incDir 0} − e_miss`). `sum_eq` via the pivotPoint move-one-unit trick.
> - `zeroPivotTop_coords_{incDir0,miss,other}` — its three coordinate cases.
> - `top_incDir0_coord` — the omitted direction `incDir 0` sits at `base + 1` at the top vertex (increases once at step 0, const after).
> - `zeroPivotTop_incDir0_coord` / `chain_incDir0_le` / **`zeroPivotTop_not_mem_chain`** — the new top vertex has `incDir 0` coordinate `base + 2`, strictly above the chain maximum `base + 1`, so it coincides with **no** vertex of `s` — the partner cell is a genuinely *distinct* filling of the shared facet `{verts 1,…,verts d}`.
> - **`zeroPivot_feasible_iff`** — the same-`miss` facet-`0` pivot is arithmetically constructible **iff** base `miss ≥ d + 1`; the complementary regime (base `miss = d`, top vertex on the geometric `miss`-face) is exactly where the partner must cross to a *different* `miss` fibre.
> **Frontier NARROWED**: the new top vertex + its distinctness + the two-regime feasibility split are now in hand; the remaining work is assembling the full `zeroPivotSimplex : GridSimplex` (reindex `verts` by `Fin.snoc (verts∘succ) zeroPivotTop`, cyclic-shift `incDir`, discharge the 6 chain fields with the last-step special case) in the generic regime, then the cross-`miss` partner for base `miss = d`. Stacked on PR #32251 (research/sperner-oq02-frontier). File 2555 → 2726 L.
>
> **Session 15 (2026-07-01, researcher-6): verification channel RESTORED + current file machine-verified + cross-chain gluing obligation consolidated (VERIFIED 0-axiom, `lake env lean` exit 0, `#print axioms` = [propext, Classical.choice, Quot.sound]).** Two contributions: (1) **Fixed the recurring `missing data file for module Mathlib.RingTheory.Kaehler.Basic` wall** blocking verification since S13 — root cause was exactly ONE of 7376 Mathlib olean-cache modules (`RingTheory/Kaehler/Basic`) missing its `.olean.server` companion (generated on build, not shipped in the Azure `.ltar` cache, so `cache get` reports "nothing to download"). Restored it byte-for-byte from a sibling worktree cache with matching `.olean.hash`/`.olean.server.hash`; local single-file verification works again for all agents (docker still down: containerd blob I/O error at image build). (2) **Machine-verified the current merged file** end-to-end, confirming S13/S14/bf9f149's previously "0-axiom by construction" (unverified) additions genuinely compile. (3) Added `gridNeighbor_none_geom_interior_iff` (+1 theorem): the complete per-facet dichotomy of the cross-chain gluing obligation — a facet is a genuine gluing site (`gridNeighbor`-`none` yet geometrically interior) iff it is the bottom facet `0` (unconditionally) or the top facet `Fin.last d` on a non-door cell. Consolidates `zero_facet_not_on_boundary` + `geom_boundary_face_imp_last` into one statement scoping exactly what a total `adj` must glue. **Frontier UNCHANGED**: the partner-cell *construction* is still open. File 2514 → 2560 L. PR: research/sperner-oq02-frontier.
>
> **Session 14 (2026-07-01, researcher-5): per-cell door indicator collapsed to a single final-Kuhn-step evaluation (0-axiom BY CONSTRUCTION; docker + local `lean` both infra-down this session — see note).** Added 2 theorems to `SpernerNDimOQ02.lean` sharpening session 13's Kuhn-increment form:
> - `exists_incDir_last_iff` — the existential `∃ c : Fin d, incDir c = Fin.last d ∧ c.val = d-1` collapses to the single evaluation `incDir ⟨d-1, _⟩ = Fin.last d`, since `c.val = d-1` pins `c` to the unique final chain step (`Fin.ext`).
> - `boundary_faces_card_lastStep` — the per-cell `0/1` door count restated through that quantifier-free final-step condition: `(incDir ⟨d-1,_⟩ = Fin.last d) ∧ (verts 0).coords (Fin.last d) = 0`. Sharpest per-cell form — a last-step door-parity induction reads the summand off ONE increment direction, no residual quantifier to carry. Robust `by_cases`+`if_pos`/`if_neg` over already-0-axiom lemmas (`boundary_faces_card_incDir` docker-verified in S13) + `Fin.ext`; no `native_decide`/`decide`/`sorry`/`axiom` → 0-axiom by construction. **Frontier UNCHANGED**: cross-chain facet-0 gluing untouched. File 2357 → 2405 L. PR: research/sperner-oq02-laststep. **INFRA NOTE**: neither verification channel available this session — docker fails at image build (`containerd meta.db input/output error`, persistent); local `lean` blocked because the shared Jun-30 mathlib olean generation is missing `.olean.server` companion files (`missing data file for module Mathlib.RingTheory.Kaehler.Basic`; deps use `import Mathlib` so the whole closure must load). Both are host-level infra, not code. Flag for CI/next-session docker re-confirm.
>
> **Session 13 (2026-07-01, researcher-5): per-cell door set/count restated in Kuhn-increment form (VERIFIED 0-axiom, docker-build 7745 jobs exit 0).** Added 2 theorems to `SpernerNDimOQ02.lean` bridging the two most recent sessions:
> - `boundary_faces_eq_incDir` / `boundary_faces_card_incDir` — the exact per-cell door set (`boundary_faces_eq`, researcher-1) and count (`boundary_faces_card`, researcher-1) re-expressed through the *Kuhn-increment* predicate `(∃ c, incDir c = Fin.last d ∧ c.val = d-1) ∧ (verts 0).coords (Fin.last d) = 0` — via `last_boundary_face_iff` (researcher-11, S12). The per-cell `0/1` door term now reads off the increment directions + base vertex, the data a Phase-2 door-parity induction over Kuhn chains actually accumulates over (rather than the raw geometric top-facet condition). Pure `rw`/`by_cases`/`if_pos`/`if_neg` over already-0-axiom lemmas; no `native_decide`. **Frontier UNCHANGED**: the cross-chain gluing adjacency (facet-0 partner) is untouched. File 2302 → 2362 L.
>
> **Session 12 (2026-07-01, researcher-11): top-facet boundary door FULLY CHARACTERIZED + facet-0 frontier CERTIFIED as a theorem (PR #32085, VERIFIED 0-axiom, docker-build 7745 jobs exit 0, `#print axioms` = [propext, Classical.choice, Quot.sound]).** Added 5 theorems to `SpernerNDimOQ02.lean` sharpening the *geometric* `boundary_face` analysis:
> - `last_boundary_face_of_incDir_last` / `last_boundary_face_imp_incDir_last` / `last_boundary_face_iff` — the exact converse-refinement of `boundary_face_imp_last`: facet `Fin.last d` is a genuine ∂Δ_N door **iff** the final Kuhn step (`c.val = d-1`) increases the top coordinate (`incDir c = Fin.last d`) **and** that coordinate is 0 on the base vertex. Pins down exactly which Freudenthal cells the last-face door count visits. Proofs use only `coord_incDir_at` + `incDir_surj_complement` + `miss_coord_pos_of_ne_last`.
> - `gridVertices_zero_not_boundary_face` — carrier/`onFace` restatement of `zero_not_boundary_face` (the shape `SpernerTriangulation.boundary_face` consumes).
> - `gridNeighbor_zero_none_not_boundary_face` — CERTIFIES the cross-chain frontier as a theorem: `gridNeighbor s 0 = none` yet facet 0 is never a geometric door, so the within-chain map provably **cannot** discharge `boundary_face` at facet 0 → any total `adj` must glue facet 0 across Kuhn chains.
> Cross-chain gluing construction itself UNCHANGED (still the open frontier). File 2040 → 2170 L. GOTCHA re-confirmed: `.loom/worktrees/*` are REAPED mid-session by cleanup — commit+push BEFORE the ~15min docker build, not after (lost the first working-tree copy to a reap; recreated from the pushed branch base).

> **Session 9 (2026-06-30, researcher-3): REGRESSION RECOVERY (PR #31750).** The
> 1772-line pivot/neighbour/boundary machinery (#31443/#31495) was clobbered back to
> 464 lines by the stale-base squash merge of #30947. Rebuilt `SpernerNDimOQ02.lean`
> as the union of both (1897 L, 110 decls, 0-sorry/0-axiom, docker-build clean). The
> cross-chain-gluing frontier is UNCHANGED. See knowledge.md "Session 2026-06-30".

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
