# S6 Gallery Wiring — circumference-via-differentiation-oq-03

**Date**: 2026-05-31
**Researcher**: researcher-1
**Mode**: REVISIT (continuing iteration on RICH-knowledge problem; KS=30 at claim)
**Outcome**: progress — gallery wiring delivered, OQ-03 entry now visible in the gallery

## Goal

Discharge the (a) Gallery wiring deliverable from the three-way next-action menu
(see `state.md` §"Next Action"). The Lean file
`proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` has been on `main`
since the 2026-05-16 #19454 bulk merge (93 LOC, 4 theorems, 0 sorries,
0 axioms), but the gallery-side data directory
`src/data/proofs/circumference-via-differentiation-oq-03/` did not yet
exist, so the proof was not discoverable through the website's auto-glob
mechanism.

## What I Did

1. **Verified ground truth on main**:
   - `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`: 93 LOC, 4 theorems
     (`riemannianVolumeBall_fin_two`, `_fin_three`,
     `riemannianVolumeBall_hasDerivWithinAt_fin_two`, `_fin_three`), 0 sorries,
     0 axioms. Confirmed via `wc -l` + grep.
   - `proofs/Proofs.lean` imports it. Confirmed via grep.
   - `src/data/proofs/circumference-via-differentiation-oq-03/` does NOT exist
     (confirmed via `ls`).

2. **Inspected the OQ-01 sibling template** (`src/data/proofs/circumference-via-differentiation-oq-01/`):
   - `meta.json` — 185 lines; full title/description/sections/overview/conclusion blocks
   - `index.ts` — 25 lines; standard Proof/Annotation re-export shape
   - `annotations.json` — 189 lines; 8 section annotations

3. **Verified the discovery mechanism** (`scripts/annotations/build.ts` lines 126-188):
   - `discoverProofs()` enumerates `src/data/proofs/*/` directories
   - Each must contain `meta.json` (required) plus optional `annotations.json`,
     `annotations.source.json`, `index.ts`
   - `proofRepoPath` in `meta.json.meta` points back to the Lean file
   - The site's `src/data/proofs/index.ts` uses Vite glob `./**/index.ts` to
     auto-register modules at build time
   - No central registry edit needed; creating the three files is sufficient

4. **Created three gallery files** under `src/data/proofs/circumference-via-differentiation-oq-03/`:
   - `meta.json` (~290 LOC including overview/conclusion/sections/crossReferences):
     - `status: verified`, `badge: original`, `sorries: 0`, `axiomCount: 0`
     - `lineCount: 93`, `theoremCount: 4`, `definitionCount: 0`
     - `proofRepoPath: Proofs/CircumferenceViaDifferentiationOQ03.lean`
     - 6 `mathlibDependencies` (`EuclideanSpace.volume_closedBall_fin_two/three`,
       `hasDerivAt_pow`, `HasDerivWithinAt.congr`, `ENNReal.toReal_mul`,
       `ENNReal.toReal_ofReal`)
     - 4 `originalContributions` (intrinsic statement via `EuclideanSpace.volume_closedBall`,
       ENNReal toReal-chain technique, Workaround C `Set.Ici 0` form, first
       gallery use of the volume_closedBall_fin_n family in derivative form)
     - 5-section `sections` array with line-ranges 1-45, 47-55, 57-65, 67-78, 80-92
     - Full `overview` block: historicalContext (Federer 1959), problemStatement,
       proofStrategy (two-stage bridge + congr), 6 keyInsights, prerequisites
     - Full `conclusion` block: summary, implications, 5 openQuestions covering
       polymorphic Bridge 1, Workaround C' polymorphic main, Bridge 2 absence,
       full R2 Riemannian, R3 standalone n-dim coarea
     - 2 `crossReferences`: parent `circumference-via-differentiation` and
       sibling `circumference-via-differentiation-oq-01`
     - `dateAdded: 2026-05-31`, `mathlib_version: 4.26.0`
   - `index.ts` (25 LOC): standard Proof/Annotation re-export module
   - `annotations.json` (5 annotations): one per major proof region — header
     (1-45), Bridge 1 n=2 (47-55), Bridge 1 n=3 (57-65), Main n=2 (67-78),
     Main n=3 (80-92). Each has type (concept/technique/insight), significance
     (key/supporting), relatedConcepts, prerequisites, and mathContext.

5. **Validated**:
   - `jq empty meta.json && jq empty annotations.json` — both parse
   - `jq '. | length' annotations.json` returns `5`
   - Ran `npx tsx scripts/annotations/build.ts`:
     - Discovered 2436 proofs (one more than before)
     - Built git touch map: 13349 paths in 9.7s
     - Generated `listings.json` (2436 proofs, 1819 KB)
   - `jq '.[] | select(.slug == "circumference-via-differentiation-oq-03")' listings.json`
     returns the expected entry with `status: verified`, `sorries: 0`,
     `annotationCount: 5`, `mathlibCount: 6`, `updatedAt: 2026-05-16T01:55:07-07:00`
     (the Lean file's last touch)
   - `npx tsc --noEmit -p tsconfig.json` — exit 0, no errors

## Files Modified

- `src/data/proofs/circumference-via-differentiation-oq-03/meta.json` (NEW, ~290 LOC)
- `src/data/proofs/circumference-via-differentiation-oq-03/index.ts` (NEW, 25 LOC)
- `src/data/proofs/circumference-via-differentiation-oq-03/annotations.json` (NEW, 5 annotations)
- `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-31-s6-gallery-wiring.md` (this file)
- `research/problems/circumference-via-differentiation-oq-03/state.md` (updated)
- `src/data/research/problems/circumference-via-differentiation-oq-03.json` (updated cursor)

## Key Findings

- **The discovery mechanism is fully auto-glob** (Vite `import.meta.glob('./**/index.ts')`
  in `src/data/proofs/index.ts`). No central registry to update. Creating the
  three files in `src/data/proofs/<slug>/` is the entire gallery-wiring deliverable.
- **`listings.json` is build-generated** (`scripts/annotations/build.ts:294-379`).
  It enumerates `src/data/proofs/*/meta.json` and projects out the lightweight
  fields for the HomePage gallery. The build also generates
  `public/data/proofs/<slug>/source.lean` (gitignored) which the runtime fetches
  lazily; on a deploy the deploy pipeline runs `pnpm build` which regenerates it.
- **`updatedAt` is set by build-time git log** (`scripts/annotations/build.ts:344-354`)
  to the most-recent commit touching either the data directory or the Lean
  file. For our entry, this resolves to `2026-05-16T01:55:07-07:00` — the
  bulk-merge commit when the Lean file landed. The data-directory creation
  in this PR will refresh this on the next build after merge.
- **The `volume_closedBall_fin_n` family is the right Mathlib primitive** for
  this style of intrinsic statement. It produces an ENNReal equation that the
  `.toReal` chain converts cleanly to the parent's Real-valued polynomial form.

## Next Steps

The three pending ACT pipelines from `state.md` reduce to two after this PR:

- **(b) S3 ACT polymorphic Bridge 1** (~50 LOC Lean): extend OQ03 Lean file
  with `riemannianVolumeBall_eq_nBallVolumeFn` under `[NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Nontrivial E]`. Pre-flight check needed: re-verify
  `InnerProductSpace.volume_closedBall` line citation at the current
  lake-pinned Mathlib SHA. Build via Docker.
- **(c) S4 ACT Workaround C' polymorphic main** (~60 LOC Lean): append
  polymorphic main theorem `riemannianVolumeBall_hasDerivWithinAt_nSphereSurfaceFn`
  stated directly via `CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn`.
  Depends on (b).

R2 (full Riemannian) and R3 (n-dim coarea) remain deferred Mathlib-roadmap
targets.

## Honesty / Calibration

This deliverable is purely **doc + gallery wiring** — no Lean code modified,
no Docker build needed. The OQ-03 entry was always *eligible* for the gallery
once the Lean file landed in May; this PR just creates the website-side
manifestation. Marketing-style claims about "newly verified results" would be
inaccurate; the verification has been on main for two weeks. What's new is
*discoverability* via the website's HomePage gallery and the proof page route.

The gallery entry's `status: verified` is accurate per the
[Axiom Integrity Policy](../../../../CLAUDE.md): 0 sorries, 0 `axiom` declarations, 0
structure-encoded assumptions in the Lean file. The `originalContributions`
list is honest about scope (n = 2, 3 only — the polymorphic version is
explicitly called out as future work in `openQuestions`).

The `keyInsights` and `openQuestions` blocks summarize the substantial
S1-S5 prior-art research from `knowledge.md`; no new mathematical claims
are introduced.
