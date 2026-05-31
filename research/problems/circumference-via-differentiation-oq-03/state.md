# Current State: circumference-via-differentiation-oq-03

**Phase**: ACT-GALLERY-WIRED (S6 — gallery entry created; S3 ACT polymorphic Bridge 1 + S4 ACT Workaround C' remain as next ACT pipelines)
**Path**: full
**Since**: 2026-05-31T~02:40Z (this S6 gallery wiring); ACT-MERGED 2026-05-30T12:15Z (S5 STATE-SYNC); ACT-merged 2026-05-16T08:55Z (commit ecb47b35601 in PR #19454 bulk merge); root-since 2026-05-12T22:55:00Z
**Iteration**: 9 (S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [merged via #19454 bulk], S3 PREP, S4 PREP, S5 STATE-SYNC, S6 GALLERY-WIRING [this])
**Researcher**: researcher-1 (S5 STATE-SYNC, S6 GALLERY-WIRING); preceding: researcher-9 (S1, S2 ACT, S4 PREP), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP + S3 PREP), researcher-4 (S2d PREP)

## Current Focus (S6 GALLERY-WIRING, researcher-1, 2026-05-31)

The gallery entry `src/data/proofs/circumference-via-differentiation-oq-03/`
has been **created**. The proof page route is now discoverable via the
website's auto-glob mechanism (`src/data/proofs/index.ts`); the build-time
`scripts/annotations/build.ts` `generateListings()` step now emits this
slug into `listings.json` (verified: `annotationCount: 5`, `mathlibCount: 6`,
`status: verified`, `sorries: 0`, `updatedAt: 2026-05-16T01:55:07-07:00`).

Three new files under `src/data/proofs/circumference-via-differentiation-oq-03/`:

- `meta.json` (~290 LOC): full proof meta with overview, conclusion, 5 sections,
  6 mathlib dependencies, 4 original-contributions, 2 cross-references
  (parent + sibling OQ-01), 5 open-questions (next ACT pipelines + Mathlib roadmap)
- `index.ts` (25 LOC): standard Proof/Annotation re-export module
- `annotations.json` (5 annotations): header, Bridge 1 n=2, Bridge 1 n=3,
  Main n=2, Main n=3

The Lean file (`proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`,
93 LOC, 4 theorems, 0 sorries, 0 axioms) is unchanged. The
`status: verified` claim in the new `meta.json` is honest per the Axiom
Integrity Policy: 0 sorries, 0 `axiom` declarations, 0 structure-encoded
assumptions in the Lean file.

Net change in this PR: 3 NEW gallery files + 2 doc files (this state.md
update + the new sessions/2026-05-31-s6-gallery-wiring.md) + JSON cursor
refresh. **No Lean modification. No Docker build needed.**

### Previous Focus (S5 STATE-SYNC, researcher-1, 2026-05-30)

The Lean S2 ACT deliverable (n=2 and n=3 Euclidean partial) landed on main as
`proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (93 lines, 4 theorems,
0 sorries, 0 axioms) via the #19454 bulk merge (commit `ecb47b35601`, dated
2026-05-16). PR #18985 (researcher-9, 2026-05-14) was CLOSED; its code was
absorbed into the bulk.

## Verified Deliverables on main (as of 2026-05-30T12:15Z)

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (93 LOC, 4 thms)
  - `riemannianVolumeBall_fin_two` — Bridge 1, n=2: vol(closedBall p r) = π r²
  - `riemannianVolumeBall_fin_three` — Bridge 1, n=3: vol(closedBall p r) = (4π/3) r³
  - `riemannianVolumeBall_hasDerivWithinAt_fin_two` — Main S5, n=2: dV/dr = 2π r
  - `riemannianVolumeBall_hasDerivWithinAt_fin_three` — Main S5, n=3: dV/dr = 4π r²
- `proofs/Proofs.lean` — `import Proofs.CircumferenceViaDifferentiationOQ03` present
- 0 sorries; 0 axioms; build verified at the time of the bulk merge

## Pending (not yet built)

- **Polymorphic Bridge 1**: the abstract `[InnerProductSpace ℝ E]` version
  (Workaround A) — documented in S3 PREP #19136 as a ~50-LOC tactic chain —
  is not yet in the Lean file.
- **Polymorphic main theorem**: the abstract-E version of dV/dr = A
  (Workaround C', skipping Bridge 2 by stating RHS directly via
  `nSphereSurfaceFn`).
- **Bridge 2** (Hausdorff-measure identification on sphere): still
  genuinely blocked on Mathlib v4.26.0's absence of the identification;
  the recommended path is Workaround C' (skip Bridge 2).

## Just completed (S6, this iteration)

- **Gallery wiring**: `src/data/proofs/circumference-via-differentiation-oq-03/`
  CREATED. The OQ-03 deliverable is now visible in the gallery via the
  auto-glob discovery mechanism in `src/data/proofs/index.ts`.

## Path to Verification (R1 vector-space route, updated)

| Stage | Deliverable | Lines | Status |
|-------|-------------|-------|--------|
| S1 | OBSERVE survey (text-only) | — | ✓ merged (#18362) |
| S2 PREP+ACT | n=2, n=3 Euclidean partial Lean (4 theorems, Docker verified) | 93 | **✓ on main via #19454 bulk** |
| S3 PREP | Mathlib availability erratum (polymorphic Bridge 1 unblocked) | doc | ✓ merged (#19136) |
| S4 PREP | Deployer-stall coordination + 3-way merge resolution doc | doc | ✓ merged (#19205) |
| S5 STATE-SYNC | post-S2-ACT-landing reconciliation (merged) | doc | ✓ merged |
| **S6 GALLERY-WIRING** | **src/data/proofs/.../{meta.json, index.ts, annotations.json} (THIS PR)** | **~315 + ~50 LOC TS/JSON** | **(this iteration)** |
| (next) S3 ACT | Polymorphic Bridge 1 (abstract [InnerProductSpace ℝ E]) | ~50 | pending |
| (next) S4 ACT | Polymorphic main theorem (Workaround C', skip Bridge 2) | ~60 | pending (depends on S3 ACT) |

R2 (full Riemannian manifold) and R3 (n-dim coarea Mathlib contribution)
remain deferred Mathlib-roadmap targets, gated on the 4-gap list in
problem.md §"Three Routes".

## Next Action

Two pending ACT pipelines remain after this S6 iteration:

### (b) S3 ACT — polymorphic Bridge 1, ~50 LOC Lean

Extend OQ03 Lean file with `riemannianVolumeBall_eq_nBallVolumeFn`
under `[NormedAddCommGroup E] [InnerProductSpace ℝ E]
[FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]`.
Proof body: `InnerProductSpace.volume_closedBall` rewrite + ENNReal.toReal
chain + `(√π)^n = π^((n:ℝ)/2)` bridge (see S3 PREP #19136 §3.2).

**Pre-flight check needed**: re-verify
`InnerProductSpace.volume_closedBall` line citation at the current
lake-pinned Mathlib SHA — two weeks elapsed since S3 PREP wrote
line 372, drift expected.

Build: `./proofs/scripts/docker-build.sh Proofs.CircumferenceViaDifferentiationOQ03`.

### (c) S4 ACT — Workaround C' polymorphic main, ~60 LOC Lean

Append `riemannianVolumeBall_hasDerivWithinAt_nSphereSurfaceFn`
stated directly via `CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn`
on RHS (skip Bridge 2). Depends on (b) Bridge 1.

Each is a single researcher iteration.

## Open PRs

- **(this PR, S6 GALLERY-WIRING)**: researcher-1, opened
  2026-05-31T~02:40Z. Doc + gallery wiring only (no Lean). Mergeable; no
  Docker build needed.

No other open OQ-03 PRs (as of 2026-05-31T02:40Z).

## Blockers

None for R1 (vector-space) S2-S5 deliverables. Pre-flight Mathlib
line-drift verification recommended before S3 ACT (b).

R2 full-manifold and R3 n-dim coarea remain Mathlib-roadmap gaps;
unchanged from S1 OBSERVE assessment.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-9 | #18362 (merged) | OBSERVE survey: 4 files; no Lean changes |
| S2 PREP | 2026-05-13 | researcher-N | #18458 (merged) | Mathlib bridge audit + Lean skeleton; doc-only |
| S2b PREP | 2026-05-13 | researcher-N | #18575 (merged) | Bridge 1 LOC tightening + Workaround-C dim lemmas; doc-only |
| S2c PREP | 2026-05-13 | researcher-12 | #18615 (merged) | Bridge 1 toReal-chain correction + HasDerivWithinAt(Set.Ici 0) refinement; doc-only |
| S2d PREP | 2026-05-13 | researcher-4 | #18691 (merged) | Audit-correction of S2c `.symm` direction; doc-only |
| S2 ACT | 2026-05-14 | researcher-9 | #18985 (CLOSED; absorbed into #19454 bulk) | R1 Euclidean n=2,3 partial: +93 LOC, 4 thms, 0 sorries, 0 axioms |
| S3 PREP | 2026-05-14 | researcher-12 | #19136 (merged) | Workaround A Mathlib availability erratum; doc-only |
| S4 PREP | 2026-05-15 | researcher-9 | #19205 (merged) | Deployer-stall coordination + 3-way merge resolution; doc-only |
| (bulk merge) | 2026-05-16 | (operator) | #19454 | Lean OQ03 file landed on main via bulk-merge commit ecb47b35601 |
| S5 STATE-SYNC | 2026-05-30 | researcher-1 | (merged) | Post-S2-ACT-landing doc reconciliation: state.md + JSON cursor → ACT-MERGED; doc-only. |
| **S6 GALLERY-WIRING** | **2026-05-31** | **researcher-1** | **(this PR)** | **Create src/data/proofs/circumference-via-differentiation-oq-03/{meta.json (~290 LOC), index.ts (25 LOC), annotations.json (5 annotations)}. Verified via npx tsx scripts/annotations/build.ts: 2436 proofs discovered (+1), listings.json includes slug with annotationCount=5 / mathlibCount=6 / status=verified. tsc --noEmit clean.** |

## Reference Files (in this directory)

- `problem.md` — formal target, classification, three-route
  classification, Mathlib infrastructure map, numerical sanity,
  anti-targets, references. ~520 lines. Unchanged this iteration.
- `knowledge.md` — S1 session summary, mathematical background,
  Mathlib API surface, Lean skeleton sketch, risk register, S∞
  roadmap, S6+ stretch notes. ~350 lines. Unchanged this iteration.
- `sessions/2026-05-12-...` through `sessions/2026-05-15-...` —
  six prior session documents from S2 PREP through S4 PREP.
- `sessions/2026-05-30-s5-state-sync-post-s2-act-landing.md` — S5 session.
- `sessions/2026-05-31-s6-gallery-wiring.md` — this iteration's session doc.

## Calibration

This S6 GALLERY-WIRING is doc + gallery only — no Lean modifications, no
Docker build. Verifies via `npx tsx scripts/annotations/build.ts`:

- `src/data/proofs/circumference-via-differentiation-oq-03/{meta.json,
  index.ts, annotations.json}` exist and parse cleanly (jq + tsc)
- `discoverProofs()` finds 2436 entries (one more than the pre-S6 count)
- `listings.json` includes the slug with the expected projections
  (status verified, sorries 0, annotationCount 5, mathlibCount 6,
  updatedAt 2026-05-16T01:55:07-07:00 from the Lean file's last touch)
- The proof page route is now discoverable via the website's auto-glob

The R1 vector-space narrative is unchanged from S1 OBSERVE; what has
changed is the **discoverability** of the verified Lean deliverable
through the website. The next concrete deliverable on the roadmap is
**(b) S3 ACT polymorphic Bridge 1** (~50 LOC Lean), which would replace
the n = 2, 3 hardcoded cases with a single general theorem under
`[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`. The pre-flight check
is to re-verify `InnerProductSpace.volume_closedBall` line citation at
the current lake-pinned Mathlib SHA — two-week-plus line drift expected
since S3 PREP wrote line 372 of `VolumeOfBalls.lean`.
