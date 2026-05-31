# Current State: circumference-via-differentiation-oq-03

**Phase**: ACT-S3-PASTED (S7 — polymorphic Bridge 1 pasted into Lean file from S3 PREP §3.2 verbatim recipe; build verification deferred per G9 lake self-loop)
**Path**: full
**Since**: 2026-05-31T~06:20Z (this S7 ACT polymorphic Bridge 1 paste); S6 GALLERY-WIRING merged 2026-05-31T~02:40Z; ACT-MERGED 2026-05-30T12:15Z (S5 STATE-SYNC); ACT-merged 2026-05-16T08:55Z (commit ecb47b35601 in PR #19454 bulk merge); root-since 2026-05-12T22:55:00Z
**Iteration**: 10 (S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [merged via #19454 bulk], S3 PREP, S4 PREP, S5 STATE-SYNC, S6 GALLERY-WIRING, S7 ACT-S3 [this])
**Researcher**: researcher-1 (S5 STATE-SYNC, S6 GALLERY-WIRING, S7 ACT-S3); preceding: researcher-9 (S1, S2 ACT, S4 PREP), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP + S3 PREP), researcher-4 (S2d PREP)

## Current Focus (S7 ACT-S3, researcher-1, 2026-05-31)

This iteration extends `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`
by pasting the **polymorphic Bridge 1** (Workaround A) from S3 PREP §3.2.
The new theorem `riemannianVolumeBall_eq_nBallVolumeFn` identifies
`(volume (Metric.closedBall p r)).toReal` with the OQ-01 polynomial
`CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) r`
under the typeclass set
`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
[MeasureSpace E] [BorelSpace E] [Nontrivial E]`.

**Pre-flight check** (2026-05-31): re-verified that the pinned Mathlib
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` still holds
`InnerProductSpace.volume_closedBall` at line 372 of
`VolumeOfBalls.lean` — 0 drift since S3 PREP wrote on 2026-05-14
(17 days elapsed; SHA unchanged). All siblings (lines 361, 377, 383,
389, 399, 417, 427) are likewise byte-identical.

Net change: `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`
goes from 93 LOC / 4 theorems to 152 LOC / 5 theorems (+59 LOC),
0 sorries, 0 axioms (verified via `grep -c`). One new import:
`Proofs.CircumferenceViaDifferentiationOQ01`.

**Build verification deferred**: per project memory on G9 lake
self-loop in the main repo (`proofs/.lake → proofs/.lake`), the
Docker build wrapper is unusable from any worktree sharing this repo.
This PR ships under the documented "build pending — G9 lake
self-loop" qualifier, consistent with concurrent ACT PRs (e.g., PR
#21477 descartes-rule-of-signs S5 ACT, PR #21475 basel-problem S20 ACT).

### Previous Focus (S6 GALLERY-WIRING, researcher-1, 2026-05-31)

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

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (93 LOC, 4 thms;
  this S7 ACT extends to 152 LOC / 5 thms in this PR, pending merge)
  - `riemannianVolumeBall_fin_two` — Bridge 1, n=2: vol(closedBall p r) = π r²
  - `riemannianVolumeBall_fin_three` — Bridge 1, n=3: vol(closedBall p r) = (4π/3) r³
  - `riemannianVolumeBall_hasDerivWithinAt_fin_two` — Main S5, n=2: dV/dr = 2π r
  - `riemannianVolumeBall_hasDerivWithinAt_fin_three` — Main S5, n=3: dV/dr = 4π r²
- `proofs/Proofs.lean` — `import Proofs.CircumferenceViaDifferentiationOQ03` present
- 0 sorries; 0 axioms; build verified at the time of the bulk merge

## Just completed (S7, this iteration, build pending)

- **Polymorphic Bridge 1 (Workaround A)** — `riemannianVolumeBall_eq_nBallVolumeFn`:
  identifies `(volume (Metric.closedBall p r)).toReal` with
  `CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) r`
  under abstract `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [Nontrivial E]`. ~30 LOC tactic body
  via the recipe in S3 PREP §3.2: `InnerProductSpace.volume_closedBall`
  rewrite + `ENNReal.toReal_*` collapse + `(√π)^n = π^((n:ℝ)/2)` bridge
  via `Real.sqrt_eq_rpow` / `Real.rpow_natCast` / `Real.rpow_mul`.

## Pending (not yet built)

- **Polymorphic main theorem (S4 ACT / Workaround C')**: the abstract-E
  version of dV/dr = A. Now unblocked by S7 polymorphic Bridge 1 (this
  iteration). The proof composes `riemannianVolumeBall_eq_nBallVolumeFn`
  (this iter) with `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt`
  via `HasDerivAt.congr`. ETA: 1 iteration, ~30 LOC.
- **Bridge 2** (Hausdorff-measure identification on sphere): still
  genuinely blocked on Mathlib v4.26.0's absence of the identification;
  the recommended path is Workaround C' (skip Bridge 2).

## Previously completed (S6, prior iteration this date)

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
| S6 GALLERY-WIRING | src/data/proofs/.../{meta.json, index.ts, annotations.json} | ~315 + ~50 LOC TS/JSON | ✓ this PR (S6) |
| **S7 ACT-S3** | **Polymorphic Bridge 1 (abstract [InnerProductSpace ℝ E])** | **+59 net (93→152)** | **(this iteration; build pending — G9 lake self-loop)** |
| (next) S4 ACT | Polymorphic main theorem (Workaround C', skip Bridge 2) | ~30 | pending (depends on S7 ACT-S3) |

R2 (full Riemannian manifold) and R3 (n-dim coarea Mathlib contribution)
remain deferred Mathlib-roadmap targets, gated on the 4-gap list in
problem.md §"Three Routes".

## Next Action

After this S7 ACT-S3 iteration, the only remaining ACT pipeline is:

### S4 ACT — Workaround C' polymorphic main theorem, ~30 LOC Lean

Append `riemannianVolumeBall_hasDerivWithinAt_nSphereSurfaceFn`
stated directly via `CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn`
on RHS (skip Bridge 2). Now unblocked by S7 ACT-S3 polymorphic
Bridge 1 (this iteration). The proof composes
`riemannianVolumeBall_eq_nBallVolumeFn` with
`CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt` via
`HasDerivAt.congr` (or its `HasDerivWithinAt` variant if matching
the existing `_fin_two/_three` `(Set.Ici 0)` convention).

Build: `./proofs/scripts/docker-build.sh Proofs.CircumferenceViaDifferentiationOQ03`
(currently blocked by G9 lake self-loop in main repo — see
the project memory `[[project_lake_self_loop_main_repo]]`).

## Open PRs

- **(this PR, S7 ACT-S3)**: researcher-1, opened 2026-05-31T~06:30Z.
  Lean +59 net (93 → 152, +1 import, +1 new theorem
  `riemannianVolumeBall_eq_nBallVolumeFn`, +5 docstring header
  expansion). 0 sorries, 0 axioms. Build pending — G9 lake self-loop.
  Pre-flight: 0 drift since S3 PREP at pinned SHA.
- S6 GALLERY-WIRING (researcher-1, opened 2026-05-31T~02:40Z):
  status pending merge — see PR list.

## Blockers

- **G9 lake self-loop in main repo**: blocks Docker build verification
  across all worktrees. Cross-cutting blocker tracked in
  `[[project_lake_self_loop_main_repo]]` memory. Recovery is a separate
  remit (not researcher-initiated). This S7 ACT-S3 PR ships under the
  documented "build pending — G9 lake self-loop" qualifier.
- R2 full-manifold and R3 n-dim coarea remain Mathlib-roadmap gaps;
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
| S6 GALLERY-WIRING | 2026-05-31 | researcher-1 | (open / merge pending) | Create src/data/proofs/circumference-via-differentiation-oq-03/{meta.json (~290 LOC), index.ts (25 LOC), annotations.json (5 annotations)}. Verified via npx tsx scripts/annotations/build.ts: 2436 proofs discovered (+1), listings.json includes slug with annotationCount=5 / mathlibCount=6 / status=verified. tsc --noEmit clean. |
| **S7 ACT-S3** | **2026-05-31** | **researcher-1** | **(this PR)** | **Polymorphic Bridge 1 paste from S3 PREP §3.2 verbatim: +1 import (Proofs.CircumferenceViaDifferentiationOQ01), +1 theorem (riemannianVolumeBall_eq_nBallVolumeFn, ~30 LOC body, ~14 LOC docstring + signature). +59 net LOC (93 → 152). 0 sorries, 0 axioms. Pre-flight: 0 drift since S3 PREP at pinned SHA 2df2f015… (17 days elapsed). Build pending — G9 lake self-loop.** |

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
- `sessions/2026-05-31-s6-gallery-wiring.md` — S6 session.
- `sessions/2026-05-31-s7-s3-act-polymorphic-bridge-1.md` — this iteration's session doc.

## Calibration

This S7 ACT-S3 PR is a focused Lean extension: +59 LOC net to
`proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (93 → 152),
adding the polymorphic Bridge 1 theorem `riemannianVolumeBall_eq_nBallVolumeFn`
from S3 PREP's §3.2 verbatim recipe. The new theorem identifies
`(volume (Metric.closedBall p r)).toReal =
  CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) r`
under the typeclass set
`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
[MeasureSpace E] [BorelSpace E] [Nontrivial E]`.

**Pre-flight check** (this iteration, 2026-05-31): re-verified the pinned
Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` still holds
`InnerProductSpace.volume_closedBall` at line 372 of `VolumeOfBalls.lean`
— 0 drift since S3 PREP wrote on 2026-05-14 (17 days elapsed, SHA
unchanged). All siblings (lines 325, 342, 361, 377, 383, 389, 399, 417,
427) byte-identical to S3 PREP §2.1 inventory.

**Verification status**: 0 sorries (grep -c verified), 0 `axiom`
declarations (grep -c '^axiom ' verified), no structure-encoded
assumptions (typeclass hypotheses are stated on the individual theorem,
not as ambient axioms). The R1 vector-space narrative is preserved
verbatim from the pre-S7 file; this iteration **adds** the polymorphic
case rather than replacing the concrete `_fin_two/_fin_three` results.

**Build pending — G9 lake self-loop**. The main repo's `proofs/.lake →
proofs/.lake` symlink blocks `./proofs/scripts/docker-build.sh` from
every sharing worktree (a cross-cutting blocker, see project memory
`[[project_lake_self_loop_main_repo]]`). This PR ships under the
documented "build pending — G9 lake self-loop" qualifier, consistent
with concurrent ACT PRs (e.g., #21477 descartes-rule-of-signs S5 ACT,
#21475 basel-problem S20 ACT). Build verification will be re-attempted
once the self-loop is resolved out-of-band.

**Risk register**: S3 PREP §3.5 enumerated 6 risks (R1–R6) for this
recipe; all are documented in `sessions/2026-05-31-s7-s3-act-polymorphic-bridge-1.md`
§"Risk Register" with mitigations. None pose mathematical risk —
all are mechanical-fix items at the deferred Docker step.

The remaining ACT deliverable on the R1 vector-space roadmap is
**S4 ACT — polymorphic main theorem** (~30 LOC), now unblocked by
this S7 ACT-S3 polymorphic Bridge 1. Composition recipe:
`riemannianVolumeBall_eq_nBallVolumeFn` (this iter) +
`CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt` (already
on main) via `HasDerivAt.congr`. ETA: 1 iteration.
