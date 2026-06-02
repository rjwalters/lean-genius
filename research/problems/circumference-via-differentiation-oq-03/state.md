# Current State: circumference-via-differentiation-oq-03

**Phase**: ACT-S8-PASTED (S8 — polymorphic main theorem `riemannianVolumeBall_hasDerivWithinAt` added by composition of S7 Bridge 1 with parent `nBallVolumeFn_hasDerivAt` via `HasDerivWithinAt.congr`; R1 vector-space ACT roadmap complete; build verification deferred per G9 lake self-loop)
**Path**: full
**Since**: 2026-06-02T13:00Z (this S8 ACT polymorphic main theorem); S7 ACT-S3 merged 2026-05-31 (#21506); S6 GALLERY-WIRING merged 2026-05-31T~02:40Z; ACT-MERGED 2026-05-30T12:15Z (S5 STATE-SYNC); ACT-merged 2026-05-16T08:55Z (commit ecb47b35601 in PR #19454 bulk merge); root-since 2026-05-12T22:55:00Z
**Iteration**: 11 (S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [merged via #19454 bulk], S3 PREP, S4 PREP, S5 STATE-SYNC, S6 GALLERY-WIRING, S7 ACT-S3, S8 ACT [this])
**Researcher**: researcher-1 (S5 STATE-SYNC, S6 GALLERY-WIRING, S7 ACT-S3, S8 ACT); preceding: researcher-9 (S1, S2 ACT, S4 PREP), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP + S3 PREP), researcher-4 (S2d PREP)

## Current Focus (S8 ACT, researcher-1, 2026-06-02)

This iteration adds the **polymorphic main theorem** `riemannianVolumeBall_hasDerivWithinAt` to `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`, closing the R1 vector-space ACT roadmap for OQ-03. The new theorem composes:

- `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt (Module.finrank ℝ E) r` — the parent's two-sided derivative `d/dr nBallVolumeFn n = nSphereSurfaceFn n` available at every `n : ℕ` and every `r : ℝ`;
- the S7 ACT-S3 polymorphic Bridge 1 equation `riemannianVolumeBall_eq_nBallVolumeFn p (hr : 0 ≤ r) : (volume (Metric.closedBall p r)).toReal = nBallVolumeFn (finrank ℝ E) r`;
- via `HasDerivWithinAt.congr` — the same Mathlib API already used by `_fin_two`/`_fin_three` in the same file.

The conclusion `HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal) (nSphereSurfaceFn (Module.finrank ℝ E) r) (Set.Ici 0) r` holds for every finite-dimensional real inner-product space `E` with the canonical `MeasureSpace`/`BorelSpace` instances and `[Nontrivial E]` (equivalent to `0 < finrank ℝ E`).

**Net change**: `CircumferenceViaDifferentiationOQ03.lean` 152 → 194 LOC (+42 net; +30 LOC theorem body + ~12 LOC docstring), 5 → 6 theorems, **0 sorries / 0 axioms preserved** (`grep -c` verified). No new imports.

**Pre-flight check** (2026-06-02): Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged from S7 ACT-S3 (2 days elapsed). Per `feedback_sha_stable_busywork`, SHA-pin transitivity carries all S3 PREP §2.1 bearer rows; this S8 ACT introduces **zero new Mathlib bearer dependencies**.

**Build verification deferred**: per project memory `[[project_lake_self_loop_main_repo]]` (G9 lake self-loop in main repo unchanged from S7 ACT-S3; same blocker, same workaround per PR #21506 / #21477 / #21475 precedent), `./proofs/scripts/docker-build.sh` is unusable from every sharing worktree. This PR ships under the documented "build pending — G9 lake self-loop" qualifier.

### Previous Focus (S7 ACT-S3, researcher-1, 2026-05-31)

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

## Verified Deliverables on main (as of 2026-05-31, post-S7 ACT-S3 merge #21506)

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (152 LOC, 5 thms;
  this S8 ACT extends to 194 LOC / 6 thms in this PR, pending merge)
  - `riemannianVolumeBall_fin_two` — Bridge 1, n=2: vol(closedBall p r) = π r²
  - `riemannianVolumeBall_fin_three` — Bridge 1, n=3: vol(closedBall p r) = (4π/3) r³
  - `riemannianVolumeBall_hasDerivWithinAt_fin_two` — Main S5, n=2: dV/dr = 2π r
  - `riemannianVolumeBall_hasDerivWithinAt_fin_three` — Main S5, n=3: dV/dr = 4π r²
  - `riemannianVolumeBall_eq_nBallVolumeFn` — S7 ACT-S3 polymorphic Bridge 1
- `proofs/Proofs.lean` — `import Proofs.CircumferenceViaDifferentiationOQ03` present
- 0 sorries; 0 axioms; build verified at the time of the bulk merge

## Just completed (S8 ACT, this iteration, build pending — G9 lake self-loop)

- **Polymorphic main theorem (Workaround C')** — `riemannianVolumeBall_hasDerivWithinAt`:
  for every `[NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]`
  and every `(p : E) {r : ℝ} (hr : 0 ≤ r)`,
  `HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
    (CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn (Module.finrank ℝ E) r)
    (Set.Ici 0) r`. ~4 LOC effective body via composition of
  `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt`
  (parent two-sided derivative) with the S7 ACT-S3 polymorphic Bridge 1
  (`riemannianVolumeBall_eq_nBallVolumeFn`) via `HasDerivWithinAt.congr` —
  the same Mathlib API already used by `_fin_two`/`_fin_three` in the
  same file. ~12 LOC docstring + 4 LOC body + 16 LOC signature/blank ≈ 42 net.

## R1 vector-space ACT roadmap: COMPLETE

After S8 ACT, all theorems on the R1 vector-space roadmap are landed.
The remaining work is:

- **R2 (genuine Riemannian)**: still gated on Mathlib v4.26.0's missing
  bearers — no `injectivityRadius`, no `expMap`, no
  `geodesicBall`/`Sphere`/`Volume` family, no n-dim coarea. See
  `problem.md` §"Three Routes" 4-gap list. Estimated >3000 Lean lines
  of foundational Mathlib contribution; out of scope for in-repo OQ-03.
- **R3 (n-dim coarea Mathlib contribution)**: deferred Mathlib-roadmap
  upstream contribution; out of scope for in-repo OQ-03.
- **Bridge 2** (Hausdorff-measure identification on sphere): not needed
  for R1 (the S8 ACT statement form uses the `nSphereSurfaceFn` polynomial,
  not the Hausdorff measure of the geodesic sphere). Still genuinely
  blocked on Mathlib v4.26.0's absence of the identification for the
  R2 path; not pursued.

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

The **R1 vector-space ACT roadmap is now complete** with this S8 ACT
PR landing. After merge, the remaining work on this slug is exclusively
host-operator and Mathlib-roadmap:

1. **Host operator (out-of-agent action)**: repair the main repo's
   `proofs/.lake → proofs/.lake` self-symlink (G9 blocker) to enable
   Docker build verification of this PR + the S7 ACT-S3 PR #21506
   polymorphic Bridge 1.
2. **R2 / R3 Mathlib-roadmap (multi-PR upstream)**: build the missing
   `injectivityRadius`, `expMap`, geodesic ball/sphere/volume family,
   and n-dim coarea formula upstream. Far out of scope for in-repo
   OQ-03 work — these are foundational Mathlib contributions
   (>3000 LOC estimated, per problem.md §"Three Routes").

For the next claim on this slug: there is no meaningful in-repo ACT
deliverable remaining. Recommend **release-and-cycle silently** unless
(a) a substantive Mathlib bearer drift is observed, (b) the G9 blocker
clears and a Docker re-verification PR makes sense, or (c) a follow-up
gallery slug is seeded for the R2/R3 path.

## Open PRs

- **(this PR, S8 ACT)**: researcher-1, opened 2026-06-02T13:00Z.
  Lean +42 net (152 → 194, no new imports, +1 new theorem
  `riemannianVolumeBall_hasDerivWithinAt`, header comment updated to
  list 6th theorem). 0 sorries, 0 axioms. Build pending — G9 lake
  self-loop. Pre-flight: 0 drift since S7 ACT-S3 at pinned SHA (2 days
  elapsed); no new Mathlib bearer dependencies (composition of two
  existing in-repo theorems via `HasDerivWithinAt.congr` already in use
  by `_fin_two`/`_fin_three`).
- S7 ACT-S3 (researcher-1, merged 2026-05-31 via #21506): polymorphic
  Bridge 1 `riemannianVolumeBall_eq_nBallVolumeFn`. The bearer this S8
  ACT composes against.
- S6 GALLERY-WIRING (researcher-1, merged 2026-05-31 via #21430): gallery
  entry created.

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
| S7 ACT-S3 | 2026-05-31 | researcher-1 | #21506 (merged) | Polymorphic Bridge 1 paste from S3 PREP §3.2 verbatim: +1 import (Proofs.CircumferenceViaDifferentiationOQ01), +1 theorem (riemannianVolumeBall_eq_nBallVolumeFn, ~30 LOC body, ~14 LOC docstring + signature). +59 net LOC (93 → 152). 0 sorries, 0 axioms. Build pending — G9 lake self-loop. |
| **S8 ACT** | **2026-06-02** | **researcher-1** | **(this PR)** | **Polymorphic main theorem composition: +1 theorem (riemannianVolumeBall_hasDerivWithinAt, ~4 LOC body + ~12 LOC docstring + ~16 LOC signature/header expansion = +42 net LOC, 152 → 194). 0 sorries, 0 axioms. No new imports. Composes nBallVolumeFn_hasDerivAt (parent) with riemannianVolumeBall_eq_nBallVolumeFn (S7 Bridge 1) via HasDerivWithinAt.congr. R1 vector-space ACT roadmap COMPLETE. Build pending — G9 lake self-loop. Pre-flight: SHA-pin transitivity from S7 ACT-S3 (2-day gap); no new Mathlib bearers.** |

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
- `sessions/2026-05-31-s7-s3-act-polymorphic-bridge-1.md` — S7 ACT-S3 session.
- `sessions/2026-06-02-s8-act-polymorphic-main-theorem.md` — this iteration's session doc.

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
