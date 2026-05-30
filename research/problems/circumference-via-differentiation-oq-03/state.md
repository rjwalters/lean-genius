# Current State: circumference-via-differentiation-oq-03

**Phase**: ACT-MERGED (S2 ACT 4-thm n=2,3 partial on main; doc-side resync pending; next ACT menu below)
**Path**: full
**Since**: 2026-05-30T12:15:00Z (this S5 STATE-SYNC); ACT-merged 2026-05-16T08:55Z (commit ecb47b35601 in PR #19454 bulk merge); root-since 2026-05-12T22:55:00Z
**Iteration**: 8 (S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [merged via #19454 bulk], S3 PREP, S4 PREP, S5 STATE-SYNC [this])
**Researcher**: researcher-1 (S5 STATE-SYNC); preceding: researcher-9 (S1, S2 ACT, S4 PREP), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP + S3 PREP), researcher-4 (S2d PREP)

## Current Focus (S5 STATE-SYNC, researcher-1, 2026-05-30)

The Lean S2 ACT deliverable (n=2 and n=3 Euclidean partial) **landed on main** as
`proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (93 lines, 4 theorems,
0 sorries, 0 axioms) via the #19454 bulk merge (commit `ecb47b35601`, dated
2026-05-16). The originally-OPEN PR #18985 (researcher-9, 2026-05-14) was
**CLOSED** without individual merge — its code was absorbed into the bulk.

Two weeks of doc-side state nonetheless described #18985 as still
awaiting deployer (the S3 PREP / S4 PREP framing was correct at the time
of writing but became stale after the 2026-05-15 → 2026-05-16
deployer-stall-recovery bulk merge). **This S5 STATE-SYNC reconciles
state.md and the JSON registry to ground truth.**

Net change in this PR: 3 doc-only files (this state.md; the new
sessions/2026-05-30-s5-state-sync-post-s2-act-landing.md; the
JSON cursor refresh). **No Lean modification. No gallery wiring.**

## Verified Deliverables on main (as of 2026-05-30T12:15Z)

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (93 LOC, 4 thms)
  - `riemannianVolumeBall_fin_two` — Bridge 1, n=2: vol(closedBall p r) = π r²
  - `riemannianVolumeBall_fin_three` — Bridge 1, n=3: vol(closedBall p r) = (4π/3) r³
  - `riemannianVolumeBall_hasDerivWithinAt_fin_two` — Main S5, n=2: dV/dr = 2π r
  - `riemannianVolumeBall_hasDerivWithinAt_fin_three` — Main S5, n=3: dV/dr = 4π r²
- `proofs/Proofs.lean` — `import Proofs.CircumferenceViaDifferentiationOQ03` present
- 0 sorries; 0 axioms; build verified at the time of the bulk merge

## Pending (not yet built)

- **Gallery wiring**: `src/data/proofs/circumference-via-differentiation-oq-03/`
  does not exist. The OQ-03 deliverable is not visible in the gallery.
- **Polymorphic Bridge 1**: the abstract `[InnerProductSpace ℝ E]` version
  (Workaround A) — documented in S3 PREP #19136 as a ~50-LOC tactic chain —
  is not yet in the Lean file.
- **Polymorphic main theorem**: the abstract-E version of dV/dr = A
  (Workaround C', skipping Bridge 2 by stating RHS directly via
  `nSphereSurfaceFn`).
- **Bridge 2** (Hausdorff-measure identification on sphere): still
  genuinely blocked on Mathlib v4.26.0's absence of the identification;
  the recommended path is Workaround C' (skip Bridge 2).

## Path to Verification (R1 vector-space route, updated)

| Stage | Deliverable | Lines | Status |
|-------|-------------|-------|--------|
| S1 | OBSERVE survey (text-only) | — | ✓ merged (#18362) |
| S2 PREP+ACT | n=2, n=3 Euclidean partial Lean (4 theorems, Docker verified) | 93 | **✓ on main via #19454 bulk** |
| S3 PREP | Mathlib availability erratum (polymorphic Bridge 1 unblocked) | doc | ✓ merged (#19136) |
| S4 PREP | Deployer-stall coordination + 3-way merge resolution doc | doc | ✓ merged (#19205) |
| **S5 STATE-SYNC** | **post-S2-ACT-landing reconciliation (this PR)** | **doc** | **(this iteration)** |
| (next) S2-b ACT | Gallery wiring: src/data/proofs/.../{meta.json,index.ts} | ~80 | pending |
| (next) S3 ACT | Polymorphic Bridge 1 (abstract [InnerProductSpace ℝ E]) | ~50 | pending |
| (next) S4 ACT | Polymorphic main theorem (Workaround C', skip Bridge 2) | ~60 | pending (depends on S3 ACT) |

R2 (full Riemannian manifold) and R3 (n-dim coarea Mathlib contribution)
remain deferred Mathlib-roadmap targets, gated on the 4-gap list in
problem.md §"Three Routes".

## Next Action

Three independent ACT pipelines, recommended order:

### (a) Gallery wiring — S2-b ACT, ~80 LOC, recommended first

Create:
- `src/data/proofs/circumference-via-differentiation-oq-03/meta.json`
  (status `verified`, badge `original`, sorries 0, axiomCount 0,
  lineCount 93, theoremCount 4, mathlibDependencies for the four
  bearers).
- `src/data/proofs/circumference-via-differentiation-oq-03/index.ts`
  (~10 LOC, parallel to OQ-01).

Test: `pnpm build`. No Lean, no Docker. Single-researcher iteration.

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

Each is a single researcher iteration; (a) ships independently of (b)/(c).

## Open PRs

- **(this PR, S5 STATE-SYNC)**: researcher-1, opened
  2026-05-30T~12:15Z. Doc-only. Mergeable; no conflicts.

No other open OQ-03 PRs (as of 2026-05-30T12:15Z).

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
| **S5 STATE-SYNC** | **2026-05-30** | **researcher-1** | **(this PR)** | **Post-S2-ACT-landing doc reconciliation: state.md + JSON cursor → ACT-MERGED; doc-only.** |

## Reference Files (in this directory)

- `problem.md` — formal target, classification, three-route
  classification, Mathlib infrastructure map, numerical sanity,
  anti-targets, references. ~520 lines. Unchanged this iteration.
- `knowledge.md` — S1 session summary, mathematical background,
  Mathlib API surface, Lean skeleton sketch, risk register, S∞
  roadmap, S6+ stretch notes. ~350 lines. Unchanged this iteration.
- `sessions/2026-05-12-...` through `sessions/2026-05-15-...` —
  six prior session documents from S2 PREP through S4 PREP.
- `sessions/2026-05-30-s5-state-sync-post-s2-act-landing.md` — this
  iteration's session doc. ~280 lines.

## Calibration

This S5 STATE-SYNC is doc-only. Verifies ground-truth on main:
- 93-LOC OQ03 Lean file exists with 4 theorems, 0 sorries, 0 axioms;
- `Proofs.lean` imports it;
- `src/data/proofs/circumference-via-differentiation-oq-03/` does NOT
  exist (gallery wiring still pending);
- PR #18985 is CLOSED (verified via gh).

The next concrete deliverable is **(a) gallery wiring**, the smallest
of the three pending ACT pipelines. The R1 vector-space target
narrative is unchanged from S1 OBSERVE; what has changed since the
last state.md is purely the doc-side cursor catching up to merged
reality.
