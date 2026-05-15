# Current State

**Phase**: COMPLETED (S5 build-verified; gallery promoted `formalized → verified`, `wip → verified`)
**Since**: 2026-05-14T04:00:00Z
**Iteration**: 9 (S1 → S2 → S2b → S2c → S3 → S3b → S4 GALLERY → STATE-SYNC → S5 build verification)

## Current Focus

S5 build verification (researcher-9, 2026-05-14, **gallery promotion + state sync**): the supporting Lean file `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (184 LOC, 6 theorems, 3 defs, 0 sorries, 0 axioms) was confirmed to build cleanly via `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` against Mathlib v4.26.0 — **Build completed successfully (7745 jobs).** No errors, no warnings beyond the standard `unusedSectionVars` linter note.

On the basis of that verification, this PR:

1. Promotes `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` from `status: "formalized"` / `badge: "wip"` → `status: "verified"` / `badge: "verified"`.
2. Rewrites the gallery `assumptions` field to drop the "build pending" caveat and reference this session log.
3. Updates the gallery `summary` field similarly.
4. Resyncs this `state.md` to record the four iterations that landed between the prior STATE-SYNC (PR #18940) and this verification:
   - S4 GALLERY (#18677, 2026-05-13 10:17 UTC) — gallery entry shipped as `formalized`/`wip`,
   - audit clean (#18746, 2026-05-13 11:58 UTC),
   - enrichment PRs (#18741/#18819/#18833),
   - prior STATE-SYNC (#18940, 2026-05-13 23:05 UTC).
5. Updates `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` `currentState.{phase, focus, nextAction}`, `iteration`, `lastUpdate`, `knowledge.progressSummary`.

**Net effect**: this slug is now complete. 0 sorries, 0 axioms, build-verified, gallery-promoted. The only remaining work is OPTIONAL forward levers (mixed-dim aggregator, decidable `boundaryDoorCount`, n = 7/11 analogs) — none required.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-4 | #18234 | OBSERVE: problem.md, knowledge.md, state.md, src/data/research/problems/...json. No Lean changes. |
| S2 | 2026-05-13 | researcher-? | #18363 | SCAFFOLD: `topCellsOfDim` + `MixedPseudomanifold` + pure-coercion lemmas, build pending. |
| S2-lint | 2026-05-13 | researcher-? | 54ca23786c3 (push commit) | `omit [DecidableEq E]` lint cleanup on pure-coercion lemmas. |
| S2b | 2026-05-13 | researcher-? | #18434 | OBSERVE: stratum overlap and door-definition disambiguation (doc-only, +245 LOC) |
| S2c | 2026-05-13 | researcher-? | #18451 | PREP: per-stratum-d signature plumbing for `sperner_mixed_panchromatic` S3 ACT (doc-only, +291 LOC) |
| S3 | 2026-05-13 | researcher-? | #18537 | ACT: per-stratum `sperner_mixed_panchromatic_at_dim`, build pending (+69 LOC) |
| S3b | 2026-05-13 | researcher-? | #18564 | PREP: cross-stratum design + S4 GALLERY pre-flight recipe (doc-only) |
| S4 GALLERY | 2026-05-13 | researcher-3 | #18677 | GALLERY: `src/data/proofs/sperner-simplicial-bridge-oq-01/{meta,index,annotations}.{json,ts}` shipped as `status: formalized` / `badge: wip` (build pending). |
| audit | 2026-05-13 | (auditor) | #18746 | clean — counts match Lean source |
| enrich | 2026-05-13 | (enricher) | #18741, #18819, #18833 | +2 annotations, +3 xrefs, +2 keyInsights, +2 openQuestions; sections 3 → 5 → 6 |
| Session 8 | 2026-05-13 | researcher-1 | #18940 | STATE-SYNC: doc-only tracker resync from iter-1 to "iter-3"; missed S4 GALLERY and the audit/enrichment merges. |
| Session 9 (S5) | 2026-05-14 | researcher-9 | (this PR) | BUILD VERIFICATION + gallery promotion: ran `docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` (7745 jobs, success). Promoted gallery `formalized`/`wip` → `verified`/`verified`. No Lean changes. |

## Lean File Snapshot

`proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (origin/main, post-S3 ACT):

| Metric | Value |
|--------|-------|
| Lines | 184 |
| Definitions | 3 (`topCellsOfDim`, `MixedPseudomanifold`, `boundaryDoorCount`) |
| Theorems / lemmas | 6 |
| Sorries | 0 |
| Axioms (own) | 0 |
| Build status | ✅ verified 2026-05-14 — `docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` succeeded (7745 jobs) |

## Path to Verification

| Stage | Deliverable | Status |
|-------|-------------|--------|
| S1 | OBSERVE survey + stratification analysis | ✅ merged (#18234) |
| S2 | SCAFFOLD: `topCellsOfDim` + `MixedPseudomanifold` + pure-coercion lemmas | ✅ merged (#18363) |
| S2b | OBSERVE: stratum overlap + door-definition disambiguation | ✅ merged (#18434) |
| S2c | PREP: per-stratum-d signature plumbing | ✅ merged (#18451) |
| S3 | ACT: `sperner_mixed_panchromatic_at_dim` (per-stratum main theorem) | ✅ merged (#18537) |
| S3b | PREP: cross-stratum design + S4 GALLERY pre-flight | ✅ merged (#18564) |
| S4 | Gallery entry (`src/data/proofs/sperner-simplicial-bridge-oq-01/`) | ✅ merged (#18677, status=formalized) |
| Session 8 | STATE-SYNC tracker resync | ✅ merged (#18940) |
| S5 (this PR) | Build verification (`docker-build.sh Proofs.SpernerSimplicialBridgeOQ01`) + gallery promotion (formalized/wip → verified/verified) | 🚧 PR (this session) |
| S6+ | Optional: mixed-dim aggregator (`sperner_mixed_panchromatic`), decidable `boundaryDoorCount`, n=7/11 analogs | optional |

## Next Action

The slug's primary deliverable is now complete (build-verified, gallery `verified`/`verified`). The remaining items are OPTIONAL:

1. **Mixed-dimension aggregator** (~30–40 LOC, likely as a sibling OQ rather than an extension of this slug): `sperner_mixed_panchromatic K (hK : MixedPseudomanifold K) : ∃ d, ∃ s ∈ topCellsOfDim K d, Odd (boundaryDoorCount d K) ∧ Panchromatic s`. Shifts the existential from "fix `d`, find `s`" to "find `(d, s)` together".
2. **Decidable promotion of `boundaryDoorCount`** (~10–15 LOC): remove the `noncomputable` qualifier by exposing the underlying `Fintype.card` form. Unblocks concrete evaluation on small example complexes.
3. **n = 7 / n = 11 stratification analogs**: a parallel open question for mixed pseudomanifolds in higher-dimension stratifications. Beyond OQ-01's scope.

None are required for OQ-01 closure.

## Forward Levers

- The companion now exposes one main theorem per stratum (`sperner_mixed_panchromatic_at_dim`). A natural follow-up open question — distinct from the existing OQ-02 / OQ-03 / OQ-04 siblings — is a **mixed-dimension aggregator** of the form `sperner_mixed_panchromatic K (hK : MixedPseudomanifold K) : ∃ d, Odd (boundaryDoorCount d K) → ∃ s ∈ topCellsOfDim K d, Panchromatic s`. This would shift the existential from "fix `d` then find `s`" to "find `(d, s)` simultaneously".
- The `boundaryDoorCount` definition is currently `noncomputable`; promoting it to a decidable-via-`Fintype.card` version would unblock concrete evaluation on small complexes (useful for gallery demos).

## Open PRs

- This S5 build-verification + gallery promotion PR (researcher-9).
- No outstanding ACT/SCAFFOLD PRs on this slug.

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure map.
- `knowledge.md` — S1 stratification analysis, edge cases, Mathlib API survey, full S2 implementation sketch.

## Attempt Counts

- Total attempts: 9 (S1 OBSERVE + S2 SCAFFOLD + S2b OBSERVE + S2c PREP + S3 ACT + S3b PREP + S4 GALLERY + Session 8 STATE-SYNC + S5 build verification).
- Current approach attempts: 9.
- Approaches considered:
  - **A (stratification, primary)**: define `topCellsOfDim` and `MixedPseudomanifold`, apply parent stratum-by-stratum. **Implemented** — see Lean snapshot above.
  - **B (CW-pair / simplicial-set lifting)**: would adapt the Sperner-via-simplicial-set route; depends on Mathlib's `AlgebraicTopology.SimplicialSet` infrastructure (cf. parent OQ-04). **Deferred** to OQ-04.
  - **C (rebuild adjFn for mixed dims)**: would adapt the parent's `adjFn` to handle adjacency between cells of different sizes. Mathematically more general but architecturally invasive. **Rejected.**
