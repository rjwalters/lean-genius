# Research State: ptolemys-complex-proof-oq-02-oq-02

## Current State
**Phase**: PREP (S2a-prep, S2a ACT parked by parent v4.26.0 blocker)
**Path**: full
**Since**: 2026-05-14T21:50 UTC
**Iteration**: 2 (S2a-prep)

## Current Focus

S2a-prep — Mathlib v4.26.0 Ptolemy-chain build-blocker diagnosis.

S2a ACT (write `chord_length_at_radius_r` helper) is **parked** until the parent's
import chain unblocks. Docker baseline of `Proofs.PtolemysComplexProofOQ02` fails at
`Proofs.PtolemysTheoremOQ01` (transitive dep) with v4.26.0 API drift:

- `Complex.abs_one` — Unknown constant
- `Complex.abs_neg` — Unknown constant
- `Complex.abs_apply` — Unknown constant (2 sites)
- `Complex.norm_eq_abs` — Unknown constant in `norm_num` lemma list

(See `sessions/2026-05-14-s2a-prep-v4.26.0-ptolemy-chain-blocker.md` for the full
mechanic-ready kit.)

A draft `Proofs.PtolemysComplexProofOQ02OQ02.lean` (chord-length helper, ~115 LOC)
was prepared during this session but cannot be Docker-verified through the broken
parent chain — held off until mechanic discharges the kit.

## Active Approach

S2a-prep: doc-only. No Lean code shipped this iteration. Mechanic-kit prepared in
session note for the Ptolemy-chain v4.26.0 regression.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2 (S1 OBSERVE survey, S2a-prep blocker diagnosis)

## Blockers

**Active**: Mathlib v4.26.0 Ptolemy-chain build regression — `Complex.norm_eq_abs`
and `Complex.abs_*` lemma family no longer fully available in `norm_num`/`simp_only`
contexts at the pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

Affected files (12 sites total, ~6 must-fix for build):

| File | Sites | Severity |
|------|-------|----------|
| `PtolemysTheoremOQ01.lean` | 6 | **must-fix** — blocks chain |
| `PtolemysComplexProofOQ02.lean` | 4 (all `rw [Complex.norm_eq_abs, Complex.sq_abs]`) | likely fine via `rw` — verify after K1 |
| `PtolemysTheoremOQ01OQ01.lean` | 1 (`norm_num`) | downstream cascade |
| `PtolemysTheoremOQ01Incomplete01.lean` | 1 (`rwa`) | likely fine via `rwa` |
| `PtolemysComplexProof.lean` | 1 (docstring only) | cosmetic |

The blocker is **not** a new finding; it surfaced on first Docker build attempt for
S2a ACT (this session). Pre-claim search (2026-05-14T21:30 UTC) confirmed no open PR
addresses it — researcher-12 documents the kit for mechanic; **does not fix** (the
6-error PtolemysTheoremOQ01 file falls in the ambiguous 4–9 error band; the doc-only
PREP route is preferred per `feedback_researcher_build_blocker_mechanic_kit_prep_pattern`).

**Tractability**: easy after mechanic discharges the kit. The two failing `example`
blocks at `PtolemysTheoremOQ01.lean:439-457` are demonstration-only (not depended on
by any theorem in the chain) — deletion is the lowest-risk fix.

## Next Action

**S2a ACT (parked)** — write `proofs/Proofs/PtolemysComplexProofOQ02OQ02.lean` with
the `chord_length_at_radius_r` helper (~80 LOC, 0 sorries, 0 axioms). Subsume the
parent's six radius-1 lemmas as `r := 1` corollaries.

**Unblocked when**: mechanic merges a fix for `PtolemysTheoremOQ01.lean:439-457`
example blocks (kit K1 in session note).

**S2a-prep draft Lean** (this session, NOT enrolled in `Proofs.lean`): the chord
length squared-norm + half-angle approach mirrors parent's `norm_exp_diff` lemma
(`PtolemysComplexProofOQ02.lean:179-207`). Draft was held back to avoid stacking
build-pending content on top of a known-broken parent chain.

## Open PRs

- This PR (S2a-prep doc-only — state.md + knowledge.md + session note,
  ~+250 LOC across 3 files).

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | merged | OBSERVE — chord-radius-$r$ + law-of-cosines roadmap (3-sub-iteration S2 plan, ~270 LOC) |
| S2a-prep | 2026-05-14 | researcher-12 | (this PR) | PREP — v4.26.0 Ptolemy-chain mechanic-kit; S2a ACT parked |
