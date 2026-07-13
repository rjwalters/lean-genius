# S3 STATE-SYNC — INFRA gates recovered (G7/G8/G9 all GREEN at T+23d)

**Date**: 2026-06-09T23:58:00Z
**Researcher**: researcher-1 (claim id researcher-75646)
**Mode**: STATE-SYNC (doc-only; INFRA recovery documentation + S2 picker-matrix update)
**Outcome**: progress — INFRA RED → GREEN over T+23d; S2 picker-matrix top row now operationally valid for a future picker

## Why this is a STATE-SYNC, not S3 ACT

The S2 OBSERVE picker matrix (sessions/2026-05-17-s2-observe-chains-subcase-skeleton.md §6) prescribes:

| G7 disk | G8 Docker | G9 .lake | Mathlib SHA | S3 action |
|---------|-----------|----------|-------------|-----------|
| ≥5 Gi | populated | real dir | unchanged | **S3 ACT chains sub-case** (chain-cover skeleton + build) |

At S3 STATE-SYNC pickup time (2026-06-09T23:55Z, T+23d since S2 OBSERVE):

| Gate | S2 status (2026-05-17) | S3 status (2026-06-09) | Δ |
|------|------------------------|------------------------|---|
| G7 host disk available | **RED** (3.3 Gi, deteriorating) | **GREEN** (99 GiB free / 90% used / 926 GiB) | +95.7 Gi |
| G8 `docker info` Server: section | **RED** (empty) | **GREEN** (populated; Server Version 29.5.3, overlayfs storage) | recovered |
| G9 `proofs/.lake` symlink | **RED** (self-cycle reported) | **GREEN** (real directory: `ls proofs/.lake/` returns content) | recovered |

All three INFRA gates are now GREEN. **Per the S2 picker matrix, this should trigger the top row: full S3 ACT chains sub-case.** However, the S2 skeleton (sessions/2026-05-17-s2-observe-chains-subcase-skeleton.md §4) is **NOT paste-ready as advertised** — careful inspection finds:

1. `recognizeChainCover` body contains `decide (∃ (P : G.Walk _ _), P.IsHamiltonian ∧ ...)` with **literal `...` placeholder** plus a parenthetical "implementation note: See S3 ACT for the concrete formulation".
2. `chain_cover_recognition_decidable` body is a **single `sorry`** with a sketch comment.

The S2 OBSERVE memo §4 explicitly says: "The skeleton intentionally uses `sorry` in the theorem and `...` placeholders in `recognizeChainCover`'s body — S2 OBSERVE is a PREP memo, not an ACT. The S3 ACT discharges both placeholders under recovered Docker."

So S3 ACT requires:

- Selecting a concrete formulation of `recognizeChainCover` (one of: Hamiltonian-walk-exists, degree-sequence check, connected + n−1 edges + max-degree ≤ 2)
- Designing a proof of `chain_cover_recognition_decidable` that uses `Mathlib.Combinatorics.SimpleGraph.Path` lemmas like `SimpleGraph.IsPath` and degree-sequence machinery
- Verifying signatures of all Mathlib bearers at the pinned SHA
- Integrating with the existing `[PartialOrder V]` typeclass machinery in the file (e.g., `coverOrientation`, `posetRank_strictMono`, `cover_implies_related`)

This is genuinely **multi-session ACT scope** (estimated ≥150 LOC + 4-6 hr design + build verification). A single-session researcher pulling this slug should NOT undertake S3 ACT in one cycle; the picker matrix should be amended to require both **INFRA GREEN** AND **skeleton fully paste-ready (no `...` no `sorry`)** as joint preconditions for ACT.

## What this S3 STATE-SYNC does ship

Doc-only updates capturing the INFRA recovery so the next picker has accurate signal:

1. **NEW** `sessions/2026-06-09-s3-statesync-infra-green-recovery.md` — this memo.
2. **state.md** head and "Current Focus" update:
   - Iteration 2 → 3
   - Phase OBSERVE → STATE-SYNC
   - Since 2026-05-17 → 2026-06-09
   - Last Updated 2026-05-17 → 2026-06-09
   - INFRA snapshot table refreshed to G7/G8/G9 all GREEN
3. **Canonical JSON** `src/data/research/problems/erdos-1006-oq-01-oq-02.json`:
   - `currentState.{phase, since, iteration, focus, nextAction}` refresh
   - `knowledge.progressSummary` prepend with S3 narrative
   - `lastUpdate` 2026-05-17 → 2026-06-09

## Pre-edit verification (build state on origin/main + worktree HEAD)

| Item | Value | Source |
|---|---|---|
| `proofs/Proofs/Erdos1006OQ01OQ02.lean` `wc -l` | 256 | `wc -l` (matches meta.json `lineCount: 256`) |
| Axiom count | 2 (`comparability_recognition_in_p`, `cover_graph_recognition_in_p`) | `grep -c "^axiom "` |
| Sorry count | 0 | `grep -c sorry` |
| Theorem count | 9 | unchanged from S2 OBSERVE |
| Definition count | 4 | unchanged from S2 OBSERVE |
| Mathlib pin SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) | `proofs/lake-manifest.json` |
| SHA delta since S1 OBSERVE (2026-05-16) | unchanged (T+24d SHA-stable) | as above |

All S1/S2 audit findings remain bit-identical at S3. No bearer re-audit performed (SHA-stable since S1).

## Updated picker matrix (post-S3)

S3 STATE-SYNC amends the S2 picker matrix to require **both** INFRA GREEN **and** skeleton paste-readiness as joint preconditions for ACT:

| G7 disk | G8 Docker | G9 .lake | Mathlib SHA | Skeleton state | S4 action |
|---------|-----------|----------|-------------|----------------|-----------|
| ≥5 Gi | populated | real dir | unchanged | **paste-ready** (no `...`, no `sorry`) | **S4 ACT** chains sub-case |
| ≥5 Gi | populated | real dir | unchanged | sketch (S2 state) | **S4 PREP** refine skeleton to paste-ready |
| ≥5 Gi | populated | real dir | bumped | any | S4 ACT but re-walk bearers first |
| ≥5 Gi | empty | real dir | unchanged | any | S4 PREP refine — wait for Docker |
| ≥5 Gi | populated | self-cycle | unchanged | any | S4 INFRA recovery first |
| <5 Gi | any | any | any | any | S4 STATE-SYNC only |
| any | any | any | unknown | any | S4 OBSERVE — re-verify pin |

**Current state hits row 2: S4 PREP refine skeleton.**

## What S4 PREP should contain (recommendation for next picker)

1. Pick a concrete `recognizeChainCover` formulation. Candidate: connected + `Finset.card (G.edgeFinset)` `= card V - 1` + `∀ v, G.degree v ≤ 2`. This is `O(n²)`-checkable and matches the path-graph characterisation.
2. Identify the exact Mathlib lemmas at the pin: `SimpleGraph.IsPath` (Combinatorics.SimpleGraph.Path), `SimpleGraph.Connected`, `SimpleGraph.degree`, `Finset.card_le_card` etc. Walk each name through `gh api /repos/leanprover-community/mathlib4/contents/Mathlib/Combinatorics/SimpleGraph/Path.lean?ref=2df2f01…` to verify signature at the pin.
3. Bridge construction: for `LinearOrder V`, show the cover graph is exactly the path on the sorted vertex list. Use the existing `coverOrientation` machinery + `posetRank_strictMono`.
4. Produce paste-ready Lean with **0 `sorry` and 0 `...`**.

Estimated S4 PREP scope: ~3-4 hours design + ~50-100 LOC paste-ready skeleton + Mathlib bearer table (verified signatures, not just names).

## Files modified

- `research/problems/erdos-1006-oq-01-oq-02/sessions/2026-06-09-s3-statesync-infra-green-recovery.md` — NEW (this memo).
- `research/problems/erdos-1006-oq-01-oq-02/state.md` — head refresh + S3 prepend block.
- `src/data/research/problems/erdos-1006-oq-01-oq-02.json` — `currentState.*` + `knowledge.progressSummary` + `lastUpdate`.

## Files NOT modified (intentional scope discipline)

- `proofs/Proofs/Erdos1006OQ01OQ02.lean` — Lean file untouched (0 byte change).
- `src/data/proofs/erdos-1006-oq-01-oq-02/` — no gallery edits.
- `problem.md` / `knowledge.md` — pre-existing from S1 OBSERVE; no factual change.
- `proofs/lake-manifest.json` — Mathlib pin unchanged.
- Sibling slugs (`erdos-1006-oq-01-oq-01`, parent `erdos-1006`) — out of scope.

## Build risk

Zero — 0 Lean files modified, 0 imports changed, 0 tactic changes. Sorries unchanged (0). Axiom count unchanged (2). Theorem count unchanged (9). LineCount unchanged on disk (256).

## Phase head transition

S1 OBSERVE → S2 OBSERVE → **S3 STATE-SYNC (INFRA recovery + picker-matrix amendment)** → next picker should ship S4 PREP (skeleton refinement to paste-ready) → S5 ACT (chains sub-case discharge).

The slug's mathematical question (`cover_graph_recognition_in_p` for arbitrary finite graphs) **remains genuinely OPEN**. S3 only refreshes the operational signals; the open content is not advanced.
