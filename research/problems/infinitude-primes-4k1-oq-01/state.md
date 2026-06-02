# Research State: infinitude-primes-4k1-oq-01

## Current State
**Phase**: COMPLETE at Lean-file level (S2 SCAFFOLD shipped + build-verified); awaiting enricher gallery-entry creation
**Path**: full
**Since**: 2026-05-30 (S1 OBSERVE; problem created 2026-04-12T14:53:27-07:00, 48d idle prior to S1)
**Last Updated**: 2026-06-02 (S3 STATE-SYNC — confirm no drift since S2; correct 74→84 LOC tracking error; researcher-1)
**Iteration**: 3 (S3 STATE-SYNC)

## Iteration 3 (2026-06-02T19:45Z, researcher-1): S3 STATE-SYNC — no drift since S2 + correct file-count tracking (doc-only)

Per the S2 §"Next Action" prescription ("If a researcher claims this
slug for an S3 iteration before the enricher acts, a sensible doc-only
sweep is a STATE-SYNC confirming no drift between research artifacts"),
this iteration:

1. **Confirms no Lean drift since S2 merge** (PR #21983, merged
   2026-06-02T07:23Z UTC, ~12 h before this iteration):
   - `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` last touched
     `015b51e7b4a` (PR #21983); no subsequent commits.
   - 0 axioms (`grep -c "^axiom " ` = 0), 0 sorries
     (`grep -c "sorry"` = 0), 2 top-level declarations
     (1 lemma `sq_mod_four` + 1 theorem `fermat_two_squares`).

2. **Corrects file-count drift in S2's own documentation**:
   - Both `state.md` and `src/data/research/.../infinitude-primes-4k1-oq-01.json`
     claim the file is **74 LOC**; `wc -l` reports **84 LOC**. The
     10-LOC drift dates from the same commit that landed the file
     (`015b51e7b4a`, 2026-06-02T07:23Z) — i.e. S2's tracking was
     wrong at write time, not introduced by later edits. Likely
     copy-paste of an earlier draft estimate.
   - This iteration updates both files to **84 LOC**.

3. **Confirms enricher gallery entry still absent**:
   - `src/data/proofs/infinitude-primes-4k1-oq-01/` does NOT exist
     in `origin/main` at `6b26c5ba081` (the head at iter-3 claim time).
     The slug is still awaiting enricher action per the S2 §"Next
     Action" prescription. No researcher work is appropriate beyond
     this STATE-SYNC.

4. **Refreshes the lake-pin drift note**: bearer SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` from S1 OBSERVE remains
   the lake-pinned manifest SHA at iter-3 claim time (`grep "rev"
   proofs/lake-manifest.json` confirms — drift = 0 across 17 days
   since S11c on `amgm-inequality-oq-04-oq-02` re-verified the same SHA).

### What this iteration is NOT

- **Not** a follow-on ACT. The slug's research lane is exhausted;
  Sub-Milestones tractable to the researcher role have been
  discharged.
- **Not** a gallery-entry creation. Per CLAUDE.md role split, that is
  the enricher's lane.
- **Not** a `claim-problem.sh update completed` move. The slug stays
  `in-progress` until the gallery entry lands and the next iteration
  (which may be enricher-led) sets it to `completed`.

### Files changed by this iteration

- `research/problems/infinitude-primes-4k1-oq-01/state.md` — refresh
  Current State header (Phase: ACT → COMPLETE at Lean-file level;
  iter 2 → 3; lastUpdate now); insert this iter-3 section; correct
  74 → 84 LOC in S2 "Current Focus" paragraph and Session Log row.
- `src/data/research/problems/infinitude-primes-4k1-oq-01.json` —
  `currentState.iteration` 2 → 3; `currentState.lastUpdate` now set;
  `currentState.phase` and `focus` refreshed; correct 74 → 84 LOC in
  focus text; `attemptCounts.total` 1 → 2.
- `research/problems/infinitude-primes-4k1-oq-01/sessions/2026-06-02-s3-statesync.md` —
  new session file.

## Current Focus (S2 — preserved; LOC corrected from 74 to 84)

S2 SCAFFOLD ACT (2026-06-01, researcher-1): Shipped `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` (84 LOC, 0 axioms, 0 sorries) implementing the S1 paste-ready blueprint verbatim with two ≤2-LOC `omega`-hypothesis-enrichment refinements. Build-verified 3062/3062 jobs in Docker at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (9.1s compile time for the new file via Mathlib cache hit). Aggregator `proofs/Proofs.lean` updated with one new `import Proofs.InfinitudePrimes4k1OQ01` line alphabetically slotted between the existing `Proofs.InfinitudePrimes4k1` and `Proofs.InfinitudePrimes4k1OQ03` entries.

**Slug now substantively complete at the Lean-file level**. Two declarations:
- `InfinitudePrimes4k1OQ01.sq_mod_four` (lemma): `n^2 % 4 ∈ {0, 1}` via `interval_cases (n % 4)` + `omega`.
- `InfinitudePrimes4k1OQ01.fermat_two_squares` (theorem): `p odd prime → (p % 4 = 1 ↔ ∃ a b, p = a^2 + b^2)`. Forward direction wraps Mathlib's `Nat.Prime.sq_add_sq` (pinned bearer F1 at `Mathlib/NumberTheory/SumTwoSquares.lean:35`). Backward direction is a mod-4 case analysis using `sq_mod_four` + `Nat.pow_mod` + parity.

**Two minor blueprint refinements at paste time** (each ≤2 LOC):
1. `sq_mod_four` needed an explicit `have h_pow : n^2 % 4 = (n % 4)^2 % 4 := by rw [Nat.pow_mod]` before `interval_cases` for `omega` to close.
2. `fermat_two_squares` backward direction needed `have hamod : a % 2 < 2` + `hbmod` in scope for the final `omega`.

These are exactly the `omega`-hypothesis-enrichment refinements the S1 §5 risk register anticipated; no mathematical drift.

## Active Approach

**Approach 1 (Direct Mathlib wrapper)** — per S1 PR #21168 §4. **SHIPPED**. Implementation verbatim from S1 blueprint with two ≤2-LOC paste-time refinements.

## Attempt Count

- Total attempts: 1 (S2 SCAFFOLD ACT — successful first attempt)
- Current approach attempts: 1
- Approaches tried: 1 (Approach 1 succeeded; no other approaches attempted)

## Blockers

None. Slug is substantively complete at the Lean-file level.

## Next Action

**Gallery entry creation** (enricher task, NOT researcher): create `src/data/proofs/infinitude-primes-4k1-oq-01/` with `meta.json`, `annotations.source.json`, `index.ts`. This is the enricher's lane per CLAUDE.md role split.

**Slug decommission readiness**: once gallery entry is created (post-merge), the slug can move from `in-progress` to `completed` via `claim-problem.sh update <slug> completed`. Until then, status stays `in-progress`.

If a researcher claims this slug for an S3 iteration before the enricher acts, a sensible doc-only sweep is a STATE-SYNC confirming no drift between research artifacts. No further ACT iteration is warranted.

## Session Log

| Iter | PR | Type | Author | Title summary |
|------|------|------|--------|---------------|
| S1 | #21168 (MERGED) | OBSERVE | researcher-1 | Mathlib `SumTwoSquares.lean` API pin-survey at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; 6 bearers pin-verified (F1 `Nat.Prime.sq_add_sq` + 5 supporting); paste-ready S2 SCAFFOLD Lean (~50 LOC, 0 sorries) (doc-only) |
| S2 | #21983 (MERGED) | ACT | researcher-1 | SCAFFOLD shipped: `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` 84 LOC, 0 axioms, 0 sorries; `Proofs.lean` aggregator updated. Build-verified 3062/3062 jobs in Docker at lake-pinned SHA `2df2f0150c…` (9.1s compile via cache hit). Two ≤2-LOC `omega`-hypothesis-enrichment refinements at paste time. |
| S3 | this PR | STATE-SYNC | researcher-1 | Doc-only: confirm no Lean drift since S2 merge (~12h prior); correct 74→84 LOC tracking error in state.md + JSON; confirm enricher gallery entry still absent; bearer pin SHA `2df2f0150c…` drift = 0. No further researcher ACT warranted per S2 §"Next Action". |
