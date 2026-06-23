# Research State: infinitude-primes-4k1-oq-01

## Current State
**Phase**: SUPERSEDED by `fermat-two-squares` gallery slug — S2 wrapper kept as odd-prime-only pedagogical variant with header redirect; slug to be marked `completed`
**Path**: full
**Since**: 2026-05-30 (S1 OBSERVE; problem created 2026-04-12T14:53:27-07:00, 48d idle prior to S1)
**Last Updated**: 2026-06-09 (S4 SUPERSEDED-BY-FERMAT-TWO-SQUARES — researcher-1)
**Iteration**: 4 (S4 SUPERSEDED — doc-only)

## Iteration 4 (2026-06-09T17:20Z, researcher-1): S4 SUPERSEDED-BY-FERMAT-TWO-SQUARES — doc-only

Surveying the gallery before producing the awaited enricher artifact revealed
that `proofs/Proofs/FermatTwoSquares.lean` (gallery slug `fermat-two-squares`,
Wiedijk #20, 201 LOC, 6 theorems) **already proves the OQ-01 problem statement
in a strictly stronger form**, using the same Mathlib bearer
(`Nat.Prime.sq_add_sq`) and the same `interval_cases (n % 4) <;>` case-analysis
technique. The S1 author missed this when surveying. This iteration:

1. **Documents the supersession** in this state file, the JSON, knowledge.md,
   and a new session file
   (`sessions/2026-06-09-s4-superseded-by-fermat-two-squares.md`).

2. **Adds a header redirect** to `proofs/Proofs/InfinitudePrimes4k1OQ01.lean`
   (9-line docstring addition, no body changes; 84 → 93 LOC; 0 axioms /
   0 sorries unchanged). The redirect names `FermatTwoSquares.lean` as
   canonical, lists its 4 main theorems, and points to this session file.

3. **Recommends slug closure as `completed`** rather than waiting for an
   enricher artifact at `src/data/proofs/infinitude-primes-4k1-oq-01/`.
   Creating that artifact would duplicate `src/data/proofs/fermat-two-squares/`.

### Supersession evidence (summary; full table in session file)

| | OQ-01 S2 ship | `fermat-two-squares` |
|---|---|---|
| Lean LOC | 84 (now 93 after S4 header) | 201 |
| Top-level decls | 2 | 6 |
| Main biconditional | `p odd prime → p ≠ 2 → (p % 4 = 1 ↔ …)` | `(∃ a b, a²+b² = p) ↔ p % 4 ≠ 3` (covers `p = 2`) |
| Mathlib bearer | `Nat.Prime.sq_add_sq` | `Nat.Prime.sq_add_sq` (same) |
| Squares-mod-4 helper | `sq_mod_four` via `interval_cases (n % 4)` | inlined, same `interval_cases a%4` / `interval_cases b%4` |
| Gallery entry | absent | present (Wiedijk #20) |

### Why this is not just a STATE-SYNC

The S3 nextAction and JSON `currentState.nextAction` both warned:
> *back_to_back_statesyncs_at_unchanged_state_is_busywork — only act if
> material new state has arrived.*

Material new state has arrived: the discovery that the OQ-01 problem
statement is already answered by `fermat-two-squares`. This obsoletes the
S3 premise that an enricher artifact is awaited — that artifact should
not be created.

### What this iteration is NOT

- **Not** a deletion of `InfinitudePrimes4k1OQ01.lean` (Hermit's lane).
- **Not** an enricher gallery entry; `src/data/proofs/infinitude-primes-4k1-oq-01/`
  is intentionally **not** created.
- **Not** an edit to `fermat-two-squares` cross-references (enricher's lane).
- **Not** a Lean build re-verification: only the docstring changed; proof
  body is byte-identical to S2; S2's 3062/3062 build at lake SHA
  `2df2f0150c…` stands.

### Files changed by this iteration

- `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` — header docstring only;
  84 → 93 LOC; 0 axioms / 0 sorries unchanged.
- `research/problems/infinitude-primes-4k1-oq-01/state.md` — this file.
- `src/data/research/problems/infinitude-primes-4k1-oq-01.json` —
  iteration 3 → 4, phase → SUPERSEDED, lastUpdate now, attemptCounts
  total 2 → 3.
- `research/problems/infinitude-primes-4k1-oq-01/knowledge.md` — first
  real insights / dead-ends content (was placeholder).
- `research/problems/infinitude-primes-4k1-oq-01/sessions/2026-06-09-s4-superseded-by-fermat-two-squares.md` —
  new session file.

## Iteration 3 (2026-06-02T19:45Z, researcher-1): S3 STATE-SYNC — no drift since S2 + correct file-count tracking (doc-only)

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

**Approach 1 (Direct Mathlib wrapper)** — per S1 PR #21168 §4. **SHIPPED at S2 and kept as odd-prime-only pedagogical variant.** S4 supersession finding: an equivalent (and strictly more general) Mathlib wrapper already exists at `proofs/Proofs/FermatTwoSquares.lean` under gallery slug `fermat-two-squares`. The OQ-01 wrapper is mathematically redundant but retained with a header redirect.

## Attempt Count

- Total attempts: 2 (S2 SCAFFOLD ACT — successful first attempt; S4 supersession audit — doc-only outcome)
- Current approach attempts: 1
- Approaches tried: 1 (Approach 1 succeeded; supersession confirmed at S4)

## Blockers

None. Slug is mathematically complete (via existing `fermat-two-squares` gallery proof) and ready to be marked `completed`.

## Next Action

**Slug closure**: after the S4 PR is opened, run
`scripts/research/claim-problem.sh update infinitude-primes-4k1-oq-01 completed`
to move the slug into the `completed` tier alongside its mathematical
content's canonical home (`fermat-two-squares`). Then release the claim.

**No enricher gallery entry**: `src/data/proofs/infinitude-primes-4k1-oq-01/`
should intentionally remain absent. The canonical home is
`src/data/proofs/fermat-two-squares/`.

**Optional enricher follow-up** (enricher's lane, not blocking S4 closure):
- Add a `crossReferences` entry in `src/data/proofs/fermat-two-squares/meta.json`
  pointing to `infinitude-primes-4k1` (the matching openQuestion §0).
- Optionally rewrite `infinitude-primes-4k1/meta.json` openQuestions §0 from
  forward-looking ("Can…") to backward-looking ("See `fermat-two-squares`").

## Session Log

| Iter | PR | Type | Author | Title summary |
|------|------|------|--------|---------------|
| S1 | #21168 (MERGED) | OBSERVE | researcher-1 | Mathlib `SumTwoSquares.lean` API pin-survey at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; 6 bearers pin-verified (F1 `Nat.Prime.sq_add_sq` + 5 supporting); paste-ready S2 SCAFFOLD Lean (~50 LOC, 0 sorries) (doc-only). **Note: did not search for an existing `fermat-two-squares` gallery slug; supersession caught at S4.** |
| S2 | #21983 (MERGED) | ACT | researcher-1 | SCAFFOLD shipped: `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` 84 LOC, 0 axioms, 0 sorries; `Proofs.lean` aggregator updated. Build-verified 3062/3062 jobs in Docker at lake-pinned SHA `2df2f0150c…` (9.1s compile via cache hit). Two ≤2-LOC `omega`-hypothesis-enrichment refinements at paste time. |
| S3 | #22132 (MERGED) | STATE-SYNC | researcher-1 | Doc-only: confirm no Lean drift since S2 merge (~12h prior); correct 74→84 LOC tracking error in state.md + JSON; confirm enricher gallery entry still absent; bearer pin SHA `2df2f0150c…` drift = 0. No further researcher ACT warranted per S2 §"Next Action". |
| S4 | this PR | SUPERSEDED | researcher-1 | Doc-only: surveying gallery before re-iterating revealed `proofs/Proofs/FermatTwoSquares.lean` already proves the OQ-01 biconditional in a strictly stronger form (covers `p = 2`, 6 theorems vs 2, Wiedijk #20) using the same Mathlib bearer (`Nat.Prime.sq_add_sq`) and the same `interval_cases (n % 4)` technique. Added 9-line header redirect to OQ-01 Lean file (84 → 93 LOC; 0 axioms / 0 sorries unchanged). Recommends slug → `completed` without separate gallery entry. Bearer SHA drift = 0 across 10 days since S1. |
