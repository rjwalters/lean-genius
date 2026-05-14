# S19 ACT — Formal Statement fix per S18 PREP §1.5 Option A (doc-only)

**Author:** researcher-4
**Timestamp:** 2026-05-14 ~03:30 UTC
**Phase:** Iter 18 S19 ACT — discharge S18 PREP §1.5 Option A (doc-only)
**Iteration:** 18 (post Iter 17 PR #18560 merged 2026-05-13 05:07 UTC,
post S18 PREP PR #18610 merged 2026-05-13 07:02 UTC)

## TL;DR

S18 PREP §1 audited the literal `problem.md` Formal Statement chain
`symBUDim(n,d) ?= buDim(p*,d) = 2⌊d/2⌋ − 1` and flagged it as
**provably inconsistent** at every odd `d ≥ 3` via this file's
axiom-free `symBUDim_lower_z2` (Iter 14, ~6 iterations old) combined
with parent's `buDim_two`. S18 PREP §1.5 recommended Option A: drop
the closed-form decoration from the literal chain.

This S19 ACT executes Option A. The Formal Statement now reads:

> For every n ≥ 2 and d ≥ 1, `symBUDim(n, d) ?= buDim(p*, d)`, where
> `p* = max{p prime : p ≤ n}`.
>
> **Closed form (even d only).** At even d = 2k with k ≥ 1, parent's
> `buDim_prime` gives `buDim(p*, 2k) = 2k − 1`, so the conjecture
> reduces to `symBUDim(n, 2k) ?= 2k − 1`. At odd d ≥ 3, the value of
> `buDim(p*, d)` for odd primes is not currently axiomatised in the
> parent file; see S18 PREP for the audit.

No Lean file is modified. No axiom is added. No sorry is changed.

## Why this S19 ACT now

Iter 17 (PR #18560, merged 2026-05-13 05:07 UTC) established the
even-d / odd-d asymmetry of the conjecture's content: at even d, the
conjecture collapses to a constant via parent's `buDim_prime`; at odd
d for odd primes, parent's cyclic-prime axiom is silent and the
conjecture's non-trivial content lives there.

S18 PREP (PR #18610, merged 2026-05-13 07:02 UTC) audited the
parent-side odd-d gap (designed proposed axiom `buDim_prime_odd` with
Lefschetz fixed-point motivation, ~135 LOC sketch across two Lean
files) AND surfaced a separate, narrower finding: the literal
`problem.md` Formal Statement chain over-claimed at odd d, asserting a
closed-form `2⌊d/2⌋ − 1` that contradicts existing axiom-free
infrastructure.

S18 PREP §6 recommended a two-PR Iter-18 ACT sequence:
1. **PR (1):** `problem.md` fix per §1.5 Option A. Small, low-risk.
2. **PR (2):** parent-side `buDim_prime_odd` axiom + this file's
   downstream PART XXV closure. ~135 LOC, axiom-adding, content-
   collapsing (PARTS VI–XX become decorative).

This session executes **PR (1)** only. **PR (2) is deferred** to a
future session because:
- It is axiom-adding to the parent file (`BorsukUlamOQ02OQ01.lean`,
  `axiomCount 9 → 10`).
- It carries the content-collapse caveat that ~1000 LOC of this
  file's `largestPrimeBelow` machinery (PARTS VI–XX) becomes
  decorative under the natural parent-side completion.
- Multiple recent PRs in this slug shipped as "(build pending)"
  (S13, S14, S15, S17 since Iter-16's "build verified" baseline);
  the cumulative silent-parent-regression risk is moderate (see
  `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`).
  PR (2) should not ship without a fresh Docker build verifying the
  cumulative state.

PR (1) is genuinely useful in its own right and is precondition-free:
the inconsistency it fixes has been latent since Iter-14 (~6
iterations ago), is visible to every reader of `problem.md`, and the
fix is purely textual.

## What changed in this PR

### `problem.md` (doc-only fix)

- **Title heading**: `For S_n, is symBUDim n d = buDim_{largest prime ≤ n} d = 2⌊d/2⌋ − 1?`
  → `For S_n, is symBUDim n d = buDim_{largest prime ≤ n} d?`
  (drops `= 2⌊d/2⌋ − 1` clause from the question).
- **Plain Language paragraph**: reworded to acknowledge that the
  "2k − 1" closed form holds at even d only via Yang-Borsuk, and that
  the odd-d value for odd primes is not currently axiomatised.
- **Formal Statement section**:
  - Conjecture line `symBUDim(n,d) ?= buDim(p*, d) = 2⌊d/2⌋ − 1`
    → `symBUDim(n,d) ?= buDim(p*, d)` (drops the closed-form
    decoration from the literal chain).
  - **New "Closed form (even d only)" paragraph**: explains that the
    `= 2k − 1` qualifier applies only at even d via parent's
    `buDim_prime`, with a pointer to S18 PREP for the audit detail.
    Also explicitly notes the prior literal "= 2⌊d/2⌋ − 1" was
    provably inconsistent at every odd d ≥ 3 (refuted by Iter-14's
    axiom-free `symBUDim_lower_z2` + parent's `buDim_two`) and was
    removed in this S19 ACT.
- **Status section** extended from 2026-05-08 to 2026-05-14:
  - Adds entry for Iter-14's `symBUDim_lower_z2` (the axiom-free
    uniform Z/2 lower bound at all d ≥ 1) — explicitly identified as
    the reason the closed-form decoration had to be dropped.
  - Adds entry for Iter-17 Part XXIV (refutes strict-mono of
    `buDim ∘ largestPrimeBelow` at every even d, axiom-free).
  - Updates Lean file metadata: 241 LOC → 1788 LOC, theoremCount
    pre-Iter-3 → 109 (107 substantive), 1 axiom (unchanged),
    0 sorries (unchanged).
  - Adds a `## Iter 18 S19 ACT (2026-05-14): formal-statement audit
    fix` subsection explaining the rationale for this PR.

Diff: +47/-8 lines on `problem.md`.

### `state.md` (state refresh)

- **Header**: `**Iteration**: 16` → `**Iteration**: 18` (was 2
  iterations stale: Iter-17 had landed mid-state.md without header
  refresh; S18 PREP added a session-file entry without touching
  state.md).
- **Current Focus paragraph** rewritten: was describing Iter-7's
  Z/2 bound as the most-recent advance (out of date by 11
  iterations); now describes Iter-17 Part XXIV + Iter-18 S18 PREP +
  S19 ACT chain.
- **Iteration 18 Builds subsection appended** (~85 lines): describes
  the S19 ACT problem.md fix in the same shape as prior iteration
  entries. Includes a **Path forward post-Iter-18 S19 ACT** block
  ranking the deferred Iter-18 PR (2) (parent-side axiom +
  PART XXV) first, with the build-baseline-check as a hard
  prerequisite. Also flags the symBUDim-side biconditional, concrete
  monotonicity instances, and stretch goals (unchanged).

Diff: +124/-6 lines on `state.md`.

### JSON refresh (`src/data/research/problems/<slug>.json`)

- `currentState.iteration` 16 → 18.
- `currentState.focus` rewritten to S19 ACT outcome.
- `currentState.nextAction` rewritten to post-S19 Path Forward.
- `currentState.phase` remains `ORIENT` (S19 ACT is doc-only; no
  Lean change ⇒ no ACT advance).
- Top-level `phase` already `ORIENT`; consistent with
  `currentState.phase` per
  `feedback_researcher_state_sync_misses_top_level_phase.md`.
- Top-level `lastUpdate` 2026-05-08T18:30:00Z → 2026-05-14T03:30:00Z.
  (Slug has no top-level `lastUpdated` field; preserve schema.)
- `knowledge.progressSummary` rewritten: ACT-DOC framing, notes the
  fix discharges S18 PREP §1.5 Option A and brings `problem.md`
  into consistency with Iter-14's `symBUDim_lower_z2`.

Diff: +5/-5 lines on JSON.

### `sessions/2026-05-14-s19-act-formal-statement-fix-per-s18-prep.md`

This file (new).

## Why this is the right scope

Per CLAUDE.md axiom integrity + S18 PREP §3.4 cost-benefit:
- This PR adds **zero axioms** (parent's axiomCount unchanged at 9;
  this file's at 1).
- This PR changes **zero Lean code** (no risk of silent build break;
  no need for a Docker build cycle).
- This PR fixes a **documented internal inconsistency** between the
  published Formal Statement and the Lean file's own axiom-free
  theorems.
- The S18 PREP itself ranked this fix as PR (1) of two recommended
  Iter-18 ACTs — explicit prior endorsement at the prior session.

Per `feedback_researcher_state_sync_misses_top_level_phase.md`: pre-
claim top-level vs currentState `phase` check passes (both ORIENT
before and after this PR). `lastUpdate` is the only top-level
timestamp field for this slug; updated. State.md header was 2
iterations stale; refresh is in scope and required.

Per `feedback_researcher_state_sync_active_thread_prep_backlog.md`:
this PR is **not** a STATE-SYNC; it's an ACT with content fix
(`problem.md` change) + accompanying state refresh. The 2-per-session
STATE-SYNC cap does not apply.

## What is NOT in this PR

- **PR (2) from S18 PREP §6** (parent-side `buDim_prime_odd` axiom +
  PART XXV closure). Deferred pending fresh Docker build of the
  cumulative Iter-17 state on origin/main + explicit content-collapse
  framing in PR (2)'s docstrings.
- **Lean file changes** of any kind.
- **meta.json** edits in `src/data/proofs/<slug>/`. Lean file is
  unchanged, so `lineCount`, `theoremCount`, `axiomCount`,
  `sorryCount` are unchanged; per
  `feedback_mechanic_linecount_drift_class_unshippable.md` this is
  fine.
- **Iter-17 build verification**. Out of scope for this doc-only
  PR; flagged as a Path-Forward item for a future researcher.

## Counts

- Lean file: 1788 LOC (unchanged), 109 theorems (107 substantive,
  unchanged), 2 definitions (unchanged), 1 axiom (unchanged),
  0 sorries (unchanged).
- `problem.md`: ~70 → ~110 lines.
- `state.md`: 931 → ~1055 lines.
- JSON: 4 string fields touched.

## Build status

No Lean change; no build required. The unchanged
`BorsukUlamOQ02OQ01OQ03OQ02.lean` inherits the Iter-17 "build
pending" status (state.md Iter-17 notes worktree reset mid-iter;
Iter-16 was last "build verified" on 2026-05-12).

A future session running PR (2) should first do a fresh Docker build
of `Proofs.BorsukUlamOQ02OQ01OQ03OQ02` against origin/main to verify
no silent parent-file regression has accumulated across the five
"build pending" PRs since Iter-16's baseline.

## Files

- `research/problems/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/problem.md`
  (formal-statement fix; +47/-8)
- `research/problems/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/state.md`
  (header bump + Iter-18 ACT section; +124/-6)
- `research/problems/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/sessions/2026-05-14-s19-act-formal-statement-fix-per-s18-prep.md`
  (this file; new)
- `src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-03-oq-02.json`
  (currentState iteration + focus + nextAction +
  knowledge.progressSummary + top-level lastUpdate; +5/-5)
