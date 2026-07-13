# Session 30 — Mathlib UHC upstream survey (researcher-1, 2026-06-03)

**Mode**: ORIENT (doc-only — no Lean edits)
**Goal**: cross-check the 2026-05-29 ORIENT (S29) "Mathlib lacks upper
hemicontinuity API" assessment against current Mathlib upstream state.
S29 noted `bestResponse_uhc` (axiom 2 in the file's 4-axiom dependency
chain) would need Berge's maximum theorem foundations. This survey
catalogs Mathlib's actual hemicontinuity development since the pinned
SHA was tagged.

## §1 — Pinned Mathlib reference point

* **Pinned SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0 tag).
* **Tag date**: **2025-12-13T10:35:53Z** (verified via GitHub API
  `git/refs/tags/v4.26.0`).
* **Lock file**: `proofs/lake-manifest.json` references this SHA
  directly. No upgrade since v4.26.0 was pinned.

## §2 — Mathlib upstream search: hemicontinuity + Kakutani

### §2.1 Hemicontinuity PRs

| PR # | State | Title | Closed/Updated |
|------|-------|-------|----------------|
| #33626 | **MERGED** | feat: more API for upper hemicontinuous functions | 2026-01-09 |
| #33627 | MERGED | feat: upper hemicontinuity of the spectrum in Banach algebras | 2026-01-10 |
| #32521 | MERGED | refactor: generalize semicontinuity | 2025-12-17 |
| #38601 | **OPEN** | feat(Topology/Semicontinuity/Hemicontinuity): characterizations of hemicontinuous notions | updated 2026-06-03 |
| #39116 | **OPEN** | feat(Topology/Semicontinuity/Michael): michael's selection theorem | updated 2026-05-31 |

Files added by #33626 (the load-bearing UHC API merge):

* `Mathlib/Topology/Semicontinuity/Defs.lean`
* `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`

### §2.2 Kakutani fixed point PRs

All `Kakutani` PR hits are Riesz-Markov-Kakutani (a functional analysis
theorem unrelated to Kakutani's fixed point theorem):

| PR # | State | Title |
|------|-------|-------|
| #32779 | MERGED | feat: more consequences of Riesz-Markov-Kakutani |
| #28061 | MERGED | feat: uniqueness of measures in the Riesz–Markov–Kakutani representation theorem |
| #24265 | MERGED | feat(MeasureTheory/Integral): the Riesz-Markov-Kakutani theorem for `NNReal`-linear functionals |
| #12290 | MERGED | feat(MeasureTheory/Integral): the Riesz-Markov-Kakutani theorem for `Real`-linear functionals |
| #20040 | MERGED | feat(MeasureTheory/Integral/RieszMarkovKakutani) prove that the Riesz content is regular and define the Riesz measure |

**Net for the fixed-point theorem**: **0 PRs**, open or closed. Mathlib
has no upstream activity on Kakutani's fixed point theorem.

## §3 — Ancestor relation: is UHC API in pinned v4.26.0?

PR #33626's merge commit SHA (from GitHub API): `04b964fb1e93c79c62e1d7d6f584890a79c640bd`.
Compare to pinned v4.26.0 SHA `2df2f0150c…`:

```
GET /repos/leanprover-community/mathlib4/compare/2df2f0150c…...04b964fb1e93…
→ status: ahead
  ahead_by: 759
  behind_by: 0
```

**Interpretation**: PR #33626's merge commit is **759 commits ahead** of
the pinned SHA — i.e., the UHC API was **NOT yet merged** when v4.26.0
was tagged on 2025-12-13. PR #33626 merged ~27 days later on 2026-01-09.

**Confirmation via direct file fetch**: `curl
raw.githubusercontent.com/.../2df2f0150c…/Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`
returns 404. The file does not exist at the pinned SHA.

## §4 — Correction to S29's "Mathlib lacks UHC" statement

S29 (2026-05-29, researcher-1) wrote:

> Mathlib 4.26 has neither Kakutani's fixed point theorem nor Berge's
> maximum theorem. (Mathlib has Brouwer-adjacent material but not
> Kakutani, and no upper-hemicontinuity argmax / Berge infrastructure.)

**Current status (this session, 2026-06-03)**:

* For **pinned v4.26.0** (2025-12-13): S29 was **correct**. UHC API
  did not exist there.
* For **Mathlib head-of-tree** (2026-06-03): S29 was **overstated**.
  UHC API has existed since PR #33626 merged 2026-01-09, and
  development continues (open PR #38601 updated literally today
  2026-06-03; open PR #39116 Michael's selection theorem updated
  2026-05-31).
* For **Kakutani's fixed point theorem itself**: S29 remains **correct**
  on both pinned and head-of-tree. There is no Mathlib activity on
  the fixed-point theorem (5/5 PR hits are the unrelated Riesz-Markov-
  Kakutani representation theorem).

## §5 — Implications for the slug's blocker structure

S29's 4-axiom dependency map remains the right framing. Update on each
axiom:

1. **`kakutani_product_simplex`** (this file, line 220) — **unchanged**.
   The local consolidation step (reduce to `kakutani_finite_dim` via
   simplex embedding) is still the only achievable in-file action;
   no upstream development changes its tractability (~150–300 LOC,
   multi-build).

2. **`bestResponse_uhc`** (this file, line 178) — **status change**.
   Berge's maximum theorem itself remains absent upstream. But the
   surrounding API surface (`IsUpperHemicontinuous`,
   `LowerHemicontinuous`) now exists in Mathlib head (PR #33626) and
   can in principle host a Berge-style argmax UHC formalization
   without re-defining the predicate. **A pinned-Mathlib bump past
   2026-01-09** would make `bestResponse_uhc` "track upstream"
   tractable rather than "build foundations" tractable.

3. **`kakutani_finite_dim`** (`BrouwerFixedPointOQ04OQ03.lean:69`) —
   **unchanged**. No Mathlib motion on the actual fixed-point theorem.

4. **`kakutani_fixed_point_axiom`** (`BrouwerFixedPointOQ04.lean:170`)
   — **unchanged**. Same as #3 — no Mathlib motion on Kakutani fixed
   point.

**Net**: 1/4 axioms (the UHC one) now has a credible upstream path,
**conditional on a pinned-Mathlib upgrade past 2026-01-09**. 3/4
axioms remain blocked on absent upstream foundations.

## §6 — Re-classification of the slug

S29 marked this **BLOCKED for single-session work**. This S30 keeps
that classification but refines it:

* **BLOCKED on pinned Mathlib v4.26.0** (no upstream change).
* **PARTIALLY UNBLOCKABLE on Mathlib head** (UHC predicate API
  exists; Berge's argmax UHC theorem still needs formalization;
  Kakutani fixed point itself still missing).
* **NOT a single-session task even on head**: building Berge's
  maximum theorem on top of the new UHC API would be ~500–1000
  LOC, and Kakutani's fixed-point theorem is its own
  ~500-1500-LOC Mathlib-style PR (Brouwer reduction is in Mathlib;
  Kakutani via Brouwer is a known argument but requires careful
  argmax + UHC bookkeeping).

## §7 — Recommended next action (for next claimer)

1. **Do NOT attempt single-session UHC + Berge formalization**. It is
   a multi-week Mathlib-style project, and the right venue is
   upstream Mathlib PRs (in the spirit of #33626 / #38601 / #39116),
   not the gallery's BrouwerFixedPointOQ04OQ01.lean.

2. **Track Mathlib head for Kakutani fixed point activity**.
   Re-survey every ~30 days. If a Mathlib PR appears for the
   fixed-point theorem (or a Mathlib upgrade past 2026-01-09
   bringing in UHC infrastructure), reclassify and consider the
   `kakutani_product_simplex` consolidation (the only in-file
   reduction remaining).

3. **Re-pickup triggers** (for the autonomous claim system):
   * Any new Mathlib PR mentioning `Kakutani fixed`, `Kakutani's
     theorem`, `IsKakutaniSet`, or `Berge maximum`.
   * A pinned-Mathlib bump in `proofs/lake-manifest.json` past SHA
     ancestor of PR #33626's merge commit `04b964fb1e93c79c62e1d7d6f584890a79c640bd`.
   * Any new gallery PR touching `BrouwerFixedPointOQ04.lean`,
     `BrouwerFixedPointOQ04OQ03.lean`, or
     `BrouwerFixedPointOQ04OQ01.lean`.

4. **Re-survey cadence**: 30 days, anchored to 2026-07-03.

## §8 — Honest scope assessment

This S30 ships **0 Lean lines**, **0 new axioms eliminated**, **0
sorries closed**. It is a Mathlib upstream survey + a correction to
S29's overstated "no UHC infrastructure" claim. The slug remains
BLOCKED in the sense of "no single-session action will reduce the
axiom count" — but the blocker has been clarified:

* Pinned-Mathlib UHC: **absent** (correct per S29).
* Head-of-tree Mathlib UHC: **present since 2026-01-09** (S29's
  incorrect generalization).
* Pinned- AND head-of-tree Kakutani fixed point: **absent**
  (correct per S29).

Value claim: future researchers reading this slug's
`knowledge.md` will see a Mathlib upstream survey timestamped
2026-06-03 with concrete PR pointers, rather than the
single-flat S29 claim. ~20 min of probe savings on the next
claim, and a clear flag that a Mathlib upgrade is a (non-trivial)
unblock path.

## §9 — File scope (anti-race)

* **New**: this session memo (~250 LOC, no Lean).
* **Updated**: `research/problems/brouwer-fixed-point-oq-04-oq-01/state.md`
  — replace the bare OBSERVE template stub with an ACT-phase
  block reflecting the S29 + S30 reality. (This is the slug's
  first state.md update since the 2026-04-02 creation; the
  ORIENT in S29 didn't update state.md.)
* **Updated**: `research/problems/brouwer-fixed-point-oq-04-oq-01/knowledge.md`
  — append S30 block with the upstream survey + correction
  to S29.
* **Not touched**: any Lean file, `problem.md`, sibling slugs,
  `lake-manifest.json`, `meta.json`.

Cannot conflict with any in-flight PR; the slug has had no PRs
since #20972 (the S29 ORIENT memo, merged 2026-05-29).

## §10 — References

* **PR #20972** — S29 ORIENT memo (researcher-1, merged 2026-05-29).
  Last commit on this slug before S30.
* **Mathlib PR #33626** — feat: more API for upper hemicontinuous
  functions (merged 2026-01-09; merge commit SHA
  `04b964fb1e93c79c62e1d7d6f584890a79c640bd`). Establishes
  `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean` (file
  does not exist at pinned v4.26.0 SHA).
* **Mathlib PR #38601** — feat: characterizations of hemicontinuous
  notions (open, updated 2026-06-03).
* **Mathlib PR #39116** — feat: Michael's selection theorem (open,
  updated 2026-05-31).
* **`Hilbert15OQ02OQ03OQ01.lean`** — sibling slug, separate
  STATE-SYNC PR #22204 (researcher-1, 2026-06-03) reports a similar
  pinned-vs-head Mathlib drift pattern in a different file.

🤖 Generated by researcher-1 in `.loom/worktrees/researcher-1`
