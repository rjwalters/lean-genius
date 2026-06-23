# S7 ACT — Path B (mixed-down alphabet) cycle-lemma equality, via overlay stack

**Slug**: `ballot-problem-oq-01-oq-01-oq-02-oq-01`
**Researcher**: researcher-3
**Date**: 2026-05-15 ~02:00 UTC
**Mode**: ACT (Lean source PR), via mechanic-PR overlay pattern
**Status**: Path B Lean source added (+155 LOC), Docker-build **clean (3062 jobs)**.

## §1 Context: deployer stall + S6/S7 PR chain stuck

Pre-claim survey (2026-05-15 ~01:58 UTC):

- `gh pr list -R rjwalters/lean-genius --state merged --limit 1` last merge:
  `2026-05-14T03:04:07Z` — **~22.9 h** zero-merge window.
- `gh pr list -R rjwalters/lean-genius --state open --json mergeStateStatus`:
  **30** OPEN PRs, all `mergeStateStatus: CLEAN` — system-wide deployer stall
  matching memory pattern
  `feedback_researcher_deployer_stall_coordination_prep_pattern.md`.
- Slug-specific OPEN PRs (already documented by S6 ACT body and S7 PREP §1.1):
  - **PR #19015** — S6 ACT (Conjecture E + 2× `linarith→omega`), MERGEABLE,
    Docker `3062 jobs` clean. Modifies `BallotProblemOQ01OQ01OQ02OQ01.lean`,
    `state.md`, slug JSON.
  - **PR #19172** — S7 PREP (Path B line-by-line transfer audit), MERGEABLE,
    doc-only.

S7 PREP §6 recommended **Option A** (wait for #19015, ACT off `main`), with
**Option B** (overlay-build per
`feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`) gated on
"if Option A stalls." The 22.9 h zero-merge window satisfies that gate.

## §2 Approach: overlay #19015 + #19172, append Path B, build-verify, ship Lean-only delta

The PR's `git diff` vs `main` includes:

- `BallotProblemOQ01OQ01OQ02OQ01.lean` — composite (#19015's S6 ACT diff +
  Path B's additions). When #19015 merges, `git rebase main` reduces this to
  **only Path B's delta**.
- This session doc — purely additive, no conflict surface.

I deliberately **reverted** the overlay's edits to `state.md`, slug JSON,
and the two upstream session docs (`2026-05-14-s6-act-...md`,
`2026-05-14-s7-prep-...md`) so that **the only files my PR touches are**
the Lean file and my own session doc. This keeps the PR self-contained and
minimises rebase conflict surface.

## §3 Path B Lean source (appended to `BallotProblemOQ01OQ01OQ02OQ01.lean`)

Path B implements S7 PREP §3's transfer template verbatim. Per-lemma LOC
budget (S7 PREP §3.7) matched within ±10 LOC:

| Component | S7 PREP estimate | Actual |
|---|---:|---:|
| `levelPosB` + 6 private helpers | ~30 | 35 |
| `levelPosB_eq` (Path B variant of `levelPos_eq`) | ~22 | 25 |
| `goodRotations_card_ge_pathB` | ~30 | 35 |
| `step_in_one_pos_mixed_neg_card_eq` (main, public) | ~12 | 8 |
| `step_in_one_pos_mixed_neg_card_bound` (slack-form corollary) | ~8 | 14 |
| Section docstring | — | 24 |
| **Total** | **~102** | **~141** |

### 3.1 Public theorems added

The two public theorems exported by Path B (declared inside namespace
`BallotMJumpCycleLemma`, opening `GeneralizedBallot`):

- `step_in_one_pos_mixed_neg_card_eq` — strict equality:
  `(goodRotations l).card = l.sum.toNat`, under `hmem : ∀ x ∈ l, x = 1 ∨
  (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ))` and `hS : 0 < l.sum`.
- `step_in_one_pos_mixed_neg_card_bound` — slack-form corollary:
  `l.sum ≤ (m : ℤ) * (goodRotations l).card + ((m : ℤ) - 1) * l.length`,
  same hypothesis + `hm : 1 ≤ m`.

The strict equality dominates the slack form: when `m ≥ 1`, both sides agree
at `m = 1` (recovering the parent's unit-decrement count) and the slack
grows linearly in `m`.

### 3.2 Critical adaptation (S7 PREP §3.2 verbatim)

Parent `levelPos_eq` (`BallotProblemOQ01.lean:715`) uses
`rcases hmem ... with h1 | hk` to split on `x = 1 ∨ x = -(k : ℤ)`.
Path B's `levelPosB_eq` destructures the existential:
`rcases hmem ... with h1 | ⟨k, _hk_lo, _hk_hi, hx_eq⟩`.

The `linarith [show (0 : ℤ) ≤ (k : ℤ) from Int.natCast_nonneg k]` discharge
preserves because `k` is now the bound `ℕ` from the existential rather than
an implicit `ℕ` parameter — `Int.natCast_nonneg` resolves identically.

The bounds `1 ≤ k` and `k ≤ m` are **underscored away** (`_hk_lo`, `_hk_hi`).
Path B's argument is therefore valid for any mixed-down alphabet
`x = 1 ∨ ∃ k ∈ ℕ, x = -k` (S7 PREP §3.2 honesty note).

## §4 Docker-build verification

Build command: `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ01OQ01OQ02OQ01`.

Log: `.loom/logs/researcher-3-ballot-pathB-build1.log` (13117 bytes).

**Outcome**: **build clean** — `Build completed successfully (3062 jobs).`
Final job line: `✔ [3062/3062] Built Proofs.BallotProblemOQ01OQ01OQ02OQ01 (2.0s)`.

Build was run with both overlays (#19015 + #19172) applied to the working
tree, so the verification is for the **composite** post-#19015-merge +
Path B state.

**Net delta** (post-overlay file `BallotProblemOQ01OQ01OQ02OQ01.lean`):
`312 → 472 LOC` (+160 LOC, including section header). Path B is appended
after `end BallotMJumpCycleLemma` at line 311 in the post-#19015 baseline,
followed by a blank line + Path B content + final `end BallotMJumpCycleLemma`.

## §5 Post-merge sequencing

This PR depends on:

1. **PR #19015** (S6 ACT) — merge first; supplies Conjecture E discharge +
   linarith→omega fixes in `BallotProblemOQ01OQ01OQ02OQ01.lean` lines 121,
   225 and new Conjecture E section (lines 226–311). Path B appends after.
2. **PR #19172** (S7 PREP) — merge in any order; doc-only.
3. **This PR (S7 ACT)** — merges last; introduces only the Path B section
   and this session doc.

If the deployer merges #19015 first then this PR, the rebase produces a
clean PR diff containing only Path B + this session doc.

If the deployer merges this PR first (out of recommended order), a manual
conflict resolution will be needed on `BallotProblemOQ01OQ01OQ02OQ01.lean`
where the linarith→omega fixes and Conjecture E section land in the same
file. The Path B section is independent (no shared identifiers with
Conjecture E or with the linarith→omega fixes), so the resolution is
textual concatenation, not semantic re-derivation.

## §6 Files in this PR

Touched (composite with overlays):

- `BallotProblemOQ01OQ01OQ02OQ01.lean` (+248/-3): overlay #19015 (lines 121,
  225, 226–311) plus **Path B (lines 313–472)**.
- `sessions/2026-05-15-s7-act-path-b-overlay-stack.md` (new, THIS PR).

Deliberately NOT in this PR (would conflict with #19015 on merge):

- `state.md` — refresh deferred to a post-merge STATE-SYNC.
- `<slug>.json` — refresh deferred to a post-merge STATE-SYNC.
- `sessions/2026-05-14-s6-act-...md` — #19015's session doc.
- `sessions/2026-05-14-s7-prep-...md` — #19172's session doc.

## §7 Honest contribution boundary

What this session **does**:

- Implements S7 PREP §3 transfer template verbatim as Lean source (~141 LOC
  including docstring), preserving the per-lemma adaptation (single
  `rcases` destructure + label rename) called out by S7 PREP.
- Provides **Docker-build verification** (3062 jobs clean) of the composite
  post-#19015 + Path B state before claiming ACT-success.
- Documents the stacked-PR strategy + per-merge-order rebase behaviour.

What this session **does NOT** do:

- Does **not** prove Path A (full two-sided alphabet `-m ≤ x ≤ m`). Path A
  requires a new `windowPos_good` lemma (~200 LOC of new mathematics per
  S5 PREP §3.1) that does **not** transfer from the parent. Path A remains
  open research.
- Does **not** update `state.md` / `<slug>.json` (intentional — see §6
  conflict avoidance).
- Does **not** attempt to merge ahead of #19015 / #19172.

## §8 References

- **PR #19015** (S6 ACT, researcher-12, 2026-05-14T07:19Z, MERGEABLE):
  S6 ACT discharging Conjecture E + 2× linarith→omega build unblockers.
- **PR #19172** (S7 PREP, researcher-8, 2026-05-14T23:53Z, MERGEABLE):
  S7 PREP Path B (mixed-down alphabet) transfer audit, line-by-line.
- Parent file: `proofs/Proofs/BallotProblemOQ01.lean` — `cycle_lemma` line
  764, `levelPos_eq` line 703, `goodRotations_card_ge` line 731.
- Memory feedback: `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`,
  `feedback_researcher_deployer_stall_coordination_prep_pattern.md`.
