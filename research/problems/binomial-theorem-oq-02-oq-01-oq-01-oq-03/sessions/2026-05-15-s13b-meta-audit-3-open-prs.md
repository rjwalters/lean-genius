# Session 13b — Meta-audit of three open doc-only PRs on this slug + independent bearer corroboration

**Date**: 2026-05-15 ~08:00 UTC
**Researcher**: researcher-9
**Mode**: META-AUDIT (doc-only, conflict-free) + independent bearer corroboration
**Trigger**: post-claim sibling-PR check revealed THREE open MERGEABLE/CLEAN
doc-only PRs on this slug (#19018 + #19138 + #19249), with #19138 and #19249
covering the **same core finding** (Mathlib CLT phantom at v4.26.0 pin).
Pattern matches the documented "duplicate-S2-ACT race" trap; the appropriate
response is a doc-only audit recommending merge order rather than a fourth
duplicate.

**Mathlib pin**: lake-pinned v4.26.0, SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`proofs/lake-manifest.json`).

---

## §1 — The three open PRs on this slug

| PR | Author | Opened | LOC | Files | Mergeable | Core scope |
|---|---|---|---|---|---|---|
| **#19018** | researcher-9 | 2026-05-14T07:44Z | +8/-11 | `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json` | MERGEABLE/CLEAN | S13 STATE-SYNC: post-S12 JSON `cs.*` refresh |
| **#19138** | researcher-3 | 2026-05-14T21:25Z | +365/-0 | `knowledge.md` (+62), `sessions/2026-05-14-s14-prep-mathlib-v426-clt-bearer-audit.md` (new, +303) | MERGEABLE/CLEAN | S14 PREP: CLT-bearer audit; 5 bearers verified, 3 absences; 3-path recommendation (defer / local charFun / Mathlib bump) |
| **#19249** | researcher-3 | 2026-05-15T04:56Z | +370/-0 | `sessions/2026-05-15-s13-prep-clt-bearer-audit.md` (new) | MERGEABLE/CLEAN | S13 PREP: CLT-bearer audit; 14 bearers verified, 4 absences; 3-option recommendation (Mathlib bump / axiom rebase / doc-only); Lemma C + Lemma A skeletons drafted |

**Source verification commands** (all run 2026-05-15 ~07:55Z):

```bash
gh pr list --repo rjwalters/lean-genius --search "binomial-theorem" --state open
gh pr view 19018 --repo rjwalters/lean-genius --json files,mergeable,mergeStateStatus
gh pr view 19138 --repo rjwalters/lean-genius --json files,mergeable,mergeStateStatus
gh pr view 19249 --repo rjwalters/lean-genius --json files,mergeable,mergeStateStatus
```

Both PR #19138 and #19249 are by the same author (researcher-3), opened ~7.5
hours apart. Body of #19249 states "0 open PRs at claim time" — the
sibling-PR existence check missed #19138. This is the documented
duplicate-research-PR-race anti-pattern.

## §2 — Head-to-head comparison of #19138 and #19249

Both PRs find the same primary result (Mathlib CLT phantom at v4.26.0) via
independent `gh api` queries. They differ in depth and scope:

| Dimension | #19138 (S14, older) | #19249 (S13, newer) |
|---|---|---|
| Body LOC | 365 (knowledge.md +62 + new file +303) | 370 (single new file) |
| Bearers pin-verified | 5 (Portmanteau, frontier_Iic, gaussianReal, PMF.binomial, HasOuterApproxClosed) | 14 (above + TendstoInDistribution + Slutsky + continuous mapping + HasLaw + IdentDistrib + iIndepFun + NoAtoms + IsProbabilityMeasure + …) |
| Negative findings | 3 (`Mathlib.Probability.CentralLimitTheorem`, `iid_central_limit_theorem`, `Mathlib.Probability.Distributions.Binomial`-as-Measure) | 4 (above + `CharacteristicFunction/`, `LevyConvergence.lean`) |
| Discharge paths | 3: defer / local charFun / Mathlib bump | 3: Mathlib bump / axiom rebase / doc-only |
| Lemma skeletons drafted | None — only path recommendation | **Lemma C (Portmanteau bridge) ~25–40 LOC** + Lemma A (Bernoulli→Binomial bridge) sketch ~80–150 LOC |
| Updates knowledge.md | YES (+62 LOC) | NO |
| Recommended action | **Defer** (Option 1, conservative — keep axiom as-is) | **Doc-only PREP (Option C)** (this very PR) |
| Cited absent files | 1 file + 1 symbol | 3 files + transitive dependency chain |

**Substantive overlap**: The core finding is the same — `Mathlib/Probability/
CentralLimitTheorem.lean` does not exist at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Both PRs verify this via
direct `gh api ?ref=<SHA>` round-trips and confirm 404.

**Substantive differences**: #19249 goes deeper on bearer transitivity (the
file's would-be proof dependencies are also absent: `CharacteristicFunction/`,
`LevyConvergence.lean`) and ships **Lemma C** skeleton (the Portmanteau bridge
itself), which is independently provable at SHA and useful regardless of
which discharge path is taken. #19138 ships a knowledge.md edit (62 LOC)
that lands the finding in the canonical knowledge record visible to all
future researchers; #19249 only adds a session file.

**Conflict surface**: ZERO. The two sessions files have distinct names
(`2026-05-14-s14-prep-…` vs `2026-05-15-s13-prep-clt-…`), and only #19138
edits `knowledge.md`. The PRs are pairwise non-conflicting; either order
yields a clean merge of both. #19018's JSON delta is also non-conflicting
with both.

## §3 — Recommended merge order

**Recommendation: merge all three (#19018 → #19138 → #19249) in chronological
open order.**

| Step | PR | Justification |
|---|---|---|
| 1 | #19018 (oldest, smallest) | JSON state-sync is a small `cs.*` refresh; lands the post-S12 BUILD-VERIFIED status into the JSON record. Zero risk. |
| 2 | #19138 | Lands the **canonical finding** into `knowledge.md` (+62 LOC) where all future researchers will see it. Without #19138, the finding stays buried in `sessions/` and is invisible to standard knowledge-tier scans. |
| 3 | #19249 | Adds **deeper bearer transitivity** + **Lemma C skeleton** that #19138 doesn't have. Complements #19138 rather than duplicates it once #19138's knowledge.md update lands. |

**Alternative — minimal-merge option**: If the deployer prefers to merge
only two (skipping #19249 as substantively duplicative of #19138), the
deferred work is the Lemma C skeleton. That skeleton is independently
provable at SHA from B1+B2+B11 (~25–40 LOC) and provides immediate value
for any future ACT regardless of discharge path. Therefore #19249 should
NOT be closed even if perceived as duplicative — its Lemma C skeleton is
the load-bearing artefact.

**No-merge alternative considered and rejected**: Closing #19249 as a
duplicate of #19138 throws away the Lemma C skeleton and the deeper
bearer-transitivity tables. Net value cost is ~150 LOC of audit detail.
The maintenance cost of merging both is essentially zero (independent
files, no rebase friction).

## §4 — Independent bearer corroboration (researcher-9, third-party)

This META-AUDIT independently re-ran the bearer queries that
#19138/#19249 cite, to provide a third-party verification of the
phantom-CLT finding. Round-trips run 2026-05-15 ~07:30Z from
worktree `.loom/worktrees/researcher-9/`:

| Bearer | Status at SHA `2df2f0150c…` | Citation |
|---|---|---|
| `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` | ✓ present | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:350` |
| `frontier_Iic [NoMaxOrder α]` | ✓ present | `Mathlib/Topology/Order/DenselyOrdered.lean:149` |
| `HasOuterApproxClosed` instance for `PseudoMetrizableSpace` | ✓ present | `Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean:217` |
| `Mathlib/Probability/CentralLimitTheorem.lean` (the file) | ✗ **ABSENT** | `gh api …/contents/…?ref=2df2f015…` returns 404; recursive tree listing of `Mathlib/Probability/` at this SHA confirms no file matches `Central` |
| `iid_central_limit_theorem` (symbol) | ✗ **ABSENT** | `gh api search/code` returns 0 hits in v4.26.0 tree |
| `tendstoInDistribution_inv_sqrt_mul_sum` (symbol) | ✗ **ABSENT** | `gh api search/code` returns hits **only on Mathlib HEAD** (post-v4.26.0); 0 hits at pinned SHA |

**Verdict**: Both sibling PRs are CORRECT. The Mathlib CLT is genuinely
absent at v4.26.0, and the S9 discharge plan is invalid as written.
Third-party corroboration from researcher-9 worktree confirms the finding.

### One refinement of #19138's table

#19138's audit at line ~107 cites `HasOuterApproxClosed ℝ` as automatic
via the `PseudoMetrizableSpace` instance. The instance is at line **217**
of `Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`, NOT line
**31** as one earlier session log cited (S9 knowledge.md). #19138's body
states "Auto" without a line number; this is correct but understates
where the instance actually lives. #19249 §2 bearer table also doesn't
cite the exact instance line. Recommend (advisory only): future S(N+)
ACT should cite `:217` for the instance to keep the bearer-audit trail
sharp. No PR-merge implication.

### One observation for sibling #19249

#19249's body claims "0 open PRs at claim time" but #19138 was open ~7.5
hours earlier on the same slug. The sibling-PR check missed #19138. This
is a process-level finding that should inform future researcher-3
sessions on this slug (and is the recurring pattern that motivates this
meta-audit). No technical implication for the PR's content — the bearer
findings are independently correct.

## §5 — Why doc-only meta-audit (and what this PR explicitly does NOT do)

This META-AUDIT is strict conflict-free with all three sibling PRs:

- **New file only**: `sessions/2026-05-15-s13b-meta-audit-3-open-prs.md`.
- **No edits to** `state.md` (all 12 prior sessions preserved verbatim).
- **No edits to** `knowledge.md` (avoiding conflict with #19138's
  knowledge.md edit on the same file).
- **No edits to** `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json`
  (avoiding race with #19018's JSON state-sync edit).
- **No edits to** `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` or any
  `src/data/proofs/` file (preserving S12 BUILD VERIFIED).
- **No new `_loom/` labels added.**
- **No `loom:review-requested`** added (math agent per `CLAUDE.md`).

Pairwise non-conflicting with: #19018 (file disjoint), #19138 (file
disjoint), #19249 (file disjoint). Mergeable in any order with all three.

What this PR EXPLICITLY does NOT do:
- Does NOT close, reject, or label any sibling PR.
- Does NOT re-do the bearer-existence audit (#19138 and #19249 already
  did it, this PR only third-party corroborates).
- Does NOT pick between the path recommendations (defer / Mathlib bump /
  axiom rebase) — that's a gallery-policy call.
- Does NOT touch the prepared "Path A bridge lemma" skeleton from #19249
  §4 — that skeleton is the load-bearing artefact and should land
  whether or not this meta-audit does.

## §6 — Recommended deployer action

1. **Merge #19018 first** (smallest, oldest, JSON-only, blocks nothing).
2. **Merge #19138 second** (lands canonical finding in `knowledge.md`).
3. **Merge #19249 third** (adds depth + Lemma C skeleton, builds on #19138).
4. **Then** (optional, post-merge cleanup) merge this meta-audit if
   considered useful; otherwise close as informational-only since once
   #19138/#19249 land the meta-audit content is partially redundant with
   the merged knowledge.md.

If only one of #19138 / #19249 can be merged due to other constraints:
prefer **#19249** because it ships the **Lemma C bridge-lemma skeleton**
that #19138 lacks. The Lemma C skeleton is the artefact a future S14
ACT will transcribe; without it, ACT will reconstruct the same 25–40 LOC
from scratch. With #19249 landed, the next ACT is a 1-Docker-iter mechanical
paste.

## §7 — Generalisation: feedback hook for sibling-PR check process

The duplicate-PREP-by-same-author race here (researcher-3 opening #19138
at 21:25Z then #19249 at 04:56Z on the same slug, with #19249's body
asserting "0 open PRs") suggests the sibling-PR-existence check in the
researcher workflow needs strengthening for cases where:

1. Same author returns to same slug within ~12 hours.
2. Search query is by branch name rather than slug pattern.

This meta-audit treats the duplicate as a feature (both PRs add value)
rather than a bug to close. But the underlying process gap is worth
flagging. Suggested feedback memory pattern key:
`feedback_researcher_sameauthor_duplicate_prep_within_12h_recommends_merge_both_not_close_either`.

## §8 — References

| Reference | Source |
|---|---|
| Lake manifest pin | `proofs/lake-manifest.json` line citing `mathlib`'s `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| Mathlib v4.26.0 Portmanteau | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:350` (verified at SHA via `gh api`) |
| Mathlib v4.26.0 frontier_Iic | `Mathlib/Topology/Order/DenselyOrdered.lean:149` (verified at SHA via `gh api`) |
| Mathlib v4.26.0 HasOuterApproxClosed instance | `Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean:217` (verified at SHA via `gh api`) |
| Sibling PR #19018 (STATE-SYNC) | https://github.com/rjwalters/lean-genius/pull/19018 |
| Sibling PR #19138 (S14 PREP) | https://github.com/rjwalters/lean-genius/pull/19138, head `09e9590328…` |
| Sibling PR #19249 (S13 PREP) | https://github.com/rjwalters/lean-genius/pull/19249, head `5e647cfeb1…` |
| Memory pattern (sibling-audit-merge-order) | `feedback_researcher_duplicate_act_race_audit_with_bundled_crossslug_commit_recommend_first_pr.md` (similar pattern: 2 open PRs on same slug, ship doc-only audit recommending merge order) |
| S12 BUILD VERIFIED state | `state.md` §"Session 12 Focus" (2026-05-13, researcher-9) |
| S9 original bridge-lemma plan | `knowledge.md` §"The Bridge Lemma S10 Should Add" (2026-05-08, researcher-8) |

## §9 — Session metadata footer

- **Researcher**: researcher-9 (worktree `.loom/worktrees/researcher-9/`)
- **Branch**: `research/binomial-theorem-oq02oq01oq01oq03-s13-prep-1778835584` (renamed conceptually to S13b meta-audit)
- **PR type**: doc-only meta-audit (~210 LOC markdown, 0 LOC Lean)
- **Build verification**: not required (no Lean modifications)
- **Conflict-free**: ✓ with #19018, #19138, #19249 (file-disjoint)
- **Releases the claim on**: `binomial-theorem-oq-02-oq-01-oq-01-oq-03`
- **Action queued for deployer**: merge #19018 → #19138 → #19249 → (optionally) this PR; or skip this PR if redundant
- **Pin-table corroboration runs**: 6 `gh api` round-trips at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, all agreeing with the sibling PRs' findings
