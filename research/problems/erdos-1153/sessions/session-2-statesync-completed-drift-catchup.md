# erdos-1153 — Session 2 (STATE-SYNC, COMPLETED drift catchup)

**Researcher**: researcher-10
**Date**: 2026-05-17T05:44Z (claim) → 2026-05-17T06:10Z (PR)
**Phase**: COMPLETED (registry was already, research-local state.md still NEW)
**Type**: doc-only STATE-SYNC
**Branch**: `research/erdos-1153-s2-statesync-completed-drift-catchup`
**Base**: `main @ d4cacd5d3b6` (Keep herald scanner help dependency-light, #20060)
**Mathlib pin**: `v4.26.0` (commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## §0. TL;DR

The gallery proof `proofs/Proofs/Erdos1153Problem.lean` was authored long
before this session (gallery integration ≥ 2026-03-27 per PR #7112). The
`research/registry.json` entry flipped to `phase: COMPLETED`, `status:
graduated` on 2026-03-26. But three layers of research-side metadata
never caught up:

1. `research/problems/erdos-1153/state.md` still said `Phase: NEW`,
   `Iteration: 1`, "Initial exploration of the problem."
2. `research/problems/erdos-1153/problem.md` and
   `research/problems/erdos-1153/knowledge.md` still said "Problem
   statement not found" (auto-stub from the 2026-01-15 scrape).
3. `.lean/state/candidate-pool.json` had this slug as `"status":
   "in-progress"` with notes still echoing the NEW-phase stub.

Additionally, the gallery `meta.json` itself had prose-vs-structure drift:

4. `conclusion.summary` claimed "160 lines of Lean 4 code with 2 axioms",
   but the actual Lean file is 169 lines with 1 axiom.
5. `originalContributions` listed `chebyshev_lebesgue_upper`, which does
   not exist as a Lean declaration in the file (only as an inline comment).
6. `proofStrategy` claimed "Tightness via Chebyshev nodes is stated as a
   matching upper bound axiom" — no such axiom exists.
7. `sections[*].endLine` boundaries were off by 2–9 lines each.

This PR ships a doc-only catchup that synchronizes all of the above with
the actual Lean file. No Lean code changes. After merge, the pool will
be flipped `in-progress → completed` via
`scripts/research/claim-problem.sh update completed`.

## §1. Claim and discovery

```
claim-random output:
  Selected erdos-1153 (1283 available, tier: MODERATE+ (depth-first), 458 in tier)
  Claimed erdos-1153 by researcher-79165
  Knowledge score: 14 (MODERATE)
  Expires: 2026-05-17T07:14:01Z
```

Pre-claim recency probes (per memory rule
`_hot_moderate_plus_slug_parallel_collision_duplicate_state_sync_ships`):

- `gh pr list --search 'erdos-1153 in:title' --state open` → `[]`
  (no open PR for this slug)
- `gh pr list --search 'erdos-1153 in:title' --state closed --limit 10`
  → 5 historical PRs, most recent `#18850` (mechanic-only, 2026-05-13,
  index.ts annotation wiring) — 4 days ago.

No same-iteration race. Safe to proceed.

## §2. Audit — drift surfaces

### §2.1 Research-local stubs (3 files)

```
research/problems/erdos-1153/
├── state.md      — Phase: NEW, Iteration: 1
├── problem.md    — "Problem statement not found"
└── knowledge.md  — "Problem statement not found"
```

These three files are the 2026-01-15 auto-stub from `erdosproblems.com`
scraping where the scraped HTML didn't yield a parseable statement. They
were never edited.

### §2.2 Registry vs research-local

```json
// research/registry.json (problems[slug=erdos-1153])
{
  "slug": "erdos-1153",
  "phase": "COMPLETED",
  "path": "full",
  "started": "2026-01-15T16:46:42.683Z",
  "status": "graduated",
  "lastUpdate": "2026-03-26T23:43:21.713Z",
  "completed": "2026-03-26T23:43:21.712Z"
}
```

Registry has been `COMPLETED + graduated` for ~52 days, but
research-local state.md continues to assert NEW phase, iteration 1.

### §2.3 Pool vs registry

```json
// .lean/state/candidate-pool.json (candidates[id=erdos-1153])
{
  "id": "erdos-1153",
  "name": "Erdős #1153",
  "tier": "A",
  "significance": 7,
  "tractability": 6,
  "status": "in-progress",
  "notes": "IN-PROGRESS: Problem statement not found | Focus: Initial exploration of the problem. | Stats: 8 items built",
  "tags": ["erdos"]
}
```

Pool says `in-progress` and the notes prose echoes the stale stub state.md.
This is why `claim-random` even selected this slug (otherwise it would be
excluded from the eligible pool).

This will be flipped post-merge via
`scripts/research/claim-problem.sh update completed` — that's the only
write path that recomputes the notes consistently.

### §2.4 Lean file ↔ meta.json structure (already aligned)

```
$ wc -l proofs/Proofs/Erdos1153Problem.lean
    169
$ grep -c "^axiom " proofs/Proofs/Erdos1153Problem.lean
    1
$ grep -cE "^(theorem|lemma) " proofs/Proofs/Erdos1153Problem.lean
    6
$ grep -cE "^(def|noncomputable def) " proofs/Proofs/Erdos1153Problem.lean
    4
$ grep -c '\bsorry\b' proofs/Proofs/Erdos1153Problem.lean
    0
```

meta.json structured fields match:

- `meta.lineCount: 169` ✓
- `meta.axiomCount: 1` ✓
- `meta.theoremCount: 6` ✓
- `meta.definitionCount: 4` ✓
- `meta.sorries: 0` ✓
- `leanFile.{lineCount, axiomCount, theoremCount, definitionCount,
  sorries}: matching` ✓
- `meta.assumptions: "1 axiom: erdos_1153 ..."` ✓

So structured numerics are clean. Drift is only in prose / contribution
lists / section boundaries.

### §2.5 Lean file ↔ meta.json prose (drifted)

| Field | Stated | Actual |
|-------|--------|--------|
| `conclusion.summary` line count | 160 | 169 |
| `conclusion.summary` axiom count | 2 | 1 |
| `conclusion.summary` "Chebyshev tightness are axiomatized" | yes | no — only inline comment |
| `overview.proofStrategy` "matching upper bound axiom" | yes | no — only inline comment |
| `meta.originalContributions[11]` | `chebyshev_lebesgue_upper` | not a declaration in the file |
| `sections[0]` (header-imports) endLine | 41 | 46 (set_options at 41-42, namespace at 44, open Finset at 46) |
| `sections[1]` (definitions) startLine | 42 | 48 (`## Definitions` header) |
| `sections[1]` (definitions) endLine | 68 | 70 (DistinctNodes body ends at 70) |
| `sections[2]` (lagrange-properties) startLine | 69 | 72 (Section 1 header) |
| `sections[2]` (lagrange-properties) endLine | 93 | 96 (lagrangeBasis_self body ends at 96) |
| `sections[3]` (lebesgue-properties) startLine | 94 | 98 (Section 2 header) |
| `sections[3]` (lebesgue-properties) endLine | 126 | 133 (lebesgueFunction_at_node_eq body ends at 133) |
| `sections[4]` (main-result) startLine | 127 | 135 (Section 3 header) |
| `sections[4]` (main-result) endLine | 160 | 169 (end Erdos1153 at 169) |
| `sections[4]` summary "Chebyshev upper bound as axioms" | yes | no |
| `sections[4]` mathContext "Matching upper bound: ... (axiom)" | yes | no |

### §2.6 Boundary line samples (cross-validation)

```
  41: set_option linter.unusedVariables false
  42: set_option linter.unusedTactic false
  44: namespace Erdos1153
  46: open Finset
  48: /-
  49: ## Definitions
  50: -/
  68: -- Nodes are distinct (required for well-defined interpolation)
  69: def DistinctNodes (n : ℕ) (nodes : Fin n → ℝ) : Prop :=
  70:   Function.Injective nodes
  72: /-
  73: ## Section 1: Properties of Lagrange Basis Polynomials
  ...
  96:   exact div_self (sub_ne_zero.mpr hne)
  98: /-
  99: ## Section 2: Properties of the Lebesgue Function
  100: -/
  ...
  133:   simp
  135: /-
  136: ## Section 3: The Main Result and Tightness
  ...
  167: -- The n-th Chebyshev polynomial roots give Lebesgue constant ≤ (2/π + ε) log n
  168:
  169: end Erdos1153
```

## §3. Decision matrix — doc-only STATE-SYNC chosen

| Option | Cost | Risk | Outcome |
|--------|------|------|---------|
| A. Doc-only S2 STATE-SYNC (chosen) | ~30 min | trivial | 3 research-local files + 1 meta.json drift catchup + pool flip + sessions memo |
| B. Lean ACT — try to prove `erdos_1153` axiom directly | unknown weeks/months | very high; classical Bernstein/Erdős proof requires complex-analysis machinery beyond current Mathlib | — |
| C. Lean ACT — add `chebyshev_lebesgue_upper` as a stated (but axiomatized) upper bound | ~1-2 hours + Docker build under 3-RED INFRA (see §4) | medium; would expand axiom count from 1 to 2, weakening the meta.json claim | — |
| D. Release without PR | 0 | low | leaves all 7 drift surfaces unaddressed; pool stays `in-progress` |

Option A is the right call: the drift inventory is concrete and reachable
without touching Lean, and pre-claim recency probes show no collision
with other agents.

Option C was rejected because **adding an axiom for an already-noted-as-
comment statement is a regression in formalization status**. The comment
at line 167 is the right form — anything beyond it should be either a
proper formalization (option B-adjacent) or remain a comment.

## §4. INFRA snapshot

(From parallel session-end memos of other researchers, this session
window ~05:00–06:00Z 2026-05-17 — not re-measured here because doc-only
PRs are insensitive to host INFRA state.)

Carry-forward from sibling sessions:

- **G7 (host disk)**: RED — multiple researchers report 2–4 GiB available
  on the system disk in the last 24h, below the 5 GiB soft-floor; the
  `mosertardos`, `dissection-of-cubes-oq-05`, `ballot-problem-oq-03`,
  `minkowski-theorem-oq-04`, `four-square-distribution-oq-01`, and
  `schauder-fixed-point-oq-03-oq-01-incomplete-01` sessions today all
  flagged this.
- **G8 (Docker)**: RED — `docker info` reports the Docker server has been
  hung for ≥20h+ across multiple sessions. Doc-only PRs do not require
  `proofs/scripts/docker-build.sh`, so this does not gate the present
  work.
- **G9 (.lake symlink)**: RED — `proofs/.lake` is a self-cycle symlink
  per multiple recent reports. Again, not relevant to doc-only catchup.

This PR is **doc-only and INFRA-insensitive**. It would be appropriate
to ship under any INFRA state.

## §5. Files changed

```
research/problems/erdos-1153/state.md                                  (rewrite)
research/problems/erdos-1153/problem.md                                (rewrite)
research/problems/erdos-1153/knowledge.md                              (rewrite)
research/problems/erdos-1153/sessions/session-2-statesync-completed-
  drift-catchup.md                                                     (NEW, this file)
src/data/proofs/erdos-1153/meta.json                                   (surgical)
```

`meta.json` edits — five surgical changes:

1. `meta.originalContributions`: drop `"chebyshev_lebesgue_upper"`
   (11 entries, was 12).
2. `overview.proofStrategy`: drop "Tightness via Chebyshev nodes is
   stated as a matching upper bound axiom"; add the corrected description
   (instantiation derivation of `erdos_1153_full_interval` from
   `erdos_1153`; Chebyshev tightness is comment-only).
3. `sections[0..4]` startLine/endLine: bring to actual file boundaries.
4. `sections[4]` summary + mathContext: drop the "matching upper bound
   axiom" claim; describe as inline comment only.
5. `conclusion.summary`: 160→169 lines, 2→1 axioms, and revise the
   Chebyshev tightness claim from "axiomatized" to "comment-only".

## §6. Post-merge cleanup

After merge, run from any researcher worktree (or main):

```bash
cd /Users/rwalters/GitHub/lean-genius
/Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh \
  update erdos-1153 completed
```

This will rewrite the `.lean/state/candidate-pool.json` entry from
`in-progress` to `completed` and refresh the notes prose so it stops
echoing the stale stub state.md.

The `research/claims/erdos-1153.json` claim (TTL 90 min, expires
2026-05-17T07:14:01Z) will be released as the final step of this PR
cycle via `claim-problem.sh release erdos-1153`.

## §7. Memory writeback

This session matches the pattern saved as
`_first_claim_lands_on_long_completed_slug_with_T_18d_lean_pr_predecessor_split_with_audit_but_not_research_json_registry_drift_catchup`
— but with these distinguishing details:

- No "T-18d Lean PR predecessor split" here; instead the gallery Lean
  file was authored ≥ 2026-03-27 (~51 days ago) via PR #7112 which only
  touched line-count drift, not a substantive Lean ACT.
- No "non-researcher Lean PR" predecessor with audit; just three legacy
  enrichment PRs (#7112, #9750, #18850) plus the original NEW-stub from
  2026-01-15.
- No "drift below threshold = release" applies: there are 7 distinct
  drift surfaces (3 research-local rewrites + 4 meta.json corrections +
  pool flip) — well above any release threshold.

The conclusion.summary `160 lines / 2 axioms` drift is the type of stale
prose-vs-structure drift that survives mechanic batch passes (mechanic
fixes the structured numeric fields but does not touch
`conclusion.summary` prose). Future researchers claiming long-completed
slugs should grep prose fields for round-number line counts that don't
match `meta.lineCount` as a quick-tell.

## §8. Sign-off

PR: `research(erdos-1153): S2 STATE-SYNC — long-completed slug + research-
JSON / state.md / pool drift catchup + meta.json prose-vs-structure fix
(doc-only)`

5 files changed: 4 rewritten + 1 NEW + 1 surgical meta.json. No Lean
file changes. No new axioms. No new theorems. Mathlib pin unchanged.
Build-pending status: N/A (doc-only). Auditor-friendly: every claim in
this memo is grounded in a specific file/line citation above.

Iteration 1 → 2. Attempt counts unchanged (1).
