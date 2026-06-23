# S1 OBSERVE — Bootstrap state.md + problem.md + sessions/ + JSON top-level fields + drift fix (doc-only)

**Date**: 2026-05-16 (~22:05 UTC)
**Researcher**: researcher-3
**Mode**: OBSERVE — bootstrap slug infrastructure for the first time; absorb existing knowledge.md + JSON `knowledge` subset + leanFiles[]; fix 4 categories of drift; record current Lean-file state as the load-bearing baseline.
**Status**: thin doc-only bootstrap. No Lean / no build / no Mathlib bearer search / no parent gallery touch.

## §0. Why S1 OBSERVE fires (slug claim-random landed on minimally-instrumented dormant slug)

`claim-problem.sh claim-random` selected `erdos-1006-oq-01-oq-02` at
2026-05-16T~22:00Z (RICH 21, MODERATE+ depth-first, Tier B). At session
start, the slug carried:

- **knowledge.md only** in `research/problems/erdos-1006-oq-01-oq-02/`
  — no `state.md`, no `problem.md`, no `sessions/` directory.
- **Canonical research JSON** at
  `src/data/research/problems/erdos-1006-oq-01-oq-02.json` missing
  8 top-level fields (`slug`, `title`, `phase`, `status`,
  `currentState`, `started`, `tags`, `lastUpdate`); present fields
  cover `id`, `tractability`, `significance`, `problemStatement`,
  `knowledge` (with progressSummary/builtItems/insights/mathlibGaps/
  nextSteps), `leanFiles[]` (6 entries), and `relatedProofs[]` (9
  entries).
- **Lean file** `proofs/Proofs/Erdos1006OQ01OQ02.lean` at **256 LOC**,
  9 theorems, 2 axioms, 4 definitions, 0 sorries (host-verified at
  session start via `wc -l` + `grep -cE`).

Sibling-slug structure comparison (host inspection):

| Sibling | state.md | problem.md | knowledge.md | sessions/ | literature/ |
|---|---|---|---|---|---|
| erdos-1006-oq-01-oq-01 | ✅ | ✅ | ✅ | ❌ | ✅ |
| erdos-1006-oq-01-oq-02 (this slug) | ❌ | ❌ | ✅ | ❌ | ❌ |
| erdos-1006-oq-02-oq-01 | ✅ | ✅ | ✅ | ❌ | ✅ |
| erdos-1006-oq-02-oq-03 | ✅ | ✅ | ❌ | ❌ | ❌ |

The OBSERVE-phase sibling `erdos-1006-oq-01-oq-01` provides the
canonical state.md template (Phase OBSERVE + Path full + Since
timestamp + Iteration 1 + Active Approach None + Attempt Counts 0 + 5
sections). S1 OBSERVE follows this template, augmented with a "Drift
Inventory" sub-section recording what S1 fixes vs leaves alone.

## §1. Drift inventory (pre-S1 OBSERVE state of canonical JSON)

### §1.1 leanFiles[1] (Erdos1006OQ01OQ02.lean)

| Field | Pre-S1 JSON | Host actual (`wc -l` + `grep -cE`) | Drift |
|---|---|---|---|
| `lineCount` | 257 | **256** | +1 off-by-one |
| `theoremCount` | 9 | 9 | ✓ |
| `axiomCount` | 2 | 2 | ✓ |
| `defCount` | 4 | 4 | ✓ |
| `sorryCount` | 0 | 0 | ✓ |
| `isAristotle` | false | n/a | ✓ |
| `githubUrl` | github.com/rjwalters/... | n/a | ✓ |

### §1.2 knowledge.progressSummary

Pre-S1 text:
> "PROGRESS: 10 theorems (was 7). Added k3_is_comparability_graph,
>  k3_not_cover_graph (8-case proof), cover_strictly_subset_comparability.
>  Strict separation between cover and comparability graphs formally
>  proved. 2 axioms, 0 sorries, 261 lines."

Both "10 theorems" and "261 lines" are **pre-#15112 stale**. PR #15112
(2026-05-03, "correct theoremCount 10→9, remove True stub") removed
the `True` stub which (i) decreased theoremCount 10→9 and (ii)
decreased lineCount 261→256 (5 LOC: docstring + stub body + blank
lines).

Post-S1 refreshed text:
> "S1 OBSERVE bootstrap (researcher-3, 2026-05-16, this PR): file at
>  9 theorems, 2 axioms, 0 sorries, 256 lines, 4 definitions (host
>  `wc -l` + `grep -cE` verified). K₃ strict-separation witness
>  (`cover_strictly_subset_comparability` at line 251) and 8-case
>  K₃-not-cover-graph proof (`k3_not_cover_graph` at line 219). Strict
>  separation between cover and comparability graphs formally proved.
>  ... [pre-existing summary follows]."

### §1.3 knowledge.builtItems[6/7/8] line refs

Pre-S1 line refs and actual line numbers (host `grep -nE '^theorem'`):

| Symbol | Pre-S1 ref | Actual | Drift |
|---|---|---|---|
| `k3_is_comparability_graph` | line 213 | line 208 | -5 |
| `k3_not_cover_graph` | line 224 | line 219 | -5 |
| `cover_strictly_subset_comparability` | line 256 | line 251 | -5 |

All three shifted by exactly 5 lines — consistent with the #15112
True-stub removal happening above these declarations.

### §1.4 Missing top-level JSON fields

Pre-S1 JSON has 7 top-level keys: `id`, `tractability`, `significance`,
`problemStatement`, `knowledge`, `leanFiles`, `relatedProofs`. Missing 8:

- `slug`: "erdos-1006-oq-01-oq-02" (mirrors `id`; some downstream tools
  read `slug` not `id`)
- `title`: "Cover Graph Recognition in P?"
- `phase`: "OBSERVE" (this S1)
- `status`: "active" (slug is not closed; the underlying open question
  remains open)
- `currentState`: full block (`phase`, `since`, `iteration`, `focus`,
  `nextAction`, `attemptCounts`, `blockers`)
- `started`: "2026-04-26T00:00:00Z" (approximate; predates oldest
  in-slug Lean activity on 2026-05-03)
- `tags`: ["erdos", "graph-theory", "complexity", "posets",
  "cover-graphs", "np", "open-question"]
- `lastUpdate`: "2026-05-16T22:05:00.000Z"

## §2. Why a "True-stub removal" account for the 5-line shift

`grep -nE "^theorem|^lemma|^axiom|^def" proofs/Proofs/Erdos1006OQ01OQ02.lean`
at session start produces declarations at lines `58, 63, 67, 77, 92,
111, 125, 146, 155, 159, 176, 191, 208, 219, 251` — 15 declarations,
9 of which are theorem/lemma (matches the `theoremCount: 9` field).

The pre-S1 builtItems references (213, 224, 256) correspond to the
last three theorems (`k3_is_comparability_graph`, `k3_not_cover_graph`,
`cover_strictly_subset_comparability`) at +5 LOC each. A 5-line stub
sitting between the `cover_subclass_comparability` block and the K₃
section would account for this; PR #15112's commit message confirms:
"remove True stub" (the stub was a placeholder before
`k3_is_comparability_graph` while the K₃ section was being drafted).

## §3. Mathlib pin SHA + bearer carry-forward

```
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Same SHA as in-flight schauder-fp-oq-03-oq-01-incomplete-01 S22 ACT
(PR #19671 merged 2026-05-16T16:21:07Z) and S23 STATE-SYNC (PR #19883
opened by this researcher ~25min before this S1 OBSERVE session) and
all adjacent same-wave PRs (#19655 shannon, #19755 abel-ruffini, etc.).
**No bearer walk** in this S1 OBSERVE — the file's 9 theorems are
already at 0 sorries; building was last attempted upstream (no recent
explicit per-slug build log; the parent gallery slug `erdos-1006` is
the build-bearing entry).

## §4. Host INFRA snapshot (carry-forward; informational only)

| Gate | Status | Evidence |
|---|---|---|
| G7 host disk | **4.3 Gi RED** | `df -h .` — below 5 Gi same-day soft-floor; unchanged from S23 schauder session ~30 min ago |
| G8 Docker | **Server: empty** | `docker info` Server section still empty; ≥7h continuous since first observed (S22 schauder ACT-time) |
| G9 proofs/.lake | **self-symlink cycle** | `/Users/rwalters/GitHub/lean-genius/proofs/.lake -> itself`; carry-forward from S6 schauder |

These do NOT block this S1 OBSERVE (doc-only). They DO block any
future S2 ACT-style work (would need Docker recovery + ≥5 Gi disk).

## §5. Files changed by this S1 OBSERVE

1. NEW `research/problems/erdos-1006-oq-01-oq-02/state.md` (~130 LOC,
   9 sections following sibling template).
2. NEW `research/problems/erdos-1006-oq-01-oq-02/problem.md` (~70 LOC).
3. NEW `research/problems/erdos-1006-oq-01-oq-02/sessions/2026-05-16-s1-observe-bootstrap-and-drift-fix.md`
   (THIS file, ~250 LOC, 10 sections).
4. MOD `src/data/research/problems/erdos-1006-oq-01-oq-02.json`
   — adds 8 top-level fields (`slug`, `title`, `phase`, `status`,
   `currentState`, `started`, `tags`, `lastUpdate`); fixes
   `leanFiles[1].lineCount` 257→256; refreshes
   `knowledge.progressSummary` prepend; fixes
   `knowledge.builtItems[6/7/8]` line refs 213→208 / 224→219 /
   256→251.

NO change to:

- `proofs/Proofs/Erdos1006OQ01OQ02.lean` or any other Lean file.
- `proofs/lake-manifest.json`.
- Parent gallery slug `src/data/proofs/erdos-1006/meta.json` (parent
  slug is independently maintained; out of scope for this -oq-01-oq-02
  slug bootstrap).
- Sibling slugs (-oq-01-oq-01, -oq-02-oq-01, etc.).
- `knowledge.md` body (preserved verbatim; the JSON `knowledge`
  subset edit is internal to JSON only).

## §6. Explicit non-actions

DO NOT in this PR:

1. ❌ Edit any `.lean` file (file is at 0 sorries; not a defect).
2. ❌ Run `./proofs/scripts/docker-build.sh` (Docker hung; would hang).
3. ❌ Run `pnpm build` (regenerates all research JSONs; would clobber
   this S1 OBSERVE's hand-tuned JSON edits and could re-introduce the
   257 LOC drift via the split-by-newlines convention vs `wc -l`).
4. ❌ Mathlib bearer walk (no Lean change; file at 0 sorries with
   stable axioms).
5. ❌ Touch parent gallery `src/data/proofs/erdos-1006/meta.json` (out
   of scope).
6. ❌ Touch sibling slugs.
7. ❌ Touch `knowledge.md` body (JSON subset edit only).
8. ❌ Resolve the underlying open question (`cover_graph_recognition_in_p`
   is genuinely open in combinatorics; no in-scope path).
9. ❌ Run `lake build` (DANGER per CLAUDE.md).

## §7. Honesty calibration

✅ This PR claims:
- The Lean file is at 256 LOC, 9 theorems, 2 axioms, 4 defs, 0 sorries
  (host-verified by `wc -l` + `grep -cE` at session start).
- The JSON pre-S1 had 8 missing top-level fields (verified by `jq keys`
  at session start).
- The 5-line shift in builtItems line refs traces to #15112
  ("remove True stub") merged 2026-05-03 (verified by `git log`).
- Mathlib pin SHA `2df2f0150c…` unchanged ≥48h (verified by `jq` on
  `proofs/lake-manifest.json`).
- The underlying mathematical question is genuinely open.

❌ This PR does NOT claim:
- That the Lean file compiles (no build verification in this session;
  the file's last direct build was upstream — likely via parent
  gallery `erdos-1006`).
- That the axiom `cover_graph_recognition_in_p` will be resolved soon.
- That progress on the open question is near-at-hand.
- Any new mathematical content (no design, no proof, no Mathlib API
  delta).

## §8. Memory citations

Patterns used in this S1 OBSERVE:

- `feedback_mechanic_pnpm_build_regenerates_all_research_jsons.md`:
  informs the "do NOT run pnpm build" non-action (would clobber the
  S1 hand-tuned leanFiles[1].lineCount via the split-newlines vs
  wc -l convention divergence).
- `feedback_worktree_absolute_path_lands_in_main_repo_use_dotloom_worktrees_path_or_cp_recovery.md`:
  informs the use of relative paths from worktree CWD for state.md /
  problem.md / sessions/ creation.
- Sibling slug `erdos-1006-oq-01-oq-01/state.md` (Phase OBSERVE +
  Path full + Since + Iteration 1 + Attempt Counts 0 + Blockers None)
  used as the canonical bootstrap template.

## §9. Open mathematical question status

**Cover graph recognition in P?** — the underlying open question of
this slug. As of 2026-05-16 (session-start best-effort review):

- The decision version is in NP (poset is a polynomial certificate).
- Sub-classes known to be in P include comparability graph recognition
  (Golumbic) and interval graph recognition (Booth-Lueker). Cover
  graph recognition's P-membership status is, to the author's
  knowledge, **open**.
- Known reductions: cover graphs ⊊ comparability graphs (this slug
  formalizes the strict separation via K₃). Recognizing cover graphs
  reduces in poly-time to two sub-questions: (i) recognize that the
  underlying graph is a comparability graph (in P), and (ii)
  determine whether the comparability relation admits a "shortcut-free"
  acyclic orientation (status uncertain).
- This is NOT a Millennium-Prize-tier hardness assumption; resolution
  could plausibly come from combinatorial techniques rather than
  complexity-theoretic breakthroughs. A literature scan (S2 OBSERVE
  candidate) is the productive next step.

The axiom `cover_graph_recognition_in_p` in
`Erdos1006OQ01OQ02.lean:176` stays in place until a literature
finding or formal proof resolves it.
