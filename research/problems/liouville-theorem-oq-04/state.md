# Research State: liouville-theorem-oq-04

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-05-16T21:38:00+00:00 (S17 STATE-SYNC)
**Iteration**: 17
**Last Updated**: 2026-05-16 (researcher-3)

## Session 17 (researcher-3, 2026-05-16, doc-only STATE-SYNC) — leanFiles[0] off-by-one fix + sessions/ bootstrap

`claim-random` landed on this long-COMPLETED (T-8d since S16 PR #17076, the
gallery-metadata-promotion-to-verified PR) slug. Audit found:

| Field | Asserts | Reality | Status |
|---|---|---|---|
| top-level `phase` / `status` | COMPLETE / completed | (no change) | ✅ |
| `currentState.phase` | COMPLETE | (no change) | ✅ |
| `currentState.iteration` | 16 | bumped to 17 | this PR |
| `currentState.since` / top `lastUpdate` | 2026-05-08T12:00Z | refreshed to 2026-05-16T21:38Z | this PR |
| `leanFiles[0].lineCount` (LiouvilleTheorem.lean) | 529 | `wc -l` = 528 | **fixed → 528** |
| `leanFiles[0].theoremCount` (parent) | 17 | 17 ✓ | unchanged |
| `leanFiles[0].axiomCount` (parent) | 1 | 1 ✓ | unchanged |
| `leanFiles[0].sorryCount` (parent) | 0 | 0 ✓ | unchanged |
| `leanFiles[1].lineCount` (OQ04) | 1344 | 1344 ✓ | unchanged |
| `leanFiles[1].theoremCount` (OQ04, includes 2 private) | 35 | 35 ✓ | unchanged |
| `leanFiles[1].axiomCount` (OQ04) | 0 | 0 ✓ | unchanged |
| `leanFiles[1].defCount` (OQ04) | 6 | 6 ✓ | unchanged |
| `leanFiles[1].sorryCount` (OQ04) | 0 | 0 ✓ (all 4 `sorry` matches are in comments, not `by sorry`) | unchanged |
| sessions/ dir | (does not exist) | flat session-N-…md files exist for S15/16 era | **bootstrap with S17 note** |
| gallery `liouville-theorem-oq-04/meta.json` | status verified, axiomCount 0, sorries 0 | matches | unchanged (out of scope) |
| gallery `liouville-theorem/meta.json` | lineCount 528 | matches | unchanged |
| sibling JSONs `oq-01/02/03` `leanFiles[*].LiouvilleTheorem.lean.lineCount` | 528 | matches | (oq-04 was the lone outlier — single-slug fix, NOT a mechanic batch candidate) |

**Root cause of the off-by-one.** The `liouville-theorem-oq-04.json` file was
(re)introduced in the same large research-JSON bootstrap commit `ecb47b3` on
2026-05-15, with `leanFiles[0].lineCount: 529` for `LiouvilleTheorem.lean`.
Three sibling JSONs (`oq-01/02/03`) and the gallery `liouville-theorem`
meta.json all use `wc -l` = 528; the OQ-04 entry alone carries the inflated
value, which is consistent with the `split('\n').length` convention
(= `wc -l + 1` for files ending in `\n`). Per project convention (memory:
"Mechanic — `pnpm build` regenerates ALL research JSONs ... uses
split('\n').length convention (= wc -l + 1) not raw wc -l ..."; recent
mechanic batches favor `wc -l`), the correct value is 528. No drift in any
other field, no drift in `LiouvilleTheoremOQ04.lean` (the slug-specific
file), no `sorry` regression, no axiom regression.

**Bearer stability.** Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0) unchanged since the S15 era. The OQ-04 file at 1344 LOC / 35 thm /
0 axiom / 6 def / 0 sorry is byte-stable since the S16 promotion PR
#17076 merged on 2026-05-08. No bearer recheck performed in this S17 cycle
(SHA-stable busywork per memory).

**Files this S17 doc-only PR (3):**
1. EDIT `src/data/research/problems/liouville-theorem-oq-04.json` — 6 fields:
   `currentState.{since, iteration, focus, nextAction, attemptCounts.total}`,
   `knowledge.progressSummary` prepend, `knowledge.nextSteps[0]` prepend a
   "DONE (S17)" entry, `leanFiles[0].lineCount: 529 → 528`, top-level
   `lastUpdate` refresh.
2. EDIT this state.md — Session 17 entry; preserve S16 → S1 content verbatim
   below.
3. NEW `sessions/2026-05-16-s17-statesync-leanfiles-off-by-one.md` (~180 LOC)
   — bootstraps the `sessions/` directory; details audit findings + non-
   actions + 24h-future-researcher rationale + bearer-stability declaration.

**Explicit non-actions in this S17 STATE-SYNC:**
- No `.lean` file touch.
- No `proofs/Proofs/Erdos1151Problem.lean`-style cross-slug parent edit (the
  parent here is `LiouvilleTheorem.lean` — out of scope; siblings already at
  528).
- No gallery `meta.json` edit (both `liouville-theorem` and
  `liouville-theorem-oq-04` are accurate).
- No `lake-manifest.json` touch.
- No `problem.md`, `knowledge.md`, `literature/` touch.
- No re-spot-check of bearers (SHA byte-stable since S15; busywork).
- No Docker build attempt (host disk pressure observed at ~4.5 Gi avail at
  claim time; out of scope for this slug).

## Current Focus (historical, S16, preserved verbatim)

Session 16 — promote gallery metadata to `verified` / `original` after
the Session 15 bridge discharge (PR #17053, merged 2026-05-08T11:27:03Z).

PR #17053 rewrote `padic_liouville_norm_bridge` from `axiom` to fully-proved
`theorem` and resolved three pre-existing build errors discovered during the
post-merge build retry (`intPolyL1_pos` Finset summand inference, the
`Int.algebraMap_eq_intCast → eq_intCast` 4.26 rename, and the
`field_simp; ring` → `field_simp <;> ring` "No goals" fix). After those fixes,
the file is **0 axioms, 0 sorries, 1344 lines, 35 theorems, 6 defs**.

This session: meta.json status `axiomatized → verified`, badge
`axiom → original`, axiomCount `1 → 0`, lineCount `1216 → 1344`,
theoremCount `34 → 35`. Narratives in `description`, `assumptions`,
`originalContributions`, `proofStrategy`, `keyInsights`, `conclusion.summary`,
`conclusion.implications`, `conclusion.openQuestions`, the `main-theorem`
section, and `mainTheorems` are refreshed to drop bridge-axiom language and
reflect the now-fully-proved state.

## Active Approach
N/A — work is COMPLETE pending build verification. Path forward is operational:
flip the gallery flags, push the metadata PR, mark candidate-pool entry
`completed`, release the claim.

## Attempt Count
- Total attempts: 15
- Current approach attempts: 1 (metadata sync)
- Approaches tried: 3

## Blockers
- None. All Lean ingredients land on `origin/main` as of PR #17053
  (commit 0175c59d).

## Next Action
**Session 17 (optional / future work)**: pursue follow-up open questions:
1. Sharpen $\mu_p \leq 2d$ to $\mu_p \leq 2$ via Roth-style auxiliary
   polynomials (much harder; would parallel a Lean formalization of Roth's
   1955 theorem).
2. Function-field analog over $\mathbb{F}_q(t)$ with $t$-adic norm —
   would need a Mathlib `LaurentSeries` p-adic infrastructure or analogous
   `RatFunc` machinery.
3. Multi-place uniform statement: $\forall p, \mu_p(\alpha) \leq 2d$ for the
   same $\alpha$ — touches the adelic product formula.

## Session 15 deltas (PR #17053, merged 2026-05-08T11:27:03Z)
- File: 1216 → 1344 lines (+128), 34 → 35 theorems (+1), defs unchanged.
- Theorem added: `padic_liouville_norm_bridge` (rewritten from `axiom`).
- Axioms: 1 → 0.
- Sorries unchanged (0).
- Build: PR triggered three sequential commits to fix pre-existing 4.26
  drift errors before the build went green; final build state on the merged
  commit is reported as resolved by the PR description.

## Session 16 deltas (this session)
- meta.json status / badge / axiomCount / counts / narratives.
- src/data/research/problems/liouville-theorem-oq-04.json:
  phase NEW → COMPLETE, currentState.iteration 15 → 16, focus updated.
- candidate-pool.json: `in-progress` → `completed`.
- No Lean changes.

## References
- Parent file: `proofs/Proofs/LiouvilleTheoremOQ04.lean` (1344 lines, 0 axioms,
  0 sorries, 35 theorems, 6 defs).
- Algebraic case: Part IV.10, `padic_liouville_bridge_algebraic_case`
  (Session 13, line ~679).
- Rational-roots case: Part IV.11,
  `padic_liouville_bridge_rational_roots_case` (Session 14, line ~846).
- Bridge theorem (formerly axiom): `padic_liouville_norm_bridge`
  (Session 15, line ~935).
- Final main theorems: `padic_liouville_estimate` (line ~1066) and
  `padic_algebraic_not_liouville` (line ~1089).
