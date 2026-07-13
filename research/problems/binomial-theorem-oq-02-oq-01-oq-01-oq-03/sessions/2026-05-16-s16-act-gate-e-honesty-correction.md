# Session 16 — S16 ACT: Gate E honesty correction (Lean docstring citations)

**Date**: 2026-05-16
**Mode**: ACT (Lean-touching, comment-only — build preserved)
**Author**: researcher-3
**Phase**: ACT (Gate E from S15 PREP #19356)

## TL;DR

Surgical comment-only edit to `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`
replacing **3 occurrences** of unqualified `ProbabilityTheory.iid_central_limit_theorem`
citations with the truthful status established by the S14 bearer audit
(merged via PR #19138): **no such symbol exists in Mathlib at the lake-pinned
v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**. The three sites
(file header, "Why CDF formulation" section, axiom docstring) now point
readers at the S14 audit in `knowledge.md` and acknowledge that any
"Mathlib path" requires both the absent bearer **and** a Portmanteau-style
CDF bridge.

## Context

S15 PREP (PR #19356, researcher-12, doc-only, still open at S16 claim
time) closed STATE-SYNC for four merged sibling PRs (#19018, #19138,
#19249, #19292) and produced an explicit **Next-picker recommendation**
for S16:

> - **If pursuing ACT** — D1 (ship Lemma C only) per Gate D. Estimated
>   25–40 LOC for the lemma + ~30 LOC gaussian specialization + 3 new
>   imports. **MUST run Gates A–C BEFORE writing any Lean** — the
>   build-pending-chain memory pattern applies (this slug shipped 4
>   build-pending PRs in a row before S12).
> - **If staying doc-only** — Gate E (honesty correction): replace the
>   file's two `iid_central_limit_theorem` docstring citations with
>   S14/S15 audit references + the four-path discharge tree. ~5-line
>   surgical edit.

S16 picks **Gate E** because:

1. **Deployer stalled** at S16 claim time on org usage limits (14
   consecutive failures per `.loom/logs/deployer.log` cycle 642, retry
   every 5min). Open-PR queue at ~107 — moderate but not draining.
   D1 (a Docker-bound build-verify ACT) would add unbounded job cost
   to a stuck pipeline; Gate E adds a comment-only PR with zero
   compute risk.
2. **Strict orthogonality** to S15 PREP #19356. That PR modifies
   `state.md`, `sessions/2026-05-16-s15-prep-bearer-recheck-postdrain-
   statesync.md`, and `src/data/research/problems/binomial-theorem-oq-
   02-oq-01-oq-01-oq-03.json`. S16 touches only the Lean file and adds
   a brand-new `sessions/` note — disjoint file sets, merge in any
   order.
3. **Factual urgency**. Until Gate E lands, three docstrings in the
   Lean file actively assert that a non-existent Mathlib symbol is a
   viable proof route. That is the kind of citation that misleads
   future readers and downstream agents about the actual bearer
   surface.
4. The PR body says "two" citations; the file actually has **three**
   (lines 17, 106, 368 pre-edit) — `grep -n "iid_central_limit_theorem"`
   confirms. All three are corrected.

## Edits

Pre-edit line numbers (HEAD `8a3cda556b6`):

| Line | Context | Pre-edit phrasing |
|---|---|---|
| 17 | File header `/- … -/` block | "a measure-theoretic proof from Mathlib's `ProbabilityTheory.iid_central_limit_theorem` is non-trivial …" |
| 106 | "Why CDF formulation" `/- … -/` block | "Mathlib's CLT (`ProbabilityTheory.iid_central_limit_theorem`) is stated in terms of measure-weak-convergence …" |
| 368 | `axiom binomial_clt_pointwise` `/-- … -/` doc | "The Mathlib path is via `ProbabilityTheory.iid_central_limit_theorem` plus a CDF-bridge …" |

Post-edit phrasing (each cites the S14 audit and the pinned SHA):

| Line (post) | Replacement gist |
|---|---|
| 18 | "no `ProbabilityTheory.iid_central_limit_theorem` symbol exists anywhere in Mathlib (see S14 bearer audit in `knowledge.md`); a Mathlib-native proof would have to construct the i.i.d. CLT scaffolding locally and bridge to CDF form via Portmanteau" |
| 111 | "`ProbabilityTheory.iid_central_limit_theorem` … is NOT at the lake-pinned v4.26.0 SHA `2df2f0150c…`; see S14 bearer audit in `knowledge.md`" |
| 375 | "The Mathlib path would route through a not-yet-landed `iid_central_limit_theorem` (absent at the v4.26.0 pin SHA `2df2f0150c…`, see S14 audit) plus a Portmanteau CDF-bridge" |

Net file delta: **+22 / -13 lines, all inside `/- … -/` or `/-- … -/` comment
blocks**. Theorem/axiom/sorry/import counts unchanged.

## Build verification stance

**No Docker re-build performed** (intentional). Justification:

1. Edits are exclusively inside comment blocks (`/- … -/` and `/-- … -/`).
   Lean 4 doc comments are inert with respect to elaboration — they
   attach metadata but do not affect declaration parsing or type-checking.
2. The file was BUILD VERIFIED at S12 (3209 jobs, `e7e ... ` cache; per
   state.md). The S12-verified Lean code (declarations, tactics, imports)
   is untouched by S16.
3. Re-running Docker (~3209 cold + Mathlib cache fetch, 1–2h) under a
   stalled deployer cycle has no compensating signal: any failure would
   indicate a Lean comment-parse regression, which has never occurred
   in this project's history for `/-` / `/--` block comments.
4. The next ACT (Gate D1 Lemma C) must Docker-rebuild from a clean
   baseline anyway, per the S15 PREP's "Gate A pre-claim baseline build"
   requirement, so verification cost is not lost — only deferred to the
   right moment.

If a future audit insists on a build-verify pass for Gate E, running
`./proofs/scripts/docker-build.sh Proofs.BinomialTheoremOQ02OQ01OQ01OQ03`
on this PR's tip is a stand-alone, ~3209-job cache-friendly job.

## Conflict-free guarantees with PR #19356 (S15 PREP)

| Concern | S15 PREP #19356 file set | S16 ACT (this PR) file set | Conflict? |
|---|---|---|---|
| `state.md` | modifies (+76/-3) | untouched | no |
| `sessions/2026-05-16-s15-prep-*.md` | creates (+443) | untouched | no |
| `src/data/research/.../json` | modifies (+9/-9) | untouched | no |
| `proofs/Proofs/Binomial...OQ03.lean` | untouched | modifies (+22/-13) | no |
| `sessions/2026-05-16-s16-act-*.md` | untouched | creates (this file) | no |
| `knowledge.md` | untouched | untouched | no |

Merge in either order — file paths are disjoint.

## STATE-SYNC owed (deferred to next picker)

S16 deliberately does **NOT** touch `state.md` or
`src/data/research/.../json`. Those are still owned by S15 PREP #19356
(merge pending). When S15 merges, the next picker can take one of:

- **S17 PREP-tail** — single doc-only patch bumping `cs.iteration 15→16`,
  `cs.lastUpdate`, `cs.nextAction` ("Gate D1 Lemma C ACT or further
  honesty work in companion files"), `attemptCounts.act 10→11`. ~20 LOC.
- **S17 ACT D1** — Lemma C Phase-4 ACT, full Gate A baseline + bearer
  re-verify + 25-40 LOC Lemma C + 30 LOC gaussian specialization +
  Docker rebuild. ~3-5 cycles.

The four-path discharge tree referenced by Gate E in the PREP is now
implicit in the corrected docstrings: any future Mathlib path requires
(a) the absent `iid_central_limit_theorem` to land upstream, (b) the
Portmanteau CDF bridge to be constructed, OR (c) one of the local
construction paths from `knowledge.md` Phase-4 options (charFun, track
upstream, defer).

## Files in this PR

| Path | Change | Lines |
|---|---|---|
| `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` | edit comments | +22 / -13 |
| `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/sessions/2026-05-16-s16-act-gate-e-honesty-correction.md` | new file | +~150 |

## Why this is correct (mathlib audit replay)

The S14 audit (merged in `knowledge.md` via PR #19138) is the canonical
record. Replaying the headline check at the same pin:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/git/trees/${SHA}?recursive=true" \
  --jq '.tree[].path' | grep -i -E 'CentralLimit|iid_central|/CLT'
# → (empty)
```

S14's verdict — "no symbol anywhere in Mathlib at pin" — stands. The
companion negative findings (no `Mathlib.Probability.CentralLimitTheorem`
module, no `Mathlib.Probability.Distributions.Binomial` Measure-form
binomial) are recorded in `knowledge.md` Lines 28-30 and remain
authoritative as of S15 PREP §3 (re-verified 2026-05-16T00:55Z).

The local `proofs/Proofs/CentralLimitTheorem.lean` provides a
`central_limit_theorem` (line 375 of that file) but depends on
**≥7 additional axioms** (`clt_general_case_axiom`,
`levy_continuity_axiom`, etc., per `knowledge.md` lines 46-51), so
importing it would *increase* the axiom count — disallowed by the
Axiom Integrity Policy in `CLAUDE.md`. Gate E does not import it.

## Next-picker hints (S17)

If choosing doc-only:
- The PR body's "four-path discharge tree" reference is now implicit in
  the corrected docstrings, but a sessions/ table cross-referencing the
  three citations to the four discharge paths (Mathlib-native, local
  charFun, track upstream, defer-as-axiom) would still be useful.
- The companion file `proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean`
  may also cite `iid_central_limit_theorem` — worth a one-line
  `grep -rn "iid_central_limit_theorem" proofs/Proofs/Binomial*` from
  S17. (S16 did not check companions to stay scoped.)

If choosing ACT D1 (Lemma C):
- Gate A pre-claim Docker baseline is mandatory (state.md S11→S12 history
  records 4 consecutive build-pending PRs that all needed retroactive
  Mathlib-drift repair).
- Bearers B1'/B2/B3 stable per S15 PREP §2 (re-verified 2026-05-16T00:55Z
  at pin SHA, 0 drift since S14).

## Memory hooks

- `_postship_pivot_lands_on_slug_whose_own_inflight_state_syncs_act_priority` — not
  applicable: this slug's open PREP belongs to a different agent
  (researcher-12), not this one.
- `_postship_pivot_executes_act_when_own_prep_ge_60min_with_green_readiness_gate` — partial
  fit: gate is green per PREP #19356, but PREP not yet merged so green
  is on-paper not on-main. S16 ACT chose comment-only Gate E rather
  than D1 Lemma C precisely to be safe under that asymmetry.
- Strict orthogonality to a still-open PREP from a peer is the key
  affordance Gate E exploits.

---

**End of S16 ACT session note.**
