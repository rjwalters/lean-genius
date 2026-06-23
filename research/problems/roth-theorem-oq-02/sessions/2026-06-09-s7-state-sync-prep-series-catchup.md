# 2026-06-09 — S7 STATE-SYNC (researcher-6)

**Claim:** `researcher-48585` (RICH, expires 2026-06-10T01:30:05Z).
**Worktree:** `.loom/worktrees/researcher-6` on a fresh
`research/roth-theorem-oq-02-cycle` branch off `origin/main`
(162265bae2cb).
**Mode:** STATE-SYNC — doc-only JSON + state.md catch-up after the
S5/S5b/S6/S6c PREP series anti-target-skipped the canonical state
surfaces for ~27 days.

## Why this session

Four doc-only PREP PRs merged on 2026-05-13 in the canonical path
`research/problems/roth-theorem-oq-02/sessions/`, each by explicit
anti-target rule **never** modified state.md, the gallery JSON
`src/data/research/problems/roth-theorem-oq-02.json`, or knowledge.md:

| PR | Phase | Merged (UTC) | Author |
|----|-------|--------------|--------|
| #18509 | S5 PREP | 2026-05-13T04:10:19Z | researcher-5 |
| #18605 | S5b PREP | 2026-05-13T06:01:48Z | researcher-6 (this researcher's prior cycle) |
| #18685 | S6 PREP | 2026-05-13T09:24:01Z | researcher-11 |
| #18709 | S6c PREP | 2026-05-13T09:22:34Z | researcher-12 |

As a result, the canonical state surfaces stalled at the S4-a ACT view
(iteration 4, "Current Focus: S4-a ACT", `phase: "ACT"`, focus text
ending at S4-a's transitivity theorems) for ~27 days even though four
substantive PREPs landed in the same canonical path.

This S7 STATE-SYNC closes that drift in the same shape as the sibling
sylow-theorems-oq-03 S8 STATE-SYNC (PR #22704, this session) and the
known [[shepherd-lifecycle]] STATE-SYNC convention.

## Race awareness

- `gh pr list --search "roth-theorem-oq-02 in:title" --state open` → 0 results.
- Active claims on `roth-theorem-oq-02`: only `researcher-48585` (this session).
- A sibling claim exists on `roth-theorem-k3-oq-01-incomplete-01`
  (`researcher-41180`); different problem, no overlap.
- Last canonical-path merge: #18443 (S4-a ACT, 2026-05-13). Last
  canonical-path PREP: #18685 (S6 PREP, 2026-05-13). No ACT or PREP
  merged since.

## On-disk verification (S7 start)

```bash
$ wc -l proofs/Proofs/RothTheoremOQ02.lean
     236 proofs/Proofs/RothTheoremOQ02.lean
$ grep -cE "^axiom " proofs/Proofs/RothTheoremOQ02.lean
2
$ grep -nE "^axiom " proofs/Proofs/RothTheoremOQ02.lean
79:axiom rothNumberNat_bloom_sisask :
175:axiom rothNumberNat_kelley_meka :
$ grep -nE "sorry" proofs/Proofs/RothTheoremOQ02.lean
40:already states a closely-related bound (`bloom_sisask_bound`) with `sorry`
```

The grep-1 sorry hit at L40 is the word "sorry" inside a docstring
referencing the parent gallery file `RothTheoremQuantitative.lean`'s
`bloom_sisask_bound`, **not** a Lean `sorry`. The file carries
**2 axioms + 0 sorries** at 236 LOC — exactly as S4-a ACT (PR #18443)
left it. No subsequent Lean edits.

## Drift table

| Surface | On-disk reality | Stale JSON | Action |
|---------|-----------------|------------|--------|
| top-level `phase` | "PREP" | `"ACT"` | bump |
| `currentState.phase` | "PREP" | `"ACT"` | bump |
| `currentState.iteration` | 9 | `4` | bump |
| `currentState.focus` | S7 narrative + PREP ledger | "S4-a ACT (...)" | rewrite |
| `currentState.nextAction` | S5-a/S6-a paste-ready, S6-d alt | "S5 candidates: BohrSet/IsLittleO/le_min" (pre-PREP-series) | rewrite |
| `currentState.attemptCounts.total` | 9 | `4` | bump |
| `currentState.attemptCounts.currentApproach` | 8 | `3` | bump |
| `currentState.lastUpdate` | 2026-06-09 | 2026-05-13 | refresh |
| `knowledge.progressSummary` | prepend S7 + PREPs | ends at S3-B | prepend |
| `knowledge.builtItems` | append S4-a + PREPs + S7 | ends at S3-B | append 6 entries |
| `knowledge.nextSteps` | S5-a/S6-a paste-ready; S6-d alt; S4-b scaffold; S4-a + PREPs completed | starts at S4-a (NEW TOP), pre-PREP-series | rewrite |
| top-level `lastUpdate` | 2026-06-09 | 2026-05-13 | refresh |

## Ship scope (3 files)

1. **`src/data/research/problems/roth-theorem-oq-02.json`** — `phase`
   (top-level "ACT" → "PREP"), `currentState` (phase, iteration 4→9,
   focus / nextAction rewrite, attemptCounts.{total 4→9,
   currentApproach 3→8}, lastUpdate refresh) +
   `knowledge.{progressSummary, builtItems, nextSteps}` rewrite +
   top-level `lastUpdate` refresh.
2. **`research/problems/roth-theorem-oq-02/state.md`** — new top
   header (Phase line + Iteration 9 + Mode S7 STATE-SYNC) + Current
   Focus (S7 STATE-SYNC 2026-06-09) section (84 LOC) covering the
   PREP series ledger, drift table, anti-targets, net axiom impact,
   Mathlib pin recheck, revised focus / next action. Prior S4-a /
   S3-B / S2 ACT-A / S1 OBSERVE sections renamed to "Prior Focus" and
   preserved verbatim below.
3. **`research/problems/roth-theorem-oq-02/sessions/2026-06-09-s7-state-sync-prep-series-catchup.md`** —
   this session log.

## Anti-targets (NO)

- **No Lean edits.** Per the S5/S5b/S6/S6c PREP anti-target rule, the
  canonical Lean stays at 2 axioms + 0 sorries until a future S5-a /
  S6-a / S6-d ACT runs Docker.
- **No `proofs/Proofs/RothTheoremOQ02.lean` touch.**
- **No `problem.md` / `knowledge.md` touch** (stable from S1 OBSERVE).
- **No legacy-path touch.** The parallel directory
  `research/roth-theorem-oq-02/` (no `problems/` segment) is out of
  scope; PR #22457 (2026-06-05, "S2 STATE-SYNC") was a STATE-SYNC
  there, against a different state.md. The two directories diverged
  long ago; reconciling them is curator/architect scope, not
  researcher.
- **No sibling-slug touch.** `roth-theorem-k3-oq-01-incomplete-01`
  has its own active claim at S7 start; this PR does not enter its
  scope.
- **No `loom:review-requested` label.** Math-PR project policy.
- **No new axioms or sorries.**

## Risk register

| # | Risk | Likelihood | Mitigation |
|---|------|-----------|-----------|
| 1 | Concurrent ACT on roth-theorem-oq-02 since 2026-05-13 | LOW | Race-check confirmed: 0 open PRs; only this claim active; last merge to state.md was the omnibus commit ecb47b35601 (not slug-specific); last slug-specific merge was S4-a ACT #18443 (2026-05-13). |
| 2 | JSON parse error after edit | LOW | Validated with `python3 -c "import json; json.load(...)"` after each edit. |
| 3 | iteration off-by-one (S5/S5b/S6/S6c counted as 4 or 2?) | LOW | Counting each as 1 iteration (per state.md attempt-count convention which is "phase-attempts not sub-letters"): S1, S2, S3-B, S4-a, S5, S5b, S6, S6c, S7 = 9. Alternative convention (S5b/S6c as sub-iterations of S5/S6) would give 7; chose 9 for full visibility. |
| 4 | Top-level `phase` bumped from "ACT" to "PREP" — gallery surface change | LOW | This matches the reality: the slug shipped its last ACT at S4-a and has been in PREP mode for the analytic envelope discharge series ever since. The "PREP" designation matches `currentState.phase` and the S5/S5b/S6/S6c PREP labels. |
| 5 | Sibling claim `researcher-41180` on roth-theorem-k3-oq-01-incomplete-01 races | NONE | Different slug; different gallery files; no shared Lean. |

## Mathlib pin recheck

Doc-only S7 — no build verification needed. The pin re-verification
baked into S5b PREP (PR #18605 §2) and S6 PREP (PR #18685 §2) both
pinned 12-lemma API tables at sha
`1c1dadbc28517bb148fc05b9abc8659ce110d217` (v4.26.0); no
`lake-manifest.json` changes touching the relevant Mathlib modules
since 2026-05-12 per `git log --oneline -- proofs/lake-manifest.json`
(cross-checked with the sylow-OQ-03 S5/S7a pin verifications in this
same session).

## Net axiom impact

- OQ-02 axiom count: **2 → 2 (unchanged)**.
- OQ-02 sorries: **0 → 0 (unchanged)**.
- Gallery JSON ↔ state.md ↔ on-disk Lean now mutually consistent.

## After this PR

- **§S5-a or §S6-a ACT (paste-ready)** — paste the verbatim K-M
  `analytic_envelope_conditional` Lean from S5b PREP §3 (PR #18605)
  and/or the parallel B-S version from S6 PREP §3 (PR #18685) into
  `RothTheoremOQ02.lean` as conditional theorems. Both PREPs produced
  complete sorry-free bodies at ~50-60 LOC each.
- **§S6-d ACT (alternative)** — ship the K-M vs B-S head-to-head
  asymptotic-dominance theorem per S6c PREP §4 (PR #18709), ~30-50 LOC.
- **§S4-b** — `BohrSet T ρ` scaffold (~200 LOC, multi-quarter starter).

Future STATE-SYNC ticks only if drift opens between on-disk lean
(adding/removing axioms via ACT) and this JSON (e.g., S5-a / S6-a ACT
landing would reset the canonical surfaces).

## Pattern notes (for memory)

This S7 STATE-SYNC and the sibling sylow-oq-03 S8 STATE-SYNC (this
session) both share the same shape: a doc-only catch-up PR repairing
the case where ACT or PREP work in the canonical path landed but the
canonical `state.md` + gallery JSON were never updated. The pattern
is becoming common enough that future researcher cycles encountering
"state.md says S4-a but session logs show S6c" should default to a
STATE-SYNC tick rather than attempting heavier work.
