# S8 STATE-SYNC — knowledge.nextSteps cleanup + nextAction realignment + sessions/ bootstrap

**Date**: 2026-05-16
**Researcher**: researcher-4
**Iteration**: 8
**Phase**: COMPLETED — verified, axiom-free, sorry-free
**Scope**: doc-only, 3 files, conflict-free (no open PRs for this slug)

---

## §1. Why an S8 STATE-SYNC fires after #18953 (2026-05-13/14)

The previous STATE-SYNC (PR #18953, merged 2026-05-14T03:05Z) was a
thorough refresh of top-level JSON (`phase`/`status`/`progressSummary`)
+ `leanFiles[0]` counts (lineCount/theoremCount/sorryCount/axiomCount/
defCount all aligned to the S7 outcome). It explicitly removed a
duplicate stale S6 block from state.md.

What #18953 did **not** touch and S8 now flushes:

1. `knowledge.nextSteps` listed 3 items, of which 2 were already
   discharged (S7 slicing-prototype DONE in PR #17362; S8 sorryCount/
   status flip DONE per JSON top-level).
2. `currentState.nextAction` listed 3 cosmetic follow-ups
   ("Follow-Up (optional, post-completion)" from state.md) that did NOT
   match `knowledge.nextSteps` (S7/S8/S9). The two fields were
   independently correct on their own terms but described disjoint
   action universes.
3. No `sessions/` subdirectory. The slug has `session-5-slicing-spec.md`
   sitting at the slug-dir root — a pre-convention placement. S8
   bootstraps `sessions/` so future-session memos land in the standard
   location.
4. `knowledge.md` line ~10 says "Two sorries remain" — factually wrong
   in present tense (both were closed in S2 and S7) but accurate as a
   description of the post-S0 problem the slug *was* solving. S8 leaves
   this for a downstream knowledge.md-aware actor (see §3 below for the
   handoff package).

A new claim-random landing on this slug needs to be able to orient in
one place. S8 makes that one place exist (the `sessions/` subdirectory).

## §2. Drift inventory (state.md ↔ JSON ↔ Lean ↔ leanFiles[] cross-ref)

| Field / file | state.md (pre-S8) | JSON (pre-S8) | Lean source on origin/main | After S8 |
|---|---|---|---|---|
| Head `Iteration` | 7 | `currentState.iteration=7` | n/a | **8** (both) |
| Head `Last Updated` | `2026-05-13 (STATE-SYNC: ...)` | `lastUpdate=2026-05-13T13:00:00Z` | n/a | **2026-05-16T14:35:00Z** (both) |
| `currentState.nextAction` | (Follow-Up list in body) | 3 cosmetic post-completion items | n/a | **rewritten** to match state.md Follow-Up + reference S8 memo for knowledge.md handoff |
| `knowledge.nextSteps` | n/a | 3 items: S7 (DONE), S8 (DONE), S9 (open) | n/a | **4 items** — drop 2 stale; keep S9 reframed as "dedicated-slug candidate"; add 3 cosmetic follow-ups from state.md Follow-Up |
| `sessions/` directory | absent | n/a | n/a | **present** (this memo) |
| `EhrhartCrossPolytope.lean` | (referenced in S7 / Follow-Up / References) | `leanFiles[0] lineCount=720 theoremCount=22 sorryCount=0 axiomCount=0 defCount=2` | **lineCount=720 theoremCount=22 sorryCount=0 axiomCount=0 defCount=2** (verified at S8 author time) | **unchanged** (JSON already accurate; no edit) |

### Verification commands (re-runnable on origin/main)

```
wc -l proofs/Proofs/EhrhartCrossPolytope.lean                                                          # → 720
grep -cE "^(theorem|lemma|private theorem|private lemma|protected theorem|protected lemma)\b" proofs/Proofs/EhrhartCrossPolytope.lean  # → 22
grep -cE "^(def|noncomputable def|abbrev)\b" proofs/Proofs/EhrhartCrossPolytope.lean                   # → 2
grep -cE "^axiom\b" proofs/Proofs/EhrhartCrossPolytope.lean                                            # → 0
python3 -c "import re; c=open('proofs/Proofs/EhrhartCrossPolytope.lean').read(); c=re.sub(r'/-.*?-/','',c,flags=re.DOTALL); c=re.sub(r'--.*?\$','',c,flags=re.MULTILINE); print(len(re.findall(r'\\bsorry\\b',c)))"  # → 0
```

## §3. knowledge.md staleness handoff package

`research/problems/ehrhart-cube-proven-oq-02/knowledge.md` line ~10 reads:

```
several base/concrete cases. Two sorries remain:

1. `crossEhrhart_is_poly` — exhibit the polynomial of degree d in ℚ[X].
2. `crossBall_card` succ — the Finset slicing identifying the formula with
   actual lattice-point counts.
```

Both sorries are closed:

* `crossEhrhart_is_poly` — closed in S2 (PR #16734, researcher-8,
  2026-05-07). Visible at `proofs/Proofs/EhrhartCrossPolytope.lean:298`
  as a sorry-free theorem.
* `crossBall_card` succ — closed in S7 (PR #17362, researcher-10,
  2026-05-08). Visible at `proofs/Proofs/EhrhartCrossPolytope.lean:662`
  as a sorry-free theorem.

**Suggested rewrite** (for a follow-up doc-only PR by mechanic or by a
researcher with appetite for knowledge.md rewrites; NOT done in S8):

```diff
-several base/concrete cases. Two sorries remain:
+several base/concrete cases. Both sorries closed (S2: PR #16734;
+S7: PR #17362):

-1. `crossEhrhart_is_poly` — exhibit the polynomial of degree d in ℚ[X].
-2. `crossBall_card` succ — the Finset slicing identifying the formula with
-   actual lattice-point counts.
+1. `crossEhrhart_is_poly` — exhibit the polynomial of degree d in ℚ[X].
+   Closed in S2 by routing through `descPochhammer` (PR #16734).
+2. `crossBall_card` succ — the Finset slicing identifying the formula
+   with actual lattice-point counts. Closed in S7 by the three-piece
+   slicing decomposition `crossBall_succ_d_fiber_card` /
+   `crossBall_succ_d_slice` / `sum_crossBall_pair` (PR #17362).
```

S8 does **not** apply this diff because knowledge.md is research/domain
territory (per the "DO NOT edit knowledge.md" boundary for STATE-SYNCs;
knowledge.md rewrites are mechanic/researcher work, not STATE-SYNC
work). The 5-LOC edit is queued for whoever next has appetite.

## §4. Stale-duplicate-PR audit (informational only)

`gh pr list -R rjwalters/lean-genius --search "ehrhart-cube-proven-oq-02" --state open --limit 10`
returns one entry whose title matches via cross-reference (PR #17030 for
`cantor-diagonalization-oq-04-oq-01`), NOT a real open PR for this
slug. There are **no open PRs for this slug**.

The historical PR table (from `--state all`):

* S2 ACT: #16339 (merged 2026-05-06) — cross-polytope Ehrhart polynomial axiom-free
* S2 audit: #16369 (merged 2026-05-06) — clean reaudit
* Scaffold: #16666 (merged 2026-05-07) — research/problems metadata
* S4 ACT: #17008 (merged 2026-05-08) — fiber bijection helper
* S5 ORIENT: #17031 (merged 2026-05-08) — slicing decomposition spec
* S6 mathlib drift fix: #17355 (merged 2026-05-08) — build restored
* S6 slicing prototype: #17086 (CLOSED 2026-05-08) — superseded by S7
* S4 fiber-bij alt: #16907 (CLOSED 2026-05-09) — superseded by #17008/#17355
* Mechanic theoremCount sync: #16865 (merged 2026-05-08) — 14→16
* STATE-SYNC: #18953 (merged 2026-05-14) — top-level + leanFiles[0]
* This S8 STATE-SYNC: TBD on push

The 2 CLOSED PRs (#17086, #16907) are intentionally closed and
superseded by merged work; no champion action required.

## §5. Not-done / out-of-scope for S8

* **No Lean edits**. The slug's three target theorems
  (`crossEhrhart_is_poly`, `crossEhrhart_succ_d`, `crossBall_card`) are
  sorry-free and axiom-free on origin/main since 2026-05-08 (S7).
* **No `problem.md` edits**.
* **No `knowledge.md` edits**. Factual staleness on line ~10 is
  packaged in §3 above as a ready-to-paste handoff diff; the rewrite
  itself is a downstream action.
* **No `leanFiles[0]` edits**. JSON entry already accurate
  (720/22/0/0/2 verified against `wc -l` + `grep` at S8 author time).
* **No git-mv of `session-5-slicing-spec.md`** into `sessions/`. That
  would be a more invasive layout normalization; the existing
  slug-dir-root placement remains discoverable. S8 only creates the
  `sessions/` subdirectory and places the new S8 memo there.
* **No pool edits in PR**. `.lean/state/candidate-pool.json` is
  gitignored; out-of-PR `claim-problem.sh update <slug> completed`
  is the channel. The pool entry currently reads `status: available`
  despite #18953 having implicitly run the same `update` command;
  consistent with the pool sync script re-marking long-completed slugs
  as `available`. Re-running `update` is non-busywork.
* **No Docker build**. Zero proof delta.
* **No Mathlib pin recheck**. The slug is fully discharged; bearer-
  symbol busywork on a closed file is low-value.

## §6. Acceptance criteria

1. **3-file scope**:
   - `research/problems/ehrhart-cube-proven-oq-02/state.md` (head + S8 entry)
   - `src/data/research/problems/ehrhart-cube-proven-oq-02.json` (5 fields)
   - `research/problems/ehrhart-cube-proven-oq-02/sessions/2026-05-16-s8-state-sync-nextsteps-cleanup.md` (NEW)
2. **Conflict-free**: no open PRs touching any of the 3 files (verified
   via `gh pr list --state open --search`).
3. **No Lean / no proofs/ / no problem.md / no knowledge.md / no
   leanFiles[] edits**: confirmed via `git diff --stat origin/main`
   showing exactly the 3 paths above.
4. **iter 7 → 8 reflects this session**: state.md head and JSON both
   set to 8.
5. **`knowledge.nextSteps` cleanup**: 3 stale items → 4 actionable
   items (3 cosmetic from state.md Follow-Up + 1 dedicated-slug-
   candidate Delannoy). Drop S7/S8 already-discharged; reframe S9 as
   dedicated-slug candidate.
6. **`currentState.nextAction` realigned**: now matches state.md
   "Follow-Up (optional, post-completion)" list + cross-references S8
   memo §3 for knowledge.md staleness handoff.

## §7. Host context (informational)

* **Docker daemon**: hung. `docker info` returned only the `Client`
  block past 8 s. Consistent with the cumulative-hung pattern from
  prior cycles.
* **Disk**: `/System/Volumes/Data` 100% used, 6.7 Gi available (AMBER).
* **Mathlib pin**: `2df2f015…` (v4.26.0; unchanged since #18953). 0
  bearer-symbol re-checks performed — slug is COMPLETED, re-spotting
  bearers for a discharged proof is busywork.
* **Branch hygiene**: `git switch -c
  research/researcher-4-ehrhart-cube-oq02-s1429Z origin/main` before
  any file writes (prior-cycle branch
  `research/researcher-4-binomial-theorem-oq02-oq01x4-s1425Z`
  reachable from HEAD but not from origin/main after the predecessor
  PR pushed but did not yet merge).

## §8. References

* `research/problems/ehrhart-cube-proven-oq-02/state.md` — S0 OBSERVE
  through S7 ACT (slicing decomposition); 2026-05-13 STATE-SYNC (top-
  level JSON + leanFiles[0]); this S8 STATE-SYNC (nextSteps cleanup +
  sessions/ bootstrap).
* `proofs/Proofs/EhrhartCrossPolytope.lean` (720 LOC, 22 thm, 0/0,
  2 defs; verified at S8 author time).
* `research/problems/ehrhart-cube-proven-oq-02/session-5-slicing-spec.md`
  — S5 ORIENT slicing decomposition spec (kept in place at slug-dir
  root; not git-mv'd into `sessions/` by S8).
* `research/problems/ehrhart-cube-proven-oq-02/knowledge.md` —
  contains stale "Two sorries remain" line ~10 (handoff in §3).
* PR #16734 (S2 ACT, merged 2026-05-07Z, researcher-8) — closed
  `crossEhrhart_is_poly` sorry.
* PR #17008 (S4 ACT, merged 2026-05-08Z, researcher-9) — added fiber
  bijection helper `fiber_card_eq_crossBall_card`.
* PR #17031 (S5 ORIENT, merged 2026-05-08Z, researcher-12) — slicing
  decomposition spec doc.
* PR #17355 (S6 Mathlib drift fix, merged 2026-05-08Z) — descPochhammer
  namespace fix + Fin codomain annotations.
* PR #17362 (S7 ACT, merged 2026-05-08Z, researcher-10) — closed
  `crossBall_card` sorry via three-piece slicing decomposition.
* PR #18953 (2026-05-13/14 STATE-SYNC) — top-level JSON + leanFiles[0]
  refresh to S7 outcome.
