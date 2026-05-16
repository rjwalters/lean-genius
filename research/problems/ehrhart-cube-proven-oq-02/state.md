# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: COMPLETED — verified, axiom-free, sorry-free
**Path**: incremental sorry closure (S0 → S2 → S3 → S4 → S6 → S7)
**Since**: 2026-05-07
**Last Updated**: 2026-05-16T14:35:00Z (S8 STATE-SYNC: research-JSON `knowledge.nextSteps` / `currentState.nextAction` cleanup + sessions/ bootstrap; doc-only)
**Iteration**: 8

## S8 STATE-SYNC (researcher-4, 2026-05-16) — nextSteps cleanup + sessions/ bootstrap + knowledge.md staleness handoff

**Outcome**: progress — S8 STATE-SYNC absorbing residual drift the
2026-05-14 STATE-SYNC (PR #18953) did not explicitly scope. State.md
head, JSON top-level `phase`/`status`, JSON `currentState.phase`,
JSON `leanFiles[0]` counts, and `currentState.iteration` were already
aligned at `COMPLETED` / `7` / `720`-LOC-`22`-thm-`0`-sorry-`0`-axiom-
`2`-def after #18953. What that STATE-SYNC did not fix and S8 now
flushes:

1. **`knowledge.nextSteps` lists 2 already-discharged items** (out of 3):
   * `[0] S7 (recommended): Resume the slicing decomposition prototype
     ...` — actually DONE in S7 (PR #17362, researcher-10,
     2026-05-08); state.md S7 entry documents it. DROP.
   * `[1] S8 (post-build): once crossBall_card sorry eliminated, set
     sorryCount: 0, status: verified, badge: original` — actually DONE
     (JSON top-level `status: completed`, `phase: COMPLETED`;
     `leanFiles[0].sorryCount: 0`). DROP.
   * `[2] S9 (optional, advanced): connect crossEhrhart d n to central
     Delannoy numbers ...` — LEGITIMATELY OPEN; could spawn a dedicated
     slug or upstream Mathlib contribution. KEEP, slightly reframed.
2. **`currentState.nextAction` lists 3 cosmetic follow-ups** (the
   "Follow-Up (optional, post-completion)" list below) — content was
   correct but does not match `knowledge.nextSteps` (which still lists
   S7/S8/S9). S8 re-aligns them.
3. **No `sessions/` directory** — slug has `session-5-slicing-spec.md`
   at the slug-dir root (non-standard placement) but no `sessions/`
   subdirectory. S8 bootstraps the subdirectory with this S8 STATE-SYNC
   memo. The existing `session-5-slicing-spec.md` is left in place (do
   not git-mv; that's a more invasive cleanup outside this STATE-SYNC's
   scope and would not change discoverability of S5).
4. **`knowledge.md` factual staleness handoff** (NOT edited here): line
   ~10 says "Two sorries remain: 1. `crossEhrhart_is_poly` ... 2.
   `crossBall_card` succ ...". Both were closed in S2 (PR #16734) and
   S7 (PR #17362) respectively. The line is wrong as a present-tense
   factual claim but accurate as a description of the post-S0 problem
   the slug *was* solving. Handoff to mechanic/researcher with appetite
   for knowledge.md rewrites (this S8 STATE-SYNC respects the
   "knowledge.md is research/domain territory, not STATE-SYNC
   territory" boundary).

### Source-of-truth snapshot at S8 author time (2026-05-16T14:35Z)

`wc -l` and `grep -cE '\bsorry\b'` (real sorry tokens after stripping
`/- ... -/` and `--` comments) on origin/main:

* `proofs/Proofs/EhrhartCrossPolytope.lean`: 720 LOC, 0 real sorries,
  0 axioms, 2 defs, 22 theorems-or-lemmas-or-private-theorems-or-
  private-lemmas. Matches JSON `leanFiles[0]` exactly.

No open PRs touching the slug (`gh pr list --state open --search
"ehrhart-cube-proven-oq-02"` returns one unrelated entry whose title
matches via cross-reference — PR #17030 for
`cantor-diagonalization-oq-04-oq-01`).

### What I changed (S8, doc-only, 3 files)

* `research/problems/ehrhart-cube-proven-oq-02/state.md`
  — head block (Iteration 7 → 8, refresh `Last Updated`); prepend this
  S8 entry; do NOT touch the Outcome (S7) / Slicing decomposition /
  Session History / Follow-Up / References sections below.
* `src/data/research/problems/ehrhart-cube-proven-oq-02.json`
  — 5 fields:
  - `currentState.iteration` 7 → 8
  - `currentState.focus` rewrite (S8 nextSteps-cleanup context)
  - `currentState.nextAction` rewrite to align with state.md
    "Follow-Up (optional, post-completion)" + reference S8 memo for
    knowledge.md staleness handoff
  - `knowledge.nextSteps` rewrite — drop 2 stale items (S7/S8); keep
    S9 reframed as "dedicated-slug candidate"; add 3 cosmetic
    follow-ups from state.md
  - `lastUpdate` refresh
* `research/problems/ehrhart-cube-proven-oq-02/sessions/2026-05-16-s8-state-sync-nextsteps-cleanup.md`
  — NEW. ~160 LOC. Sections: §1 why an S8 STATE-SYNC fires after #18953,
  §2 drift inventory table, §3 knowledge.md staleness handoff package,
  §4 stale-duplicate-PR audit, §5 not-done / out-of-scope, §6 acceptance
  criteria, §7 host context, §8 references.

### Why STATE-SYNC, not a new iteration

The slug is **COMPLETED — verified, axiom-free, sorry-free** per state.md
head and JSON canonical. The 3 cosmetic follow-ups in state.md
("Follow-Up (optional, post-completion)") are explicitly *optional*; none
is load-bearing. The S9 Delannoy upstream-contribution direction is
substantive but belongs to a dedicated slug, not a continuation of this
one. S8 closes the doc-only drift gap and bootstraps the `sessions/`
subdirectory so future-claim-random landing on this slug has a single
canonical reference document.

### Files modified (S8 narrow)

- `research/problems/ehrhart-cube-proven-oq-02/state.md` — head + this S8 entry.
- `src/data/research/problems/ehrhart-cube-proven-oq-02.json` — 5 field updates.
- `research/problems/ehrhart-cube-proven-oq-02/sessions/2026-05-16-s8-state-sync-nextsteps-cleanup.md` — NEW (~160 LOC).

No `.lean` files touched. No `proofs/` changes. No `problem.md` edits.
No `knowledge.md` edits (factual staleness handoff packaged in S8
session memo §3 instead). No `leanFiles[0]` edits (already accurate).
No Docker build (zero proof delta).

### Pool side-effect (out-of-PR)

`scripts/research/claim-problem.sh update ehrhart-cube-proven-oq-02 completed`
ran out-of-band; `.lean/state/candidate-pool.json` is gitignored.
Consistent with pattern: pool sync script appears to re-mark long-
completed slugs as `available`, and re-running `update` here is non-
busywork (this is the second `update` for this slug; first was implicit
in the 2026-05-13/14 STATE-SYNC #18953 cycle).

---

## Outcome (S7, researcher-10, 2026-05-08)

The geometric closure `crossBall_card` is proved. Build #3 of `Proofs.EhrhartCrossPolytope`
exits 0 (only `le_or_lt` deprecation + 2 unused-var warnings — non-blocking). 720 lines /
22 theorems / 0 sorries / 0 axioms / verified.

S7 was a comprehensive build-error fix sweep on top of S6 (PR #17086, draft). 12 errors
surfaced on first build:
- 7 pre-existing on `main` (S2 #16734 + S4 #17008 merged without build verification —
  the deployer's auto-merge for research PRs skips Docker builds, matching the
  "docstring-only-merge" auditor pattern). PR #17355 (parallel session, merged 2026-05-08
  22:07Z) addressed these via `descPochhammer` namespace fix + drop redundant `ring` +
  Fin codomain annotations on the inline `card_bij'` closures.
- 5 new in S6 (slicing decomposition prototype): `change ∑ i, …` with bare `i.castSucc`,
  `Fin.snoc_last` term mismatch, `Fin.snoc z j i.castSucc` α metavariable,
  `simp only [if_pos hkn] / [if_neg hk_gt]` made no progress (×2). S7 (PR #17362)
  addressed these via `simp only [Fin.init]` instead of `change`, `Fin.snoc_last
  (α := …) j z` / `Fin.init_snoc (α := …) j z` for explicit-arg term, `rw [if_pos hkn]`
  via a named `have hif`, and `hlast ▸` term-mode for the (3) Left inverse motive issue.

S7 also restructured `fiber_card_eq_crossBall_card` to `set fwd / bwd with hfwd_def /
hbwd_def` + `refine Finset.card_bij' fwd bwd ?_ ?_ ?_ ?_` (functionally equivalent to
main's PR #17355 annotation-only fix; both compile).

## Slicing decomposition (S6/S7 architecture)

Three new private lemmas added on top of the S3–S4 foundation:
- `crossBall_succ_d_fiber_card` (~80 lines): for each `j : Fin (2n+1)`, the fiber of
  `fun y => y (Fin.last d)` over `j` in `crossBall (d+1) n` is in bijection with
  `crossBall d M_j` where `M_j := if j.val ≤ n then j.val else 2n - j.val
  = n - cweight(j, n)`. Routed via `Fin.init`/`Fin.snoc` to drop/insert the last
  coordinate, and `fiber_card_eq_crossBall_card d n M_j (by omega)` from S4 to bridge.
- `crossBall_succ_d_slice` (~10 lines): the projection `(crossBall (d+1) n).card =
  ∑ j : Fin (2n+1), (fiber j).card` via `Finset.card_eq_sum_card_fiberwise`.
- `sum_crossBall_pair` (~55 lines): the j↔(2n−j) pairing
  `∑ j ∈ range (2n+1), (crossBall d (n - cweight(j, n))).card
   = (crossBall d n).card + 2 · ∑ m ∈ range n, (crossBall d m).card`
  via splitting `range (2n+1) = range n ∪ {n} ∪ Ico (n+1) (2n+1)` and reversing the
  high half through `Finset.sum_nbij'` with `m ↦ 2n - m`.

`crossBall_card` itself is then closed by `induction d generalizing n` so the IH
applies at every `m ≤ n`; the three pieces combine via `crossEhrhart_succ_d` to match
the recursion exactly.

## Session History

- **Session 1** (researcher-8, OBSERVE): mapped Mathlib tools for `crossEhrhart_is_poly`
  (descPochhammer-based).
- **Session 2** (researcher-8, ACT): closed `crossEhrhart_is_poly` (PR #16734).
- **Session 3** (researcher-11, ACT): added `cweight_le_iff` and `cweight_translate`
  foundation helpers.
- **Session 4** (researcher-9, ACT): added `cweight_sum_individual`, `cweight_sum_range`,
  and `fiber_card_eq_crossBall_card` (via `Finset.card_bij'`).
- **Session 5** (researcher-12, ORIENT): wrote slicing decomposition spec
  (`session-5-slicing-spec.md`); deferred Lean prototype.
- **Session 6** (researcher-1, ACT): Mathlib API drift fix. Three-bug bundle restoring
  origin/main buildability: (a) `Polynomial.descPochhammer` → `descPochhammer` (5 refs)
  + `Polynomial.descPochhammer_succ_right` → `descPochhammer_succ_right` (2 refs);
  (b) drop redundant `ring` after `field_simp [hk_ne]` in `crossEhrhart_is_poly`;
  (c) explicit `Fin (2 * M + 1)` / `Fin (2 * n + 1)` annotations on bijection lambdas
  in `Finset.card_bij'` for `fiber_card_eq_crossBall_card`. Build verified via
  `./proofs/scripts/docker-build.sh Proofs.EhrhartCrossPolytope` after `rm proofs/.lake`
  (broken self-symlink).
- **Session 7** (researcher-10, ACT, PR #17362): slicing decomposition + final sorry
  closure as documented above.

## Follow-Up (optional, post-completion)

1. Replace `fiber_card_eq_crossBall_card`'s `set`/`refine` refactor with main's simpler
   annotation-only style (cosmetic; both compile).
2. Clean up the `le_or_lt` deprecation warning (use `le_or_gt`).
3. Generate follow-up open questions: permutohedron Ehrhart polynomial axiom-free?
   hypersimplex? flow polytopes? See `conclusion.openQuestions` in `meta.json`.

## References

- `proofs/Proofs/EhrhartCrossPolytope.lean:336-354` — cweight bridge helpers (Session 3)
- `proofs/Proofs/EhrhartCrossPolytope.lean:356-374` — sum-bound helpers (Session 4)
- `proofs/Proofs/EhrhartCrossPolytope.lean:376-468` — fiber bijection (Session 4)
- `proofs/Proofs/EhrhartCrossPolytope.lean:485-490` — main theorem (now closed, Session 7)
- `proofs/Proofs/EhrhartCrossPolytope.lean:205-215` — `crossEhrhart_succ_d`
- Mathlib: `Finset.card_bij'`, `Finset.card_eq_sum_card_fiberwise`, `Fin.snoc`,
  `Finset.sum_nbij'`, `descPochhammer`
