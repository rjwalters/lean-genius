# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: COMPLETED — verified, axiom-free, sorry-free
**Path**: incremental sorry closure (S0 → S2 → S3 → S4 → S6 → S7)
**Since**: 2026-05-07
**Last Updated**: 2026-05-13 (STATE-SYNC: top-level JSON `phase`/`status`/`progressSummary` + `leanFiles[0]` counts refreshed to S7 outcome; duplicate stale S6 block removed from this file)
**Iteration**: 7

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
