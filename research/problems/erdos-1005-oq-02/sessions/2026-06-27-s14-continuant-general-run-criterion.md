# Session s14 — The continuant: a run-length criterion for *every* length

**Date**: 2026-06-27
**Researcher**: researcher-4
**Phase**: FORMALIZED (verified infrastructure; the open `1/12` constant remains open)
**Build**: `lake env lean` against the shared main-repo Mathlib `.olean` cache
(worktree `proofs/.lake` symlinks to `proofs/.lake`); Docker still down.

## Goal

Execute the iteration-13 "Next Action": replace the per-length §11/§12/§13 run
windows by ONE statement valid for arbitrary run length, via a `Continuant`
definition and a closed form for the iterated §9 Farey successor.

## What was added (§14, 0-sorry / 0-axiom)

Three definitions + ten theorems. `#print axioms` reports only
`propext / Classical.choice / Quot.sound` on every new theorem.

### Definitions
- `Continuant : List ℤ → ℤ` — minus-sign continuant, head-two-element recurrence
  `K(k₁ :: k₂ :: ks) = k₁·K(k₂ :: ks) − K(ks)`, bases `K([])=1`, `K([k])=k`.
- `secondCont : List ℤ → ℤ` — trailing continuant (coefficient of `a`):
  `secondCont (k::ks) = K(ks)`, `secondCont [] = 0`.
- `stepSeq a c ks` — the iterated successor: applies `tₘ₊₁ = kₘ·tₘ − tₘ₋₁` once
  per quotient in `ks` to the consecutive pair `(a,c)`, returning `t_{|ks|+1}`.

### Theorems
- `continuant_cons` — the **unified** single-step recurrence
  `K(k::ks) = k·K(ks) − secondCont ks`, valid in *every* case. Key subtlety: the
  naive "two shorter tails" recurrence `K(k::ks) = k·K(ks) − K(ks.tail)` is WRONG
  at `ks = []` (it gives `k·1 − K([]) = k−1` instead of `k`). The `secondCont []
  = 0` convention is exactly the `K₋₁ = 0` index convention of classical
  continuants, and repairs the edge case.
- `stepSeq_eq_continuant` (**headline**) — closed form
  `stepSeq a c ks = K(ks)·c − secondCont(ks)·a`, by induction on `ks` (generalizing
  `a c`), one `continuant_cons` rewrite + `ring` in the step.
- `endpoint_window` — `(a − pₘ)(b − qₘ)` factors as the continuant window
  `((1+secondCont ks)a − K·c)·((1+secondCont ks)b − K·d)` (pure `ring` after the
  closed form).
- `simOrd_run_iff` (**headline**) — endpoints of a length-`(|ks|+1)` run are
  `SimOrd` **iff** that single window is `≥ 0`. Proof is `rw [simOrd_iff_prod, hp,
  hq, endpoint_window]`.
- Ladder checks `continuant_two/_three`, `secondCont_one/_two/_three`: reproduce
  the §11/§12/§13 constants `1, k, k₁k₂−1, k₁k₂k₃−k₁−k₃` and `a`-coefficients
  `1, k₂, k₂k₃−1`.
- Subsumption checks `endpoint_window_one/_two/_three`: the general window
  *literally specializes* (by `ring`) to the §11 `(2a−kc)`, §12
  `((k₂+1)a−(k₁k₂−1)c)`, §13 `(k₂k₃·a−(k₁k₂k₃−k₁−k₃)c)` windows at `|ks|=1,2,3`.

## File delta

`Erdos1005ProblemOQ02.lean`: 1146 → 1317 lines, 57 → 71 theorems, 2 → 5 defs.

## Honest boundary

This is the *structural* run criterion. It does NOT bound the density of
quotient values for which the windows hold — that density count is the actual
`1/12`–`1/4` optimization and remains open. The gain is that the optimization is
now a single quantified statement (continuant positivity over a quotient list)
rather than an unbounded family of per-length inequalities.

## Next action

Density side. With `simOrd_run_iff` reducing runs to continuant positivity:
(1) prove `K(ks) ≥ 1`, `secondCont ks ≥ 0` for all-`≥1` quotient lists (induction
on `continuant_cons`) to certify the windows' sign structure; (2) characterize,
via the continuant, which quotient lists keep ALL non-adjacent windows
nonnegative — isolating the extremal configurations a density count toward
`1/12` must sum over. The continuant matrix `[[k,−1],[1,0]]` product gives `K` a
determinant/Cassini handle.
