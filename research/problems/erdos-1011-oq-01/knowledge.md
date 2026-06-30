# Knowledge Base: erdos-1011-oq-01

## Problem Understanding

Seeker-minted descendant of Erdős Problem #1011 ("Triangles in Graphs with High
Chromatic Number"). The parent studies `f_r(n)`, the minimal edge count forcing
a triangle in an `n`-vertex graph of chromatic number ≥ r, and is OPEN in
general. The parent file `Erdos1011Problem.lean` axiomatizes the known small
cases (5 axioms total). This OQ-01 target: **discharge the triangle base case**
— `f_2(n)`, which is Mantel's theorem (1907), the `r = 2` instance of Turán's
theorem — converting the parent's `turan_theorem` axiom into a proved theorem.

## Progress Summary

VERIFIED & SHIPPED (researcher-7, 2026-06-28, PR pending). Authored
`proofs/Proofs/Erdos1011OQ01.lean`, a self-contained (Mathlib-only) file proving
with 0 axioms / 0 sorries:

- `triangleFree_card_edgeFinset_le` — Mantel's bound: a triangle-free graph
  (`G.CliqueFree 3`) on `n` vertices has `#edges ≤ n²/4`.
- `four_mul_card_edgeFinset_le` — cleared-denominator form `4·#edges ≤ n²`.
- `turanGraph_two_triangleFree` — the Turán graph `turanGraph n 2` is triangle-free.
- `card_edgeFinset_turanGraph_two` — its exact edge count `(n²−(n%2)²)/4`.
- `mantel_sharp_even` — sharpness: for even `n`, `turanGraph n 2` is triangle-free
  with exactly `n²/4` edges.

## Insights

- The whole result is a *specialization* of Mathlib's Turán development, not a
  new proof: "triangle-free" = `CliqueFree 3`, and "no triangle" is the `r = 2`
  case of `K_{r+1}`-free. `SimpleGraph.CliqueFree.card_edgeFinset_le` at `r = 2`
  IS Mantel's theorem.
- Mathlib states the bound with exact integer corrections
  `(n²−(n%r)²)(r−1)/(2r) + (n%r).choose 2`. At `r=2` the binomial term is 0
  (`n%2 ≤ 1 < 2`, `Nat.choose_eq_zero_of_lt`) and the subtraction only lowers
  the bound, so the textbook `⌊n²/4⌋` drops out by `Nat`-division monotonicity.
- Sharpness is given by an explicit witness (`turanGraph n 2`) with a computed
  exact edge count, not asserted.

## Verification status

**VERIFIED (0-axiom).** Docker down; used host fallback
`cd proofs && /opt/homebrew/bin/lake env lean <worktree>/proofs/Proofs/Erdos1011OQ01.lean`
against prebuilt Mathlib 4.26.0 oleans — 0 errors. `#print axioms` on all 5
theorems shows only `[propext, Classical.choice, Quot.sound]` (no sorryAx, no
Lean.ofReduceBool). Gallery entry authored under
`src/data/proofs/erdos-1011-oq-01/` (status verified / badge original).

## Dead Ends / Notes

- Did NOT attempt to discharge the parent's other 4 axioms (Erdős–Gallai f_3,
  Simonovits/Davies–Illingworth/HHKP asymptotics) — those are deeper and not
  obviously available in Mathlib 4.26.0. Flagged as follow-ups in the gallery
  meta `openQuestions`.
- Mathlib's Turán bound is *structural* (graph isomorphism to `turanGraph`) plus
  the edge-count corollary `CliqueFree.card_edgeFinset_le`; the latter is the
  directly usable form for the upper bound.
