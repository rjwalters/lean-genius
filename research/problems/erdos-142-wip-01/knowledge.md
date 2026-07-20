# erdos-142-wip-01 — Asymptotic formula for r_k(N)

## State
Parent `Erdos142Problem.lean` was a definitions-only stub (arithProg, IsAPFree, rk;
0 theorems). The problem itself (asymptotic formula for r_k(N)) is OPEN and worth
$10,000; even k=3 (Roth / Kelley–Meka) is far from an asymptotic formula.

## Session 2026-07-20 (researcher-1)
Route: **foundational API on the def-only stub** (no attempt at the deep asymptotics —
that needs additive-combinatorial machinery well beyond Mathlib).

Added 13 axiom-free, sorry-free lemmas (host-verified Lean v4.31.0,
`#print axioms` = propext/Classical.choice/Quot.sound only):

- arithProg: `arithProg_zero`, `mem_arithProg`, `arithProg_card_le` (≤ k),
  `self_mem_arithProg`, `arithProg_one` (= {a}), `arithProg_card` (= k when d>0, via injectivity).
- IsAPFree: `IsAPFree_of_k_le_one`, `IsAPFree_empty`, `IsAPFree.subset` (downward closed).
- rk: `rk_le` (≤ N), `rk_mono_N` (monotone in N), `rk_zero` (rk k 0 = 0),
  `rk_eq_of_k_le_one` (rk k N = N for k ≤ 1).

## Blocked / not attempted
- Szemerédi (r_k(N) = o(N)), Roth/Kelley–Meka upper bounds, Behrend lower bound,
  Green–Tao k=4: all require machinery not in Mathlib. Route "prove asymptotics
  directly" is BLOCKED (reopen bar: materially new Mathlib additive-combinatorics
  infrastructure).
