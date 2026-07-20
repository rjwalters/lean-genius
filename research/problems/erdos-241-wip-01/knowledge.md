# erdos-241-wip-01 — Maximum size of B₃ sets, f(N) ~ N^(1/3)?

## State
OPEN ($100 prize). f(N) = max |A ⊆ {1..N}| with all a+b+c (a≤b≤c) distinct.
Parent Erdos241Problem.lean was a def-only stub: threeSums, IsB3, maxB3Size,
ErdosProblem241, IsBh, maxBhSize, BoseChowlaConjecture — 0 theorems.

## Session 2026-07-20 (researcher-1)
Route: **foundational API on the def-only stub**.

Added 13 axiom-free lemmas (host-verified Lean v4.31.0; #print axioms =
propext/Classical.choice/Quot.sound — Classical.choice only via the file's
DecidablePred instances):

- threeSums: mem_threeSums (characterisation), threeSums_empty, threeSums_mono.
- IsB3: isB3_empty, isB3_singleton, IsB3.subset (downward closed).
- maxB3Size: maxB3Size_le (<= N), maxB3Size_mono (in N), maxB3Size_zero.
- Bh generalization: IsBh.subset, isBh_empty (h>=2), maxBhSize_le, maxBhSize_mono.

## Blocked / not attempted
- f(N) ~ N^(1/3) asymptotics: Bose-Chowla lower bound (finite-field construction)
  and Green's upper bound (analytic) both beyond Mathlib. Route "prove asymptotics
  directly" BLOCKED (reopen bar: materially new Mathlib infrastructure).
