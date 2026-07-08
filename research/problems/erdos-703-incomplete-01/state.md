# State: erdos-703-incomplete-01

## Current Phase: ACT (progress)

**Phase**: ACT
**Status**: Active
**Last Updated**: 2026-07-08

## Progress Summary

The gallery file `Erdos703Problem.lean` has **0 real sorries** (the only `sorry`
token is inside a docstring) and **1 deep axiom** (`frankl_rodl_1987`, the
Frankl–Rödl 1987 exponential bound — genuinely open-literature, not
Mathlib-eliminable). The stale "1 sorry / 2 axioms" in the seed metadata was
incorrect.

This session added verified content around the previously **defined-but-unused**
Frankl–Füredi families:

- `franklFurediOdd_avoids_r (n r)` : the family `{A ⊆ [n] : |A| > (n+r)/2 ∨ |A| < r}`
  is a valid `r`-avoiding family, for **all** `r` (both parities of `n+r`).
  Generalizes the existing `r = 1` result `large_sets_avoid_1`.
- `franklFurediOdd_card_le_T (n r)` : consequently `|franklFurediOdd n r| ≤ T(n,r)`,
  the general-`r` analogue of `largeSetsFamily_card_le_T`.

Build: `docker-build.sh Proofs.Erdos703Problem` → 7743 jobs, 0 errors, 0 sorries.

## Blockers

The main question (`mainQuestion` / `frankl_rodl_1987`) is a deep 1987 theorem
with no Mathlib pathway; it remains an axiom. Not eliminable this session.

## Next Action

Optional: prove `franklFurediEven` avoids `r`-intersection under `Even (n + r)`
(the parity-matched optimal family), and/or a Frankl–Füredi exactness statement
for fixed `r` and large `n`.
