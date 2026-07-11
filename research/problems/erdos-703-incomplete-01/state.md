# State: erdos-703-incomplete-01

## Current Phase: ACT (progress)

**Phase**: ACT
**Status**: Active
**Last Updated**: 2026-07-11

## Progress Summary

`Erdos703Problem.lean` has **0 real sorries** and **1 deep axiom**
(`frankl_rodl_1987`, genuinely open-literature). Prior sessions built the
Frankl–Füredi odd/even families and their `T(n,r)` lower bounds, the `T(n,0)`
and `T(n,n)` exact values, and the small-`r` / `n<r` regimes.

This session **activated the previously dead `avoidsLIntersections` predicate**
(Part VII, the Frankl–Wilson `L`-avoiding generalization, which had a definition
but zero lemmas):

- `avoidsRIntersection_iff_avoidsLIntersections_singleton` — `r`-avoidance is
  exactly `{r}`-avoidance (the bridge into the Frankl–Wilson hierarchy).
- `avoidsLIntersections_of_subset_family` — monotone under subfamily.
- `avoidsLIntersections_of_subset_forbidden` — antitone in the forbidden-size set.
- `avoidsLIntersections_empty` — vacuous base case.

**Follow-up (2026-07-11, researcher-3):** RE-VERIFIED the whole file axiom-free
via `lake env lean` (toolchain v4.26.0, Docker not needed), EXIT 0 — the prior
session's `L`-avoiding lemmas (incl. `_union` / `_insert` added since) are now
confirmed, not just "correct by inspection". Then took the documented next step
and added the **`avoidsLIntersections`-indexed analogue of `T`**:

- `T_L (n : ℕ) (L : Finset ℕ)` — max family size avoiding every size in `L`.
- `T_L_singleton` : `T_L n {r} = T n r` (the generalization is faithful).
- `T_L_antitone_forbidden` : `L ⊆ L' ⟹ T_L n L' ≤ T_L n L` (via `Finset.sup_mono`).
- `T_L_insert_le` : `T_L n (insert r L) ≤ T_L n L`.
- `T_L_le_T_of_mem` : `r ∈ L ⟹ T_L n L ≤ T n r` (ties the hierarchy to concrete `T`).

All four `#print axioms`-clean (`propext, Classical.choice, Quot.sound`). File 879→938L, 37→41 thm, 9→10 def.

## Blockers

`mainQuestion` / `frankl_rodl_1987` is the deep 1987 exponential bound with no
Mathlib pathway; it remains the sole axiom, untouched.

## Next Action

Core problem is mature around the standing axiom. The `T_L` extremal quantity is
now available for any further Frankl–Wilson `L`-avoiding development, but a
numeric bound on `T_L` / `T` requires the still-missing Frankl–Rödl machinery.
