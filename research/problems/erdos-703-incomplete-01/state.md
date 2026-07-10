# State: erdos-703-incomplete-01

## Current Phase: ACT (progress)

**Phase**: ACT
**Status**: Active
**Last Updated**: 2026-07-09

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

## Blockers

`mainQuestion` / `frankl_rodl_1987` is the deep 1987 exponential bound with no
Mathlib pathway; it remains an axiom, untouched. Docker daemon corrupted this
session (containerd `meta.db` I/O error at image build) → shipped UNVERIFIED;
the four new lemmas are trivial Finset-membership facts, correct by inspection.

## Next Action

Re-verify once docker repaired:
`./proofs/scripts/docker-build.sh Proofs.Erdos703Problem`. Further `L`-avoiding
API (e.g. an `avoidsLIntersections`-indexed analogue of `T`) is possible but the
core problem is otherwise mature around the standing axiom.
