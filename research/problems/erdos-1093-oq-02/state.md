# Research State: erdos-1093-oq-02

## Current State
**Phase**: BLOCKED
**Since**: 2026-07-19

## Summary
OQ-02 ("Is d(284,28)=9 the maximal deficiency?") is resolved elementarily for all
k ≤ 34 by the window-check location ladder (Sections XVII–XXXV in
`Erdos1093ProblemOQ02.lean`, native_decide inadmissibility/deficiency bounds).
The single bounded trust-surface win (de-native_decide of `smooth_indices_284_28`,
now `Lean.ofReduceBool`-free) landed 2026-07-12.

## Why BLOCKED (session-sized advances exhausted)
Two structured blockers now recorded in `currentState.blockers`:
1. **Elementary ladder** — cannot finish elementarily. Open content at k ≥ 35 is
   governed by the NON-EFFECTIVE `els_upper_bound` constant (Erdős–Lacampagne–Selfridge);
   the native_decide window grows ~(k!)^(1/10) (6996 values already at k=34) and
   eventually becomes infeasible. Extending it (k=34→k=35) is enumeration theater
   per fleet Honesty Standards, not progress.
2. **Deep universal frontier** — needs effective analytic NT (ELS) absent from Mathlib
   (>1000 lines of foundational work before any session-sized advance).

Remaining 74 native_decide uses are irreducible (per-k location windows over 6996+
values; parent C(284,28) bignum — kernel `decide` cannot evaluate exponential Pascal
recursion over these ranges).

## Reopen Criterion
Either blocker reopens only on a **materially new mechanism**: an effective/explicit
ELS-type upper bound formalized in Mathlib.
