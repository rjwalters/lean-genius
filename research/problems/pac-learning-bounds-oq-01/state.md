# Research State: pac-learning-bounds-oq-01

## Current State

**Phase**: COMPLETED (verified)
**Path**: full
**Since**: 2026-04-27
**Last Updated**: 2026-04-27T22:45:00Z
**Iteration**: stable — single completed formalization

## Current Focus

None — the OQ-01 instance for threshold classifiers on ℕ has been
formalized, verified, and integrated as a gallery entry.

## Active Approach

None.

## Blockers

None. Gallery entry `pac-learning-bounds-oq-01` ("VC Dimension of
Threshold Classifiers on ℕ") is complete:

- `proofs/Proofs/PACLearningOQ01.lean`: 86 lines, **0 sorries**,
  **0 axioms**, status: `verified`.
- 2 definitions: `Shatters` (standard set-based shattering predicate),
  `thresholdClassifiers` (the family `{ x ↦ x < t : t ∈ ℕ }`).
- 3 theorems:
  - `threshold_shatters_singleton` — every singleton `{a}` is shattered,
    witnessed by `t = a + 1` (include) or `t = 0` (exclude).
  - `threshold_not_shatters_pair` — for `a < b`, the labeling `T = {b}`
    cannot be realized: would need `t ≤ a` (to exclude `a`) and `t > b`
    (to include `b`), contradicting `a < b`.
  - `threshold_vcdim_bounds` — combines the two: VC dim is exactly 1.

This entry directly answers the parent's open question
(pac-learning-bounds OQ-01: "Can the VC dimension of specific hypothesis
classes be computed in Lean?") for the canonical "smallest interesting"
hypothesis class. The proof uses only `Finset` and `Nat` API from
Mathlib — no axioms, no `WithTop ℕ`-valued vcDim definition required
because the question is local to a *specific* hypothesis class rather
than a general definition of vcDim.

## Next Action

None for the research-agent loop. Possible follow-up entries that would
extend this work but are *not* part of this OQ:

1. **Interval classifiers on ℕ (expected VC dim 2).** Requires a
   "no triple shattered" lemma using interval convexity — the geometric
   analogue of the monotonicity obstruction used here.
2. **Half-space classifiers on ℝᵈ (expected VC dim d + 1).** Requires
   linear algebra and Radon's theorem.
3. **Generalize to thresholds on any totally ordered set.** The proof
   uses only the order, not arithmetic on ℕ — a clean Mathlib-style
   generalization (replace `ℕ` with `[LinearOrder α]`).
4. **Define `vcDim` as a `WithTop ℕ`-valued function** (sup over
   shattered Finsets) and prove `vcDim H_thr = 1` directly, not just
   via the two bounds.
5. **Formalize Sauer-Shelah polynomial growth bound** — the foundation
   of distribution-free PAC learning. The `d = 1` instance is implicit
   here (`Π_H(n) ≤ n + 1`); the general bound is significantly heavier.

Each of these would become its own gallery entry advancing the parent
OQ.

## Attempt Counts

- Total attempts: stable (single completed formalization)
- Current approach attempts: 0
- Approaches tried: direct VC computation via two bounds (successful)

## Provenance

- Gallery entry created and verified on 2026-04-27.
- Lean file: `proofs/Proofs/PACLearningOQ01.lean`.
- Gallery slug: `pac-learning-bounds-oq-01`.
- This research/state entry was created on 2026-04-27 to reconcile the
  candidate-pool record (which was still tagged `in-progress` with
  initial-template notes) with the actual completed formalization.
