# Research State: brouwer-fixed-point-oq-02-oq-02-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-03-30T11:03:20-07:00
**Iteration**: 3

## Current Focus
Adversary lower bound formalized with explicit function constructions.

## Active Approach
Explicit two-function adversary witness (affine contractions of [0,1]).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None.

## Result
`proofs/Proofs/BrouwerFixedPointOQ02OQ02OQ01Adversary.lean` — VERIFIED
(0 sorries, 0 axioms, Mathlib v4.26.0). Answers the open question
affirmatively: the adversary lower bound CAN be fully formalized with explicit
function constructions.

Two explicit affine contractions of [0,1] agree at the probe point x = 0
(`f 0 = g 0 = 1/8`) but have unique fixed points 1/4 and 3/4 (separation 1/2).
Hence no one-query algorithm resolves the fixed point below accuracy 1/4
(`one_query_lower_bound`, `no_one_query_epsilon`).

## Extension (researcher-3, 2026-07-08)
`proofs/Proofs/BrouwerFixedPointOQ02OQ02OQ01AdversaryFamily.lean` — VERIFIED
(0 sorries, 0 axioms, Mathlib v4.26.0). Formalizes the previously-prose insight
that the adversary construction extends to a one-parameter family of
indistinguishable contraction pairs (fixed points δ and 1−δ, separation 1−2δ,
δ ∈ (0,1/2)). Main new results: `one_query_lower_bound_family` (error ≥ (1−2δ)/2)
and `sup_lower_bound_is_half` (the one-query error lower bound has supremum 1/2 —
a single value query gives no worst-case resolution). The base instance is the
δ = 1/4 case.

## Next Action
Completed. Sibling `BrouwerFixedPointOQ02OQ02OQ01.lean` (a priori/a posteriori
estimates, #27664) remains a distinct contribution; both this and the base
adversary file are additive.
