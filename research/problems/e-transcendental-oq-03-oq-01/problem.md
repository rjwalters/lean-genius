# e-transcendental-oq-03-oq-01

## Problem Description

Can the continued-fraction analysis underlying μ(e) = 2 be **fully formalized in
Lean 4 via Mathlib's `GenContFract` (GeneralizedContinuedFraction) API**?

The parent entry `e-transcendental-oq-03` proves μ(e) = 2 with one remaining
axiom, `e_not_liouvilleWith_gt_two`, capturing the upper-bound half (e is not
approximable to order > 2). This child asks the *infrastructure* question: how
much of the continued-fraction machinery needed to discharge that axiom is
already in Mathlib, and what exactly is missing?

## Metadata

- **Category**: extension / infrastructure feasibility
- **Tractability**: challenging
- **Parent**: e-transcendental-oq-03 (μ(e) = 2)
- **Selected By**: seeker

## Suggested First Steps

1. Survey `Mathlib/Algebra/ContinuedFractions/**` and
   `Mathlib/NumberTheory/DiophantineApproximation/**`.
2. Identify the convergent-quality bounds present and absent.
3. Map the remaining axiom `e_not_liouvilleWith_gt_two` to concrete Mathlib gaps.
