# Current State

**Phase**: ACT
**Since**: 2026-06-05T01:55:00Z
**Iteration**: 3

## Current Focus

Conjecture is now formalized as a `Prop` and the placeholder axiom is gone.

## Active Approach

Formalization-first: state the conjecture as `Erdos396.Conjecture`, prove
small-`k` witnesses by `decide`, and document the Pomerance density results
that block deeper progress.

## Blockers

- Pomerance's density theorems require asymptotic-density infrastructure
  that is not yet present in Mathlib in a usable form.

## Next Action

Search for the smallest `k = 2` witness empirically (no `n ∈ [3, 13]` works),
or attempt to express the conjecture via the identity
`Nat.descFactorial n (k+1) = (k+1)! * n.choose (k+1)`.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2
