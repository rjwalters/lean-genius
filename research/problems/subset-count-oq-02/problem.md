# subset-count-oq-02

## Problem Statement

How does the subset counting theorem (|P(S)| = 2^n) generalize to multisets?

For a multiset s with n elements (counted with multiplicity), the powerset
(all submultisets, counted with multiplicity) has cardinality 2^n. The number
of k-element submultisets is C(n, k).

## Source

- **Parent Proof**: subset-count (Number of Subsets of a Set, Wiedijk #52)
- **Category**: generalization
- **Tractability**: standard
- **Tags**: combinatorics, multisets, powerset, counting

## Approach Ideas

1. Use Mathlib's `Multiset.card_powerset` for the main result
2. Use `Multiset.card_powersetCard` for the fixed-size version
3. Connect back to the Finset (set) case

## Notes

Selected by Seeker on 2026-03-29. Formalization uses Mathlib's multiset powerset infrastructure.
