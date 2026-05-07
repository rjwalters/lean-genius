# Current State

**Phase**: ACT
**Since**: 2026-05-07T16:00:00.000Z
**Iteration**: 5

## Current Focus

Achievability base case for r = 1 proved at n = 4. Working toward uniform
construction for all n > 3.

## Active Approach

**Approach 1**: Concrete witness families.

- ✅ n = 4: F₄ = {{0, 1}, {0, 2, 3}}, sizes {2, 3} (formally verified)
- 🟡 n = 5: F₅ = {{0, 1}, {0, 2, 3}, {1, 2, 3, 4}}, sizes {2, 3, 4} (verified by hand;
  not yet in Lean)
- 🟡 n = 6: F₆ = {{0, 1}, {0, 2, 3}, {0, 2, 4, 5}, {1, 2, 3, 4, 5}},
  sizes {2, 3, 4, 5} (verified by hand; not yet in Lean)

**Approach 2**: Uniform construction (open).

- Tried shifted intervals A_s = {s, …, 2s−1} (mod n): works for n ≤ 5 but
  fails at n = 6 (A₂ = {2, 3} ⊆ A₅ = {0, 1, 2, 3, 5}).
- Tried prefix + sentinel A_s = {0, 1, …, s−2, n−1}: trivially nested
  (A_s ⊂ A_{s+1}).
- SCD-based: pick one element of size s from each chain in a symmetric chain
  decomposition; chains are disjoint so picks are pairwise incomparable.
  Mathlib does not currently have an SCD construction.

## Blockers

- General uniform construction for all n > 3 not yet found by hand;
  literature (Anderson, Engel) uses SCD but Mathlib lacks it.

## Next Action

1. Extend witness lemmas to n = 5 and n = 6 in Lean (mechanical).
2. Investigate Mathlib for any SCD-related lemmas.
3. If Mathlib lacks SCD, consider explicit family per n (e.g., conditional
   on n parity) instead of full uniform proof.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1 (n = 4 verified)
- Approaches tried: 3 (shifted intervals, prefix+sentinel, concrete witnesses)

## Strategic Notes

The structural lemmas already proved (`size1_and_complement_pair_only`,
`distinctSizes_card_le_n_sub_two`) gave the upper bound `≤ n − 2`. Closing
the gap to `≥ n − 2` requires a *constructive* witness for each n > 3.
Empirical extension obstructions (e.g., F₆ does not extend to F₇ by adding
one set) suggest the construction is not "monotone inductive" — each n
likely needs its own family or a non-trivial restructuring rule.
