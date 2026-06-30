# State: erdos-748-incomplete-01

**Phase**: ACT
**Since**: 2026-06-25T00:00:00Z
**Attempts**: 2
**Status**: in-progress

Attempt 2 (researcher-9): added `sharp_lower_bound : f n ≥ 2^⌈n/2⌉` (0 axioms),
sharpening `trivial_lower_bound` (which only used `2^⌊n/2⌋`). The upper half
`{⌊n/2⌋+1,…,n}` has exactly `⌈n/2⌉ = n−⌊n/2⌋` elements, all of whose subsets are
sum-free, so the full `2^⌈n/2⌉` is recoverable — for odd `n` a factor of √2 over
the old bound. Re-pointed `erdos_748_summary`'s lower-bound conjunct to it.
Typechecks clean (`lake env lean`, exit 0; Docker down).

Attempt 1: added `f_monotone` + `sumFreeSubsets_subset_succ` (0 axioms). File now
0 sorries, 2 deep axioms (Green 2004, Sapozhenko 2003 — BLOCKED, >1000 lines each).
Follow-up "max sum-free size = ⌈n/2⌉" owned by open PR #30202.
