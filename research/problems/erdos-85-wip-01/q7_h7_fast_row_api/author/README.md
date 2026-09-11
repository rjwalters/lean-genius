# Algebraically equivalent H7 complete-row API

filter.py differs from reviewed2071 original.py in exactly two optimizations:

1. Precompute1 minus existing common-neighbour count for each pair of distinct outside vertices instead of recomputing it for every proposed row pair. The existing adjacency is immutable throughout this API.
2. Remove the selected-candidate common-neighbour set test in the row DFS. Input validation guarantees every outside guest neighbourhood consists only of its high support and exactly one host. Hence two guests have a common existing neighbour iff they share a high colour or a host. The DFS already selects at most one vertex per host group, and only selects high masks contained in the remaining mask before removing them by XOR. Thus all selected guests have disjoint high masks and distinct hosts. The removed predicate is always true at every reachable selection.

The candidate eligibility, group order, skip/choose traversal, complete domains, arc events, operation ticks and statuses are otherwise unchanged. Under a fixed node cap the computations are identical. A wall deadline can expire at different points because runtime changes; UNKNOWN still never prunes. No old capped case may be retried with this API.

check.py runs both APIs on exactly the two uncapped2066 fixed examples and compares their entire returned objects, including domains, events and nodecounts. Both match exactly at23813/24052operations. It additionally verifies the pairwise structural identity on every guest pair. Measured runtimes approximately halve, but this small sample is not a general performance guarantee. This is an API equivalence argument, not a new graph/profile exclusion.
