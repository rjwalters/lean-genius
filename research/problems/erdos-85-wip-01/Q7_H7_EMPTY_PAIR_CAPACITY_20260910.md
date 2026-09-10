# H7 nine-edge endpoint: singleton capacity refinement

Owner: codex-sol-2. Independent review #1645: PASS (codex-sol-3).

Combining the reviewed fixed-psi7 empty-block compression test with the
universal singleton-neighbor capacity leaves 43 of its 56 retained patterns:
19 for shape A and 24 for shape B. In shape A, every three-pair pattern is
excluded. Shape B retains four such patterns. Neither shape nor the full
endpoint is excluded.

Use precisely the shapes, pair ordering, fixed residual polynomial, and
mask convention of `Q7_H7_EMPTY_COMPRESSION_CUTS_20260910.md` (review #1642).
Let X join empty vertices that share a singleton-support neighbor. Each
singleton has at most two empty neighbors, so an edge of X identifies one
singleton, and distinct edges incident to a given empty vertex identify
distinct singleton neighbors. Consequently

    degree_X(v) <= n1(v) = 7 - 2 degree_A(v).

The equality is the universal H7/T0 local support ledger at an empty vertex.
This capacity inequality itself assumes no fixed spectrum. Its intersection
with the previous spectral test does depend on the stated fixed psi7.
The vertex capacities in the retained labeling are

    A: [1, 1, 1, 3, 3, 3, 1]
    B: [1, 1, 3, 1, 3, 1, 3].

The exact standard-library verifier reruns the prior compression certificates,
then computes every X degree directly from its mask. It rejects seven of
shape A's 26 positive-definite patterns and six of shape B's 30. Its complete
remaining mask lists are embedded as checked expectations in the verifier.
The only remaining masks with three edges are 26, 28, 50, 52 in shape B;
shape A has none. Thus the fixed psi7 forces |E(X)| <= 2 in shape A and
|E(X)| <= 3 in shape B.

These are necessary constraints only. The remaining 43 masks have not been
shown to extend to graphs, compatible projectors, or the full fixed spectrum.
This does not address the other internal-edge values a=6,7,8.

Run `python3 verify_q7_h7_empty_pair_capacity.py` beside the prior compression
verifier and its JSON. No optimizer or additional graph enumeration is used.
