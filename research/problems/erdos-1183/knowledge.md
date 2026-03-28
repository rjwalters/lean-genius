# Erdős #1183 - Knowledge Base

## Problem Statement

Let f(n) be maximal such that in any 2-coloring of the subsets of {1,...,n}
there is always a monochromatic family of at least f(n) sets closed under
taking unions and intersections. Estimate f(n).

Let F(n) be defined similarly requiring only union-closure. Is F(n) ≥ n^{ω(n)}
for some ω(n) → ∞, and F(n) < (1+o(1))^n?

A problem of Erdős and Ulam [Er78, p.39].

## Status

**Erdős Database Status**: OPEN
**Tags**: combinatorics, ramsey theory

**Tractability Score**: 6/10
**Aristotle Suitable**: No (open problem)

## Known Results

- f(n) ≥ ⌈(n+1)/2⌉ (trivial chain bound, proved in our formalization)
- Howorka: F(n) > n^{ω(n)} for same-size colorings (no reference given in [Er78])
- Erdős: "we have no plausible conjecture for the true order of magnitude of f(n)"

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #2
- Problem #39
- Problem #1

## References

- [Er78] P. Erdős, Proc. Ninth Southeastern Conf. on Combinatorics, 1978, p.39

## Sessions

### Session 1 (2026-03-28, researcher-4)
**Decision**: DEEP DIVE
**Outcome**: COMPLETED

Built complete formalization:
- `proofs/Proofs/Erdos1183Problem.lean` (223 lines)
- Defined: SubsetColoring, IsUnionClosed, IsInterClosed, IsSublattice, IsChain
- Proved: chains are sublattices, standard chain has n+1 elements
- Main result: `erdos1183_chain_bound` — f(n) ≥ ⌈(n+1)/2⌉
- 10 theorems, 10 definitions, 2 axioms (open questions), 0 sorries

**Key Insight**: The trivial bound comes from the maximal chain
∅ ⊂ {0} ⊂ {0,1} ⊂ ... ⊂ {0,...,n-1} which has n+1 elements.
By pigeonhole, ⌈(n+1)/2⌉ share a color. Any subchain is a sublattice.

---

*Generated from erdosproblems.com on 2026-01-16, updated 2026-03-28*
