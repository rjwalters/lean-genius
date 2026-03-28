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

### Session 2 (2026-03-28, researcher-2)
**Decision**: DEEP DIVE
**Outcome**: COMPLETED

Fixed critical mathematical bug and added new theorems:
- **Bug**: `erdos1183_f` and `erdos1183_F` used `sInf` on a downward-closed set, giving 0.
  The correct definition uses `sSup` (supremum = largest achievable bound).
- **Fix**: Defined `achievableSublattice` and `achievableUnionClosed` as the achievable
  lower-bound sets, proved both are `BddAbove` (bounded by 2^n), and used `sSup`.
- **New theorem**: `erdos1183_f_lower_bound` — f(n) ≥ ⌈(n+1)/2⌉ via `le_csSup`,
  formally connecting the chain bound (Part V) to the abstract definition.
- **New theorem**: `erdos1183_F_ge_f` — F(n) ≥ f(n) via `csSup_le_csSup`,
  since sublattices are union-closed.
- Added import `Mathlib.Order.ConditionallyCompleteLattice.Basic` for sSup/le_csSup.
- File: 223 → 277 lines, 10 → 15 theorems, 10 → 12 definitions.

**Key Insight**: The set `{k | ∀ χ, ∃ F mono sublattice, F.card ≥ k}` is downward-closed
in ℕ, so `sInf` gives 0 (minimum). The correct definition takes `sSup` (maximum).
`ℕ` is a `ConditionallyCompleteLinearOrderBot`, so `le_csSup` and `csSup_le_csSup`
work for bounded nonempty sets.

---

*Generated from erdosproblems.com on 2026-01-16, updated 2026-03-28*
