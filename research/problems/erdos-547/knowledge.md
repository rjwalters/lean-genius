# Erdős #547 - Knowledge Base

## Problem Statement

If T is a tree on n vertices then R(T) ≤ 2n - 2, where R(T) is the 2-color Ramsey number of T.

## Status

**Erdős Database Status**: SOLVED (for large n)
**Tractability Score**: 6/10
**Aristotle Suitable**: Yes (known proof to formalize)

## Key Definitions Built

| Name | Type | Description | Location |
|------|------|-------------|----------|
| EdgeColoring | def | 2-coloring of edges of K_n | Erdos547Problem.lean:32 |
| HasMonochromaticCopy | def | K_n contains monochromatic copy of G | Erdos547Problem.lean:37 |
| ramseyNumber | def | R(G) = min n s.t. any 2-coloring has mono copy | Erdos547Problem.lean:49 |
| maxDegree | def | Maximum degree of a graph | Erdos547Problem.lean:67 |
| IsPath | def | Tree with max degree 2 | Erdos547Problem.lean:82 |
| IsStar | def | Tree with central vertex | Erdos547Problem.lean:86 |

## Key Results Built

| Name | Status | Description |
|------|--------|-------------|
| exists_ramsey_number | AXIOM | Ramsey's theorem for graphs |
| tree_ramsey_bound | SORRY | Main: R(T) ≤ 2n - 2 |
| chvatal_bound | SORRY | Chvátal: R(T) ≤ (Δ-1)(n-1) + 1 |
| path_ramsey | AXIOM | R(P_n) = n |
| star_ramsey | AXIOM | R(S_n) = 2n - 2 |
| bound_is_tight | SORRY | Stars achieve the bound |

## Insights

1. **Mathlib Integration**: SimpleGraph.IsTree is available in Mathlib with IsTree.card_edgeFinset
2. **Ramsey Infrastructure Gap**: Mathlib has van der Waerden/Hales-Jewett but NOT graph Ramsey numbers
3. **Edge Coloring Model**: We represent edge colorings as Sym2 (Fin n) → Bool
4. **Classical Decidability**: ramseyNumber requires Classical.decPred for Nat.find

## Mathlib Gaps

- No graph Ramsey number infrastructure
- No edge coloring Ramsey theory (only vertex coloring in SimpleGraph.Coloring)
- Would need ~300-500 lines to build proper Ramsey infrastructure

## Next Steps

1. Submit tree_ramsey_bound to Aristotle (HARD sorry - known proof exists)
2. chvatal_bound could be proved from embedding lemma + induction
3. bound_is_tight needs explicit star construction on Fin n

## Tags

- erdos
- ramsey-theory
- trees
- graph-coloring

## Related Problems

- Erdős #549, #550 (other tree problems)
- Erdős #64 (tree embeddings)

## References

- Chvátal, V. (1977): Tree-complete graph Ramsey numbers
- Zhao et al.: Resolution for large n
- Burr, S.: Survey of tree Ramsey numbers

## Sessions

### Session 2026-01-15 (Session 1) - Infrastructure Setup

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Scouted Mathlib for tree/Ramsey infrastructure
- Found SimpleGraph.IsTree in Mathlib/Combinatorics/SimpleGraph/Acyclic
- Refactored file to use Mathlib's IsTree directly
- Fixed type class issues (DecidableRel, Fintype instances)
- Used Classical.decPred for ramseyNumber definition
- Reduced sorries from 5 to 3

### Key Findings
- Mathlib has tree infrastructure (IsTree, IsAcyclic, card_edgeFinset)
- Mathlib LACKS graph Ramsey number theory
- Edge colorings need custom definition (Sym2 → Bool)

### Files Modified
- proofs/Proofs/Erdos547Problem.lean (major refactor)

### Next Steps
- Submit remaining HARD sorries to Aristotle
- Consider building minimal Ramsey infrastructure (~300 lines)

---

*Generated on 2026-01-15*
