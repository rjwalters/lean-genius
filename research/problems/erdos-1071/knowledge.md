# Erdős #1071 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Are there a finite set of unit line segments in the unit square, no two of which intersect, which are maximal with respect to this property?

Is there a region $R$ with a maximal set of disjoint unit line segments that is countably infinite?



A question of Erd\H{o}s and T\'{o}th. The answer to the first question is yes (which Erd\H{o}s gave \$10 for).

There are two examples Erd\H{o}s gives in \cite{Er87b}, the {IMAGE=1071-one,first} by Danzer, the {IMAGE=1071-two,second} by an unnamed participant.




References


[Er87b] Erd\H{o}s, P., Some combinatorial and metric problems in geometry. Intuitive geometry (Si\'{o}fok, 1985) (1987), 167-177.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #1070
- Problem #1072
- Problem #2
- Problem #39
- Problem #1

## References

- Er87b

## Sessions

---

## Session 2026-04-21 (Session 1) — Zorn Existence + Danzer Axiom

**Mode**: FRESH
**Outcome**: progress
**Phase**: ACT (was ACT)

### What I Did

- Added `IsExtendable` predicate: a packing is extendable if a new unit segment can be added
- Proved `maximal_iff_not_extendable`: MaximalPacking ↔ ¬IsExtendable (clean characterization)
- Proved `packing_chain_union`: union of any chain of packings is itself a packing (key Zorn lemma)
- Proved `exists_maximal_packing` via Zorn's lemma: every bounded-region packing can be extended to a maximal one
- Added `danzer_finite_maximal_packing` axiom: Danzer's $10-prize result that a FINITE maximal packing exists

### Key Findings

- The Zorn argument is clean: packings ordered by ⊆ satisfy the chain condition (packing_chain_union); Zorn gives a maximal element m. If s ∉ m were disjoint from all of m, insert s m would be a larger packing, contradicting Zorn maximality. Hence some element of m blocks s.
- `packing_chain_union` handles chain comparability: for T, U ∈ chain with T ≠ U, either T ⊆ U or U ⊆ T; disjointness of s ∈ T and t ∈ U follows from disjointness within the bigger set.
- `exists_maximal_packing` is strictly weaker than `danzer_finite_maximal_packing`: Zorn gives existence of *some* maximal packing; Danzer shows a FINITE one exists. The finiteness is the hard geometric content.
- All proofs close: 0 sorries, 1 axiom (Danzer), 23 theorems total.

### Files Modified

- `proofs/Proofs/Erdos1071Problem.lean` (253 → 323 lines)
- `src/data/proofs/erdos-1071/meta.json` (axiomCount 0→1, badge wip→axiom)
- `src/data/research/problems/erdos-1071.json` (knowledge updated)

### Next Steps

- Area/compactness argument: prove formally that [0,1]² admits only finitely many disjoint unit segments (this would verify Danzer's finiteness claim from first principles rather than axiom)
- The core open problem (part b: countably infinite maximal packing in some region) remains open; no Aristotle help applicable

---

*Generated from erdosproblems.com on 2026-01-15*
