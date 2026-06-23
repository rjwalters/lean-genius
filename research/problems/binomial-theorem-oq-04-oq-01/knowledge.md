# binomial-theorem-oq-04-oq-01: Combinatorial Vandermonde via Explicit Bijection

## Problem Summary

**Open Question**: Can Vandermonde's identity C(m+n,r) = Σ C(m,k)·C(n,r-k) be proved
combinatorially via an explicit bijection on Finsets, rather than through the algebraic
Nat.add_choose_eq route?

**Answer**: YES. Proved via explicit split-merge bijection.

**Status**: COMPLETED - 299 lines, 0 sorries, 0 axioms.

## Session 2026-03-18 - Full Proof

**Mode**: FRESH
**Outcome**: completed

### Approach: Split-Merge Bijection

The key idea: partition r-element subsets of {0,...,m+n-1} by how many elements
fall below threshold m.

**Forward map (split)**: S ↦ (lowPart m S, highPart m S)
- lowPart: S ∩ {0,...,m-1}
- highPart: (S ∩ {m,...,m+n-1}).image (· - m)

**Inverse map (merge)**: (A, B) ↦ A ∪ B.image (· + m)

**Main proof structure**:
1. Show split and merge are inverses (round-trip properties)
2. Define `fiber m n r k` = {S ∈ powersetCard r (range (m+n)) | |lowPart m S| = k}
3. Show fibers are pairwise disjoint and cover all of powersetCard
4. Show each fiber has size C(m,k)·C(n,r-k) via card_bij
5. Sum via card_biUnion to get Vandermonde

### Lean 4 Technical Notes

- `omega` cannot beta-reduce `(fun x => x - m) a` to `a - m`; need explicit coercion
- `card_biUnion` expects `PairwiseDisjoint` (not explicit ∀∀∀ quantifiers)
- Use `card_image_of_injOn` for subtraction (not globally injective)
- Use `biUnion + card_biUnion` instead of `sum_card_fiberwise` (may not exist)

### Files Created

- `proofs/Proofs/BinomialTheoremOQ04OQ01.lean` (299 lines, 0 sorries, 0 axioms)

## Approaches Explored

### Split-Merge Bijection
**Status**: successful
Split r-subsets of {0,...,m+n-1} at threshold m into low/high parts, use card_bij for fiber bijection
**Outcome**: Complete proof with 0 sorries
