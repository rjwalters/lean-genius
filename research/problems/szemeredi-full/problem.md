# Problem: Szemeredi's Theorem (Full)

**Slug**: szemeredi-full
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Szemeredi Regularity and Applications (Phase 3)

## Problem Statement

### Formal Statement

For every integer $k \geq 3$ and every $\delta > 0$, there exists $N_0 = N_0(k, \delta)$ such that every subset $A \subseteq [N]$ with $|A| \geq \delta N$ and $N \geq N_0$ contains a $k$-term arithmetic progression.

Equivalently: every subset of the natural numbers with positive upper density contains arbitrarily long arithmetic progressions.

### Plain Language

Szemeredi's theorem says that any "dense" subset of the integers -- one that takes up a positive fraction of {1, 2, ..., N} for all large N -- must contain arithmetic progressions of every length. You cannot avoid long evenly-spaced patterns in a dense set, no matter how cleverly you construct it. This is one of the deepest and most celebrated results in all of combinatorics.

### Why This Matters

Szemeredi's theorem (1975) is a landmark of 20th century mathematics. It resolved a conjecture of Erdos and Turan from 1936 and has inspired entire fields: the Furstenberg ergodic theory approach (1977), Gowers' higher-order Fourier analysis (2001), and the Green-Tao theorem on primes in arithmetic progression (2004). Formalizing it would be a genuine milestone for the Lean community.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Depends on** | szemeredi-regularity | Regularity provides the structural decomposition |
| **Depends on** | szemeredi-counting | Counting/removal lemma bridges to arithmetic structure |
| **Depends on** | roth-theorem-k3 | Roth's theorem is the k=3 base case |

## Known Results

### What's Already in Mathlib

- `Finset` arithmetic operations
- `ArithmeticProgression` type (if it exists) or `Finset.range` constructions
- Basic density/cardinality lemmas
- `SimpleGraph` infrastructure (for regularity approach)

### What Needs to Be Built

- k-term AP definition and basic properties
- Upper density for subsets of naturals
- The full Szemeredi theorem (induction on k using regularity + counting)
- Or alternatively: hypergraph regularity approach

### Our Goal

Formalize the full Szemeredi theorem. The original proof uses regularity + counting lemma + induction on k. The k=3 case (Roth) uses Fourier analysis; the general case extends this using the regularity lemma to find structured subsets where the induction can proceed.

## Initial Thoughts

### Potential Approaches

1. **Via regularity lemma (Szemeredi 1975)**
   - Why it might work: Original proof, builds on our regularity infrastructure
   - Risk: The induction on k through regularity is extremely complex

2. **Via hypergraph regularity**
   - Why it might work: More modern approach, cleaner induction
   - Risk: Hypergraph regularity is even harder than graph regularity

3. **Via ergodic theory (Furstenberg 1977)**
   - Why it might work: Fundamentally different, elegant
   - Risk: Requires measure-theoretic ergodic theory infrastructure

4. **Via Gowers uniformity norms (2001)**
   - Why it might work: Best quantitative bounds, modern approach
   - Risk: Requires higher-order Fourier analysis

### Key Difficulties

- The induction on k is the hardest part of any approach
- The regularity approach requires controlling a tower of regularity applications
- Connecting graph-theoretic regularity to arithmetic progressions
- The quantitative bounds are tower-type, which is unavoidable

## Tractability Assessment

**Difficulty**: Extremely Hard
**Tractability**: 3/10
**Significance**: 10/10

**Justification**:
- This is one of the hardest theorems ever formalized in any proof assistant
- No known formalization exists in Lean, Coq, Isabelle, or any other system
- The proof is extremely long and technically demanding by any approach
- Maximum significance: a formalization would be a genuine research contribution

**Estimated Effort**:
- Exploration: 5 days
- Implementation: 20-40 days (depends heavily on infrastructure)

## References

### Papers
- Szemeredi (1975) - "On sets of integers containing no k elements in arithmetic progression"
- Furstenberg (1977) - "Ergodic behavior of diagonal measures and a theorem of Szemeredi"
- Gowers (2001) - "A new proof of Szemeredi's theorem"
- Green & Tao (2008) - "The primes contain arbitrarily long arithmetic progressions"

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic`
- `Mathlib.Combinatorics.Additive.FreimanRuzsa`
- `Mathlib.MeasureTheory.Measure.MeasureSpace`

## Metadata

```yaml
tags:
  - szemeredi
  - combinatorics
  - additive-combinatorics
  - arithmetic-progressions
  - marquee-phase-3
related_proofs:
  - roth-theorem-k3
  - szemeredi-regularity
  - szemeredi-counting
  - prob-method-lovasz-local
difficulty: extremely-hard
source: marquee-initiative
initiative: szemeredi-regularity-phase-3
created: 2026-03-21
```
