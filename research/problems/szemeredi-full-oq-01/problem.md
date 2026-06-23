# Problem: Szemerédi Theorem — Furstenberg Ergodic-Theoretic Proof Formalization

**Slug**: szemeredi-full-oq-01
**Created**: 2026-04-23
**Status**: Active (OBSERVE)
**Source**: gallery-gap (szemeredi-full openQuestions[0])
**Tier**: A | **Significance**: 9/10 | **Tractability**: 4/10 (hard)

## Problem Statement

### Formal Statement

Szemerédi's theorem: for all $k \in \mathbb{N}$ and $\delta > 0$, any subset of $\{1, \ldots, N\}$
with at least $\delta N$ elements contains an arithmetic progression of length $k$ (for large enough $N$).

Furstenberg's 1977 proof proceeds via the **Correspondence Principle**: any subset
$A \subseteq \mathbb{Z}$ of positive upper density $\bar{d}(A) > 0$ corresponds to a
measure-preserving system $(X, \mathcal{B}, \mu, T)$. Then $k$-APs in $A$ follow from the
**Multiple Recurrence Theorem**:

$$
\liminf_{N \to \infty} \frac{1}{N} \sum_{n=1}^{N} \mu\!\left(A \cap T^{-n}A \cap T^{-2n}A \cap \cdots \cap T^{-(k-1)n}A\right) > 0
$$

for any measure-preserving system and any measurable $A$ with $\mu(A) > 0$.

### Plain Language

Can we formalize Furstenberg's ergodic-theoretic proof of Szemerédi's theorem in Lean 4?

The existing `szemeredi-full` gallery proof assembles the result via the hypergraph counting
approach. Furstenberg's 1977 proof is fundamentally different: it translates the combinatorial
density statement into a question about recurrence in measure-preserving dynamical systems,
proving the "multiple recurrence theorem" using ergodic theory.

### Why This Matters

1. **Two independent proofs**: An independent machine-checked verification of Szemerédi's theorem.
2. **Bridge between domains**: The Furstenberg Correspondence Principle connects combinatorics
   and ergodic theory — formalizing it in Lean makes this bridge reusable for other results.
3. **Green-Tao path**: The Green-Tao theorem (primes contain long APs) uses Furstenberg-style
   methods; this would be an intermediate step toward that formalization.
4. **Mathlib infrastructure**: Mathlib has significant measure theory and ergodic foundations.

## Known Results

### What's Already Proven

- **Szemerédi's theorem** — formalized in `szemeredi-full` via hypergraph counting approach
- **van der Waerden's theorem** — combinatorial precursor; may be in Mathlib
- Mathlib: `MeasureTheory.Measure`, measure-preserving maps, some ergodic theory

### What's Still Open (in Lean)

- Furstenberg Correspondence Principle
- Furstenberg Multiple Recurrence Theorem
- Connecting the ergodic proof to the existing `szemeredi-full` statement

### Our Goal

Formalize the statement of Furstenberg's Multiple Recurrence Theorem and identify
the key Mathlib gaps:

1. State upper density $\bar{d}(A)$ formally in Lean
2. State the Furstenberg Correspondence Principle in terms of Mathlib's measure theory
3. State the Multiple Recurrence Theorem as a Lean theorem (with sorry proof)
4. Show how these imply Szemerédi's theorem

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `szemeredi-full` | Main theorem formalized via hypergraph approach | Case assembly, axiom reduction |
| `szemeredi-regularity` | Regularity lemma component | Graph theory, epsilon regularity |
| `szemeredi-counting` | Counting lemma component | Hypergraph combinatorics |
| `szemeredi-core` | Core structural results | |

## Initial Thoughts

### Potential Approaches

1. **Statement-level formalization**: State the Multiple Recurrence Theorem cleanly in Lean
   using Mathlib's measure theory, without proving it.
   - Why it might work: Mathlib has measure spaces, measure-preserving maps
   - Risk: Upper density construction may need new definitions

2. **Correspondence Principle first**: Formalize the correspondence between density subsets
   and measure-preserving systems as a standalone result.
   - Why it might work: Clear mathematical content, separable from deep ergodic theory
   - Risk: Compactification and Hahn-Kolmogorov machinery may be missing

3. **Sorry-sketch of full proof**: Write the ergodic proof structure with sorries at hard steps.
   - Why it might work: Demonstrates the proof architecture
   - Risk: Too many sorries may obscure what is actually formalized

### Key Difficulties

- **Upper density**: Defining $\bar{d}(A) = \limsup_{N\to\infty} |A \cap [1,N]| / N$ in Lean
- **Compactification**: The correspondence uses the Bohr compactification of $\mathbb{Z}$ — not in Mathlib
- **Multiple recurrence**: Deep ergodic theory; van der Waerden used as a subresult in one approach
- **Connecting back**: Showing the ergodic conclusion implies density APs requires bookkeeping

### What Would a Proof Need?

- Upper density definition and basic lemmas
- A measure-preserving system on a compact space with shift
- Furstenberg Correspondence Principle (new Mathlib content)
- Multiple recurrence for commuting measure-preserving maps

## Tractability Assessment

**Difficulty**: Hard (4/10)

**Justification**:
- The Furstenberg proof requires graduate-level ergodic theory
- Key components are not in Mathlib (correspondence principle, multiple recurrence)
- A statement formalization (with sorry proofs) is achievable
- A full proof is out of scope for this problem instance

**Estimated Effort**:
- Exploration (OBSERVE): 1-2 days — audit Mathlib coverage for upper density, ergodic machinery
- Feasibility (ORIENT): 1-2 days — identify gaps, pick approach
- Statement formalization (ACT): 3-5 days if tractable

## References

### Papers

- Furstenberg, H. (1977). "Ergodic behavior of diagonal measures and a theorem of Szemerédi on arithmetic progressions." *Journal d'Analyse Mathématique* 31:204–256.
- Furstenberg, H., Katznelson, Y., Ornstein, D. (1982). "The ergodic theoretical proof of Szemerédi's theorem." *Bulletin of the AMS* 7(3):527–552.
- Tao, T. (2006). "A quantitative ergodic theory proof of Szemerédi's theorem." arXiv:math/0405251.

### Mathlib Modules

- `Mathlib.MeasureTheory.Measure.MeasureSpace` — measure spaces
- `Mathlib.MeasureTheory.MeasurePreservingEquiv` — measure-preserving maps
- `Mathlib.Dynamics.Ergodic` — ergodic theory (check actual module path)
- `Mathlib.Order.LiminfLimsup` — liminf/limsup machinery for upper density

## Metadata

```yaml
tags:
  - ergodic-theory
  - combinatorics
  - szemeredi
  - furstenberg
  - measure-theory
  - arithmetic-progressions
related_proofs:
  - szemeredi-full
  - szemeredi-regularity
  - szemeredi-counting
  - szemeredi-core
difficulty: hard
tractability: 4
significance: 9
tier: A
source: gallery-gap
created: 2026-04-23
```
