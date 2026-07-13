# Problem: Erdős Probabilistic Lower Bound for R(4,k)

**Slug**: ramsey-r4k-extensions-oq-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
R(4, k) \geq c \cdot \frac{k^2}{\log k}
$$

for some absolute constant $c > 0$, where $R(4,k)$ is the Ramsey number (smallest $n$ such that every 2-coloring of $K_n$ contains a red $K_4$ or a blue $K_k$).

The proof uses the probabilistic method: color edges of $K_n$ uniformly at random, and compute the expected number of monochromatic $K_4$ or $K_k$ subgraphs.

### Plain Language

The gallery has formalized the upper bound side of R(4,k). This problem asks to formalize the **lower bound** using Erdős's probabilistic argument:

1. Choose $n \approx c \cdot k^2/\log k$
2. Color each edge of $K_n$ red with probability $p = (k \log k / n)^{1/3}$ independently
3. Compute $\mathbb{E}[\text{# red } K_4] + \mathbb{E}[\text{# blue } K_k]$
4. Show this expectation is $< 1$, so there exists a coloring avoiding both

The formalization requires: uniform random graph model in Lean, expectation computation, and the probabilistic argument.

### Why This Matters

- The lower bound $R(4,k) \geq ck^2/\log k$ matches the upper bound up to $k$ (the gap is $[k^2/\log k, k^3/\log k]$)
- Demonstrates the probabilistic method applied to Ramsey theory
- One of the cleanest examples of Erdős's probabilistic combinatorics technique
- Connects to `ramsey-r4k-extensions-oq-03` (Lovász Local Lemma approach)

## Known Results

### What's Already Proven

- Gallery: R(4,k) upper bound formalization (ramsey-r4k-extensions)
- Mathlib: `MeasureTheory.probability_eq`, basic probability measure infrastructure
- Mathlib: `Finset.card_choose` for counting subgraph choices

### What's Still Open

- Formal probability model for uniform random edge coloring in Lean 4
- Expectation computation for $\binom{n}{4}$ monochromatic $K_4$s
- The probabilistic existence argument (if $\mathbb{E}[X] < 1$ then $\Pr[X = 0] > 0$)

### Our Goal

Formalize: `theorem erdos_probabilistic_lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ k, ∃ n, n ≥ c * k^2 / Real.log k ∧ ¬(∃ coloring : complete_graph n → Bool, ...)` 

(or an equivalent statement using a concrete achievability witness)

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ramsey-r4k-extensions | Direct predecessor | R(4,k) upper bound |
| ramseys-theorem | Base result | R(r,s) exists |
| prob-method-lovasz-local | Key tool | LLL for Ramsey bounds |
| prob-method-expectation | Method | First moment method |

## Initial Thoughts

### Potential Approaches

1. **First moment method (expectation argument)**
   - For $n = \lfloor c \cdot k^2 / \log k \rfloor$, color each edge red with prob $p = (k \log k / n)^{1/3}$
   - $\mathbb{E}[\text{red } K_4] = \binom{n}{4} p^6 \leq \binom{n}{4} \cdot (k \log k / n)^2$
   - For appropriate $c$, this sum is $< 1/2$
   - Similarly for blue $K_k$: $\mathbb{E}[\text{blue } K_k] = \binom{n}{k}(1-p)^{\binom{k}{2}} < 1/2$
   - By union bound + first moment, exists a good coloring
   - Why it might work: standard technique
   - Risk: setting up probability spaces in Lean is non-trivial

2. **Concrete constructive approach**
   - Use a pseudorandom construction instead of probabilistic argument
   - Paley graphs give Ramsey lower bounds deterministically
   - Why it might work: avoids measure theory in Lean
   - Risk: requires algebraic combinatorics (quadratic residues, finite fields)

### Key Difficulties

- **Probability model**: Setting up `PMF (Fin 2 → Finset.univ (CompleteGraph n).edgeSet)` or similar
- **Expectation computation**: $\mathbb{E}[\binom{n}{4} p^6]$ requires combinatorial counting in Lean
- **Clique avoidance**: Connecting "low expectation" to "positive probability" (Markov's inequality)

### What Would a Proof Need?

- `MeasureTheory.Measure.pi` for product probability measures on edges
- `MeasureTheory.integral_fintype` for computing expectations
- `Finset.card_powersetLen` for counting monochromatic cliques
- `NNReal.Finset.sum_le_card_nsmul` for bounding expectations

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Setting up the formal probability model for random graph is the main hurdle
- Mathlib's probability infrastructure exists but is complex
- The expectation computation is routine math but verbose Lean
- This is a challenging formalization even for experienced Lean users
- Marked as tractable but likely requires significant exploration time

**Estimated Effort**:
- Exploration: 3-5 hours (finding right Mathlib infrastructure)
- Implementation: 1-2 weeks if probabilistic approach
- Alternatively: Paley graph construction might be faster (2-3 days)

## References

### Papers
- Erdős, P. (1947). "Some remarks on the theory of graphs" — first use of probabilistic method for Ramsey
- Spencer, J. (1994). "Ten Lectures on the Probabilistic Method" — comprehensive treatment

### Mathlib
- `Mathlib.Probability.ProbabilityMassFunction.Basic` — PMF infrastructure
- `Mathlib.Probability.Independence.Basic` — independent events
- `Mathlib.Combinatorics.SimpleGraph.Clique` — graph cliques

## Metadata

```yaml
tags:
  - ramsey-theory
  - combinatorics
  - probabilistic-method
  - first-moment-method
  - seeker-selected
related_proofs:
  - ramsey-r4k-extensions
  - ramseys-theorem
  - prob-method-expectation
difficulty: high
source: gallery-gap
created: 2026-04-21
```
