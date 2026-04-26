# Problem: Generalize BSC Capacity Proof to Symmetric Channels

**Slug**: shannon-channel-coding-oq-02-oq-04
**Created**: 2026-04-23T01:33:17+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a symmetric discrete memoryless channel (DMC) with input alphabet 𝒳, output alphabet
𝒴, transition probabilities p(y|x), define the capacity:

$$
C = \max_{p(x)} I(X; Y) = \log |\mathcal{X}| - H(Y|X)
$$

where for a symmetric channel the maximizing distribution is uniform over 𝒳, giving:

$$
C_{\text{symmetric}} = \log |\mathcal{X}| + \sum_{y \in \mathcal{Y}} p(y|x_0) \log p(y|x_0)
$$

**Goal**: Formalize in Lean 4 that the capacity of any symmetric channel is achieved by
the uniform input distribution, generalizing the existing BSC capacity placeholder proof.

### Plain Language

The existing `shannon-channel-coding` gallery proof contains a `sorry`-backed placeholder
for BSC (Binary Symmetric Channel) capacity. The BSC is a special case of symmetric
channels. This problem asks to prove the general result: for symmetric channels, the
uniform input distribution maximizes mutual information, giving a clean closed-form for
capacity. This is more general than BSC and covers a wide class of practical channels.

### Why This Matters

1. **Generalizes existing gallery work**: Moves the placeholder from `True` to an actual
   verified capacity formula for the entire class of symmetric channels.

2. **Core information theory**: The symmetry argument is the key technique that makes
   BSC/BEC/Z-channel capacities computable — formalizing it unlocks a family of results.

3. **Mathlib connection**: Requires `MeasureTheory.entropy`, `Finset.sum`, and mutual
   information formalizations that are increasingly available in Mathlib4.

## Known Results

### What's Already Proven

- `shannon-channel-coding`: General noisy channel coding theorem (with sorries in capacity computation)
- `shannon-entropy`: Entropy function formalized in gallery
- BSC capacity C = 1 - H(p) where H is binary entropy (placeholder `True` in gallery)

### What's Still Open

- Formal statement that uniform distribution maximizes I(X;Y) for symmetric channels
- Closed-form capacity formula C = log|𝒳| - H(Y|X) for symmetric channels
- Connecting to Mathlib4 probability/entropy machinery

### Our Goal

Prove the symmetric channel capacity theorem: if p(y|x) is a symmetric channel matrix
(each row a permutation of every other row, each column having the same set of values),
then the uniform distribution achieves capacity and C = log|𝒳| + Σ_y p(y|x₀) log p(y|x₀).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `shannon-channel-coding` | Direct parent — contains the BSC placeholder | Channel coding theorem |
| `shannon-entropy` | Entropy function definition and properties | Shannon entropy |
| `shannon-source-coding` | Sister proof on source coding | AEP, entropy |

## Initial Thoughts

### Potential Approaches

1. **Direct symmetry argument**: Show that for symmetric channels, I(X;Y) is concave
   in p(X) and the uniform distribution is the unique maximizer by symmetry.
   - Why it might work: Standard textbook argument (Cover & Thomas Ch. 7)
   - Risk: Formalizing "symmetry" of a channel in Lean requires careful type design

2. **Convexity + Lagrange multipliers**: Use that mutual information is concave in p(X)
   for fixed channel, then apply KKT conditions at uniform distribution.
   - Why it might work: Mathlib has convexity tools
   - Risk: Lagrange/KKT in Lean is not well-established

3. **Direct computation**: For specific symmetric channels (BSC, BEC), just compute
   I(X;Y) under uniform p(X) and show it equals the claimed formula.
   - Why it might work: Avoids abstract symmetry, more tractable
   - Risk: Only proves special cases, not the general theorem

### Key Difficulties

- Defining "symmetric channel" formally in Lean (not a standard Mathlib type)
- Mathlib4 mutual information API (may need `MeasureTheory.Measure.entropy`)
- Sum over output alphabet when Y is a `Fintype`

### What Would a Proof Need?

- Lean definition of symmetric DMC as a `Matrix 𝒳 𝒴 ℝ` with symmetry conditions
- Mutual information I(X;Y) as a function of `p : ProbabilityMeasure 𝒳`
- Concavity of I(X;Y) in p(X) for fixed channel (or direct symmetry argument)
- The closed-form H(Y|X) = H(Y|X=x₀) for any fixed x₀ in a symmetric channel

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is textbook-level (Cover & Thomas Theorem 7.2.1)
- Mathlib4 has entropy and fintype probability tools, but mutual information API may be incomplete
- Start with Approach 3 (specific channels) to get partial results, then generalize
- The hardest part is the Lean API for mutual information — may need to build it

**Estimated Effort**:
- Exploration: 1-2 days (check Mathlib4 mutual information support)
- If tractable: 1-2 weeks (formalize symmetric channel type and capacity theorem)
- If hard: Partial result for BSC only is still valuable

## References

### Papers
- Cover & Thomas, "Elements of Information Theory" Ch. 7 — symmetric channel capacity
- Shannon (1948), "A Mathematical Theory of Communication" — original channel capacity

### Mathlib
- `Mathlib.MeasureTheory.Measure.MeasureSpace` — probability measures
- `Mathlib.Analysis.InnerProductSpace.Basic` — convexity tools
- Search for `entropy` in Mathlib4 for current state of information theory formalization

## Metadata

```yaml
tags:
  - information-theory
  - channel-capacity
  - bsc
  - symmetric-channels
  - entropy
related_proofs:
  - shannon-channel-coding
  - shannon-entropy
  - shannon-source-coding
difficulty: medium
source: gallery-gap
created: 2026-04-23T01:33:17+02:00
```

**Significance**: 7/10
**Tractability**: 6/10
