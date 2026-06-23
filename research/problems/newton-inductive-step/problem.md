# Problem: Ultra-Log-Concavity of Binomial Coefficients

**Slug**: newton-inductive-step-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap (open question from newton-inductive-step proof)

## Problem Statement

### Formal Statement

$$
\text{For fixed } m \geq 0, \text{ the sequence } a_k = \binom{m}{k}^2 / \binom{m}{0}^2 \text{ is log-concave in } k.
$$

Equivalently: $a_k^2 \geq a_{k-1} \cdot a_{k+1}$ for all valid $k$, where $a_k = \binom{m}{k}^2$.

### Plain Language

Prove that the squared binomial coefficients $\binom{m}{k}^2$ form a log-concave sequence in $k$. This is a stronger property than the ordinary log-concavity of $\binom{m}{k}$ (Newton's inequality), known as "ultra-log-concavity."

### Why This Matters

Ultra-log-concavity is a key structural property of combinatorial sequences. It implies log-concavity and unimodality, and connects to the theory of Polya frequency sequences, total positivity, and the real-rootedness of generating polynomials.

## Known Results

### What's Already Proven

- `newton-inductive-step`: The inductive step for Newton's log-concavity theorem (verified, 0 axioms)
- Log-concavity of binomial coefficients: $\binom{m}{k}^2 \geq \binom{m}{k-1}\binom{m}{k+1}$
- Mathlib has `Nat.choose` and basic binomial coefficient identities

### What's Still Open

- Ultra-log-concavity (squared version) not yet formalized
- Connection to Liggett's theorem (1997) on ultra-log-concavity

### Our Goal

Formalize the ultra-log-concavity inequality for binomial coefficients in Lean 4.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| newton-inductive-step | Direct parent - provides log-concavity infrastructure | Induction, polynomial manipulation |
| amgm-inequality | Inequality techniques | AM-GM, power means |
| binomial-theorem | Binomial coefficient foundations | Nat.choose, combinatorial identities |

## Initial Thoughts

### Potential Approaches

1. **Direct algebraic proof**: Expand $\binom{m}{k}^4 \geq \binom{m}{k-1}^2 \cdot \binom{m}{k+1}^2$ using factorial representations
   - Why it might work: purely algebraic, no deep theory needed
   - Risk: messy factorial arithmetic in Lean

2. **Via injection/combinatorial argument**: Use the FKG inequality or a combinatorial injection
   - Why it might work: elegant and structural
   - Risk: may require infrastructure not in Mathlib

### Key Difficulties

- Factorial arithmetic can be tedious in Lean
- May need careful handling of division in natural numbers

### What Would a Proof Need?

- Key lemma: $\binom{m}{k}/\binom{m}{k-1} = (m-k+1)/k$ is decreasing in $k$
- Technical: This monotonicity squared gives ultra-log-concavity

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The algebraic proof is known and elementary
- Parent proof infrastructure exists (newton-inductive-step)
- Mathlib has binomial coefficient API

**Estimated Effort**:
- Exploration: 1-2 hours
- If tractable: 1-2 days
- If hard: 3-5 days

## References

### Papers
- Liggett, T.M. (1997), "Ultra logconcave sequences and negative dependence"
- Stanley, R. (1989), "Log-concave and unimodal sequences in algebra, combinatorics, and geometry"

### Mathlib
- `Mathlib.Data.Nat.Choose.Basic` — binomial coefficients
- `Mathlib.Data.Nat.Choose.Factorization` — factorial decomposition

## Metadata

```yaml
tags:
  - combinatorics
  - inequalities
  - log-concavity
  - binomial-coefficients
related_proofs:
  - newton-inductive-step
  - binomial-theorem
  - amgm-inequality
difficulty: medium
source: gallery-gap
created: 2026-03-30
```
