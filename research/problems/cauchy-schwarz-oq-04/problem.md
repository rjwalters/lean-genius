# Problem: Cauchy-Schwarz Equality Condition Strengthening

**Slug**: cauchy-schwarz-oq-04
**Created**: 2026-03-14
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\langle u, v \rangle = \|u\| \cdot \|v\| \implies u = \frac{\langle u, v \rangle}{\|v\|^2} \cdot v
$$

More precisely: in a real inner product space, when the Cauchy-Schwarz equality holds (i.e., $u$ and $v$ are linearly dependent), the proportionality constant $c$ such that $u = c \cdot v$ is exactly $c = \frac{\langle u, v \rangle}{\|v\|^2}$.

### Plain Language

The Cauchy-Schwarz inequality states $|\langle u, v \rangle| \leq \|u\| \cdot \|v\|$, with equality iff $u$ and $v$ are proportional. This problem asks us to formalize the *exact* proportionality constant: when equality holds, $u = \frac{\langle u, v \rangle}{\|v\|^2} v$.

### Why This Matters

The equality condition with explicit constant is fundamental in:
- Projection operators and orthogonal decomposition
- Gram-Schmidt process (the projection coefficient is exactly this constant)
- Best approximation in Hilbert spaces
- Signal processing (correlation coefficients)

## Known Results

### What's Already Proven

- Cauchy-Schwarz inequality in `cauchy-schwarz` gallery proof
- `inner_mul_le_norm_mul_norm` in Mathlib
- Linear dependence characterization from equality case

### What's Still Open

- Explicit proportionality constant formalization in Lean 4
- Connection to orthogonal projection formula

### Our Goal

Formalize in Lean 4 that when Cauchy-Schwarz equality holds for nonzero $v$, the vector $u$ equals $\frac{\langle u, v \rangle}{\|v\|^2} \cdot v$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-schwarz | Parent proof, establishes the inequality and equality condition | Inner product axioms, norm properties |
| cauchy-schwarz-oq-01 | Complex inner product space extension | Inner product generalization |
| cauchy-schwarz-oq-03 | Hölder's inequality generalization | Lp spaces |

## Initial Thoughts

### Potential Approaches

1. **Direct from Mathlib inner product space API**
   - Why it might work: Mathlib has `InnerProductSpace` with projection lemmas
   - Risk: May need to navigate between different norm/inner product APIs

2. **From linear dependence characterization**
   - Why it might work: If equality holds, vectors are linearly dependent, so $u = cv$ for some $c$. Then $\langle cv, v \rangle = c\|v\|^2$ gives $c = \langle u,v \rangle / \|v\|^2$.
   - Risk: Linear dependence may give $v = cu$ instead of $u = cv$

### Key Difficulties

- Handling the $v \neq 0$ condition
- Navigating Mathlib's inner product space hierarchy
- Real vs complex inner product subtleties

### What Would a Proof Need?

- Key lemma: equality in C-S implies linear dependence
- Key lemma: inner product bilinearity to extract the constant
- Technical: `InnerProductSpace` instance, division by `‖v‖²`

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- This is a standard textbook result with a short proof
- Mathlib has extensive inner product space support
- The proof strategy is clear: equality → proportionality → compute constant
- Similar algebraic manipulations appear in existing gallery proofs

**Estimated Effort**:
- Exploration: 1-2 hours
- Formalization: 1-2 days

## References

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product space definitions and Cauchy-Schwarz
- `inner_mul_le_norm_mul_norm` — the inequality itself
- `norm_inner_eq_norm` related lemmas — equality conditions

## Metadata

```yaml
tags:
  - analysis
  - inner-product-spaces
  - cauchy-schwarz
  - extension
related_proofs:
  - cauchy-schwarz
  - cauchy-schwarz-oq-01
  - cauchy-schwarz-oq-03
difficulty: low
source: proof-suggestion
created: 2026-03-14
```

**Significance**: 5/10
**Tractability**: 7/10
