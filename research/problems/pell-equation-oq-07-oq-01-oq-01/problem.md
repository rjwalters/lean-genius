# Problem: Prove the Cassini/Catalan-type identity xₙ₋₁xₙ₊₁ − xₙ² = (constant)·(N(a))ⁿ f...

## Statement

### Plain Language
AVAILABLE — Prove the Cassini/Catalan-type identity xₙ₋₁xₙ₊₁ − xₙ² = (constant)·(N(a))ⁿ from det(Mⁿ) = (det M)ⁿ = N(a)ⁿ, deriving the determinant identity directly from the companion-matrix closed form.

### Formal Statement
For a quadratic integer $a = p + q\sqrt d \in \mathbb{Z}[\sqrt d]$ with norm $N(a) = p^2 - d q^2$, let $M = \begin{pmatrix} p & d q \\ q & p \end{pmatrix}$ be its companion (multiplication) matrix, so $\det M = N(a)$. The second-order sequence $(x_n)$ defined by $x_{n+1} = 2p\,x_n - N(a)\,x_{n-1}$ (the real part of $a^n = x_n + y_n\sqrt d$) satisfies the Cassini/Catalan-type identity
$$
x_{n-1}\,x_{n+1} - x_n^2 = \bigl(x_0 x_2 - x_1^2\bigr)\, N(a)^{\,n-1} \qquad (n \ge 1),
$$
which is obtained directly from $\det(M^n) = (\det M)^n = N(a)^n$.

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - number-theory
  - diophantine-equations
  - pell-equation
  - quadratic-integers
  - zsqrtd
  - binet-formula
  - closed-form
  - companion-matrix
  - characteristic-polynomial
  - conjugation
  - seeker-selected
```

**Significance**: 7/10
**Tractability**: 6/10

## Why This Matters

1. **Research value** - AVAILABLE — Prove the Cassini/Catalan-type identity xₙ₋₁xₙ₊₁ − xₙ² = (constant)·(N(a))ⁿ from det(Mⁿ) = (det M)ⁿ = N(a)ⁿ, deriving the determinant identity directly from the companion-matrix closed form

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
