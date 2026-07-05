# Problem: Unconditional codimension-m orthogonal compression corollary

## Statement

### Plain Language
SEEKER-SELECTED: Discharge the Rayleigh-agreement hypothesis for the codimension-m orthogonal compression (the projection-adjoint identity holds for any subspace), yielding an unconditional codimension-m interlacing corollary.

### Formal Statement

Let $A$ be a self-adjoint (Hermitian) operator on a finite-dimensional real or
complex inner product space $V$, and let $W \subseteq V$ be **any** subspace of
codimension $m$, with orthogonal projection $P_W$. Let $B = P_W\, A\, P_W|_W$ be
the compression of $A$ to $W$. Writing eigenvalues in decreasing order
$\lambda_1 \ge \lambda_2 \ge \dots$, the eigenvalues interlace unconditionally:

$$
\lambda_{k+m}(A) \;\le\; \lambda_k(B) \;\le\; \lambda_k(A),
\qquad 1 \le k \le \dim W .
$$

The point of this OQ is that the **Rayleigh-agreement (projection–adjoint) identity**
$\langle P_W A P_W\, v,\, v\rangle = \langle A v, v\rangle$ for all $v \in W$ holds for
*every* subspace $W$ — no invariance or special-position hypothesis is required — so the
codimension-$m$ interlacing corollary follows unconditionally from the min–max
characterization of eigenvalues.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - linear-algebra
  - spectral-theory
  - research
  - seeker-selected
```

**Significance**: 6/10
**Tractability**: 7/10

## Why This Matters

1. **Research value** - SEEKER-SELECTED: Discharge the Rayleigh-agreement hypothesis for the codimension-m orthogonal compression (the projection-adjoint identity holds for any subspace), yielding an unconditional codimension-m interlacing corollary

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
