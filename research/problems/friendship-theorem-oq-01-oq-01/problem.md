# Problem: Friendship theorem — does the integrality step generalize to strongly regular graphs?

## Statement

### Plain Language
The spectral proof of the Friendship Theorem reduces to one number-theoretic
fact: a `k`-regular friendship graph satisfies `A² = (k−1)I + J`, and an
elementary "polynomial + UFD" argument forces `k − 1` to be a perfect square.
The parent entry (friendship-theorem-oq-01) asks whether this integrality
argument generalizes beyond friendship graphs. The natural target is the class
of **strongly regular graphs (SRGs)**, whose adjacency matrix satisfies the
quadratic `A² = (k−μ)I + μJ + (λ−μ)A`. We prove the classical Bose /
Cameron–Van Lint **integrality dichotomy** that the eigenvalue multiplicities
force, and recover the friendship step as the `λ = μ = 1` special case.

### Formal Statement
$$
\begin{aligned}
&\text{Given SRG data } (n,k,\lambda,\mu),\ \text{restricted eigenvalues } r,s
   \text{ with } r+s=\lambda-\mu,\ rs=-(k-\mu),\\
&\text{multiplicities } f,g\ge 0 \text{ with } f+g=n-1 \text{ and }
   k+fr+gs=0:\\
&\quad \text{IsSquare}\big((\lambda-\mu)^2+4(k-\mu)\big)
   \ \lor\ \big(f=g \ \land\ 2k+(n-1)(\lambda-\mu)=0\big).
\end{aligned}
$$

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - graph-theory
  - spectral-theory
  - strongly-regular-graphs
  - number-theory
  - friendship-theorem
  - seeker-selected
```

**Significance**: 7/10
**Tractability**: 6/10

## Why This Matters

1. **Research value** — Affirmatively answers the parent entry's open question:
   the elementary integrality argument behind `k − 1 = ⬚` is not special to
   friendship graphs but is the `λ = μ = 1` slice of the general SRG integrality
   dichotomy. The integrality content is verified with zero axioms; only the
   spectral input (existence of restricted eigenvalues with integer
   multiplicities) is taken as hypothesis, since Mathlib lacks the spectral
   decomposition of a general symmetric integer matrix.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| friendship-theorem-oq-01 | Parent: the spectral / characteristic-polynomial friendship proof whose open question this answers |
| friendship-theorem | Root: the finite Friendship Theorem (Erdős–Rényi–Sós 1966) |
| friendship-theorem-oq-04 | Sibling: isolates the covering/regularity half of the same spectral proof for the infinite case |
