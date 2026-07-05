# Problem: Jordan Block Counts from the Generalized-Eigenspace Dimension Tower

**Slug**: cayley-hamilton-minpoly-oq-01-oq-01-oq-02
**Created**: 2026-07-04T00:45:01-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $V$ be a finite-dimensional vector space over an algebraically closed field
$k$, $f : V \to V$ linear, and $\mu$ an eigenvalue. Write
$G_k(\mu) = \ker\big((f - \mu)^{k}\big)$ for the $k$-th generalized eigenspace,
giving the ascending tower

$$
0 = G_0 \subseteq G_1 \subseteq G_2 \subseteq \cdots \subseteq G_\infty(\mu).
$$

Prove that the **number of Jordan blocks of size exactly $j$** for the eigenvalue
$\mu$ is recovered from second differences of the tower dimensions:

$$
\#\{\text{Jordan blocks of size } j \text{ at } \mu\}
= \big(\dim G_j - \dim G_{j-1}\big) - \big(\dim G_{j+1} - \dim G_{j}\big)
= 2\dim G_j - \dim G_{j-1} - \dim G_{j+1}.
$$

Equivalently, the number of blocks of size $\ge j$ is
$\dim G_j - \dim G_{j-1} = \dim\ker(f-\mu)^{j} - \dim\ker(f-\mu)^{j-1}$.

### Plain Language

The parent proof pins down the *multiplicity* $e_\mu$ (the exponent of $(X-\mu)$
in the minimal polynomial, i.e. the largest block). This generalization extracts
the **full Jordan block-size distribution** at $\mu$ purely from the dimensions
of the kernel tower — no explicit Jordan basis required. The key fact is that
each Jordan block of size $s$ contributes exactly one dimension to each of
$G_1, \dots, G_s$ and nothing beyond, so consecutive differences count blocks of
size $\ge j$ and second differences count blocks of size exactly $j$.

### Why This Matters

This is the quantitative heart of the Jordan canonical form: it shows the JCF is
determined (up to permutation) by the rank data $\operatorname{rank}(f-\mu)^k$,
giving a similarity invariant that is computable without constructing a basis.

## Known Results

### What's Already Proven

- Parent proof `cayley-hamilton-minpoly-oq-01-oq-01`: de-axiomatized JCF product
  formula $\text{minpoly} = \prod_\mu (X - \mu)^{e_\mu}$, where $e_\mu$ is the
  stabilization index of the generalized-eigenspace tower.
- Mathlib `Module.End.genEigenspace`, `Module.End.maxGenEigenspace`, and the
  primary-decomposition / generalized-eigenspace API.

### What's Still Open

- The block-count formula (first and second differences) as named theorems.
- Connecting the counts to `Module.End.HasEigenvalue` multiplicities.

### Our Goal

Prove `#blocks of size ≥ j = dim Gⱼ − dim Gⱼ₋₁` and the exact-size second-
difference formula, using the generalized-eigenspace tower already built in the
parent entry.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton-minpoly-oq-01-oq-01 | Direct parent — builds the tower & $e_\mu$ | generalized eigenspaces, minpoly |
| cayley-hamilton-minpoly | Cayley–Hamilton base | annihilating polynomials |
| minpoly-charpoly | minpoly/charpoly relationship | polynomial invariants |

## Initial Thoughts

### Potential Approaches

1. **Nilpotent reduction on each generalized eigenspace**: restrict to
   $G_\infty(\mu)$, where $N = f - \mu$ is nilpotent; the dimensions
   $\dim\ker N^k$ are governed by the partition (block sizes), and second
   differences of $k \mapsto \dim\ker N^k$ recover the conjugate partition.
   - Why it might work: standard partition/Young-diagram combinatorics; matches
     Mathlib's nilpotent API.
   - Risk: formalizing the partition bookkeeping cleanly.

2. **Rank-nullity on the tower**: $\dim G_j - \dim G_{j-1} =
   \dim\ker N^{j} - \dim\ker N^{j-1}$; show this equals the number of blocks of
   size $\ge j$ directly from a Jordan decomposition existence result.
   - Why it might work: reuses existence of JCF (or primary decomposition).
   - Risk: depends how much JCF structure Mathlib exposes vs. must be built.

### Key Difficulties

- Whether to route through an explicit Jordan basis or stay purely dimensional.
- Mathlib coverage of the full JCF (block structure) vs. just generalized
  eigenspaces.

### What Would a Proof Need?

- Lemma: on a nilpotent $N$, $\dim\ker N^{j} - \dim\ker N^{j-1}$ is nonincreasing
  in $j$ (needed for the counts to be nonnegative).
- Lemma: second difference $= $ number of blocks of exact size $j$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The generalized-eigenspace tower is already constructed in the parent entry,
  so the infrastructure exists.
- The combinatorics (partition ↔ kernel dimensions) is classical; the risk is
  Mathlib's JCF coverage.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks

## References

### Mathlib
- `Mathlib.LinearAlgebra.Eigenspace.Basic` / `...Zero` — generalized eigenspaces.
- `Mathlib.LinearAlgebra.JordanChevalley` and nilpotent-operator lemmas.

## Metadata

```yaml
tags:
  - linear-algebra
  - cayley-hamilton
  - minimal-polynomial
  - jordan-canonical-form
  - generalized-eigenspace
  - eigenvalues
related_proofs:
  - cayley-hamilton-minpoly-oq-01-oq-01
  - cayley-hamilton-minpoly
difficulty: medium
source: gallery-gap
created: 2026-07-04T00:45:01-07:00
```

**Significance**: 6/10
**Tractability**: 5/10
