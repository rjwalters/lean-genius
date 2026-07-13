# Problem: Hockey-Stick and Li Jen-Shu Diagonal Sum Identities

**Slug**: binomial-theorem-oq-06-oq-02
**Status**: Active
**Source**: proof-suggestion (open question from `binomial-theorem-oq-06`)

## Problem Statement

### Formal Statement

Formalize the following diagonal sums of Pascal's triangle as consequences of / companions to
Vandermonde's convolution (the parent entry):

1. **Hockey-stick identity:**
$$
\sum_{i=r}^{n} \binom{i}{r} = \binom{n+1}{r+1}.
$$

2. **Li Jen-Shu (Vandermonde-diagonal) identity**, e.g.
$$
\sum_{k=0}^{n} \binom{n}{k}\binom{n}{k} = \binom{2n}{n},
$$
and connect $\sum_k \binom{n}{k}^2 = \binom{2n}{n}$ to the lattice-path / Catalan-number reading
(central binomial coefficient counts monotone lattice paths).

Prove the hockey-stick identity and the central-square identity $\sum_k \binom{n}{k}^2 = \binom{2n}{n}$
over $\mathbb{N}$.

### Plain Language

The parent proved Vandermonde's convolution and $\sum \binom{n}{k}^2 = \binom{2n}{n}$. This asks for
the *hockey-stick* diagonal sum $\sum_{i\ge r}\binom{i}{r}=\binom{n+1}{r+1}$ and the lattice-path
interpretation of the central identity.

### Why This Matters

Hockey-stick and the central-square identity are the canonical "diagonal sums" of Pascal's triangle;
together with Vandermonde they round out the elementary binomial-sum toolkit and link to lattice paths.

## Known Results

### What's Already Proven

- Vandermonde's convolution and $\sum_k \binom{n}{k}^2 = \binom{2n}{n}$ — parent `binomial-theorem-oq-06`.
- Mathlib: `Nat.sum_range_choose`, `Nat.add_choose_le`, `Nat.succ_sub`, Pascal's rule `Nat.choose_succ_succ`,
  and `Nat.add_pow_le`; hockey-stick may already exist as `Nat.sum_range_choose_mul_two` variants — check first.

### Our Goal

Prove the hockey-stick identity (primary) and re-derive $\sum \binom{n}{k}^2 = \binom{2n}{n}$ with the
lattice-path narrative, 0 axioms, 0 sorries. Verify which pieces Mathlib already provides before building.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| binomial-theorem-oq-06 | Parent: Vandermonde convolution | `Finset.sum`, Pascal's rule |
| combinations-formula-* | Binomial coefficient identities | `Nat.choose`, absorption |

## Initial Thoughts

### Potential Approaches

1. **Hockey-stick by induction** on $n$ using Pascal's rule `Nat.choose_succ_succ`;
   `Finset.sum_range_succ` + `omega`.
2. **Central square via Vandermonde** + `Nat.choose_symm` (rewrite one factor), reusing the parent.

### Key Difficulties

- Reindexing the diagonal sum (`Finset.Icc r n` vs `Finset.range`) cleanly.
- Confirming Mathlib does not already ship these (avoid trivial restatement) — add the lattice-path
  interpretation as genuine value if the raw identity is already present.
