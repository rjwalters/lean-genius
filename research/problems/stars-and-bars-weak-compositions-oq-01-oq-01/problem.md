# Problem: Last-Part Recurrence for Weak Compositions

**Slug**: stars-and-bars-weak-compositions-oq-01-oq-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
C(n,k) \;=\; \sum_{j=0}^{n} C(n-j,\, k-1), \qquad k \ge 1, \qquad C(n,0) = [\,n = 0\,],
$$

where $C(n,k) = \binom{n+k-1}{n}$ counts the weak compositions of $n$ into exactly $k$
non-negative parts (equivalently, multisets of size $n$ drawn from $k$ types). The goal is
to formalize this last-part convolution recurrence and prove it agrees with the closed
form $\binom{n+k-1}{n}$ established by the parent entry
`stars-and-bars-weak-compositions-oq-01`. As a corollary, recover the single-step
Pascal-type identity

$$
\binom{n+k-1}{n} = \binom{n+k-2}{n} + \binom{n+k-2}{n-1}.
$$

### Plain Language

Stars-and-bars says the number of ways to write $n$ as an ordered sum of $k$ non-negative
integers is $\binom{n+k-1}{n}$. This problem asks for the *recursive* view: if you fix the
last part to be $j$ (any value from $0$ to $n$), the remaining $k-1$ parts must sum to
$n-j$, so the total splits as a sum over $j$ of $(k-1)$-part counts. Proving this
convolution equals the closed form is the hockey-stick identity in disguise; collapsing
the last part into "is it zero or positive?" yields the ordinary Pascal recurrence for
multiset coefficients.

### Why This Matters

The convolution recurrence is the combinatorial backbone connecting stars-and-bars to the
generating-function identity $\sum_n C(n,k)x^n = (1-x)^{-k}$ (product of geometric series
= convolution of coefficient sequences). Formalizing it gives a self-contained,
induction-friendly route to the multiset-coefficient count that avoids direct
`Nat.choose` surgery and supplies a reusable summation lemma for other counting entries.

## Known Results

### What's Already Proven

- Closed form $C(n,k)=\binom{n+k-1}{n}$ — parent `stars-and-bars-weak-compositions-oq-01`.
- Hockey-stick identity in Mathlib (`Nat.sum_range_choose`, `Nat.add_choose`) — supplies
  the summation collapse.

### What's Still Open (for this entry)

- A machine-checked statement of the last-part recurrence and its equivalence to the
  closed form.
- The Pascal-type corollary derived as a one-line specialization.

### Our Goal

Formalize `C n k = ∑ j in Finset.range (n+1), C (n-j) (k-1)` for
`C n k = Nat.choose (n+k-1) n`, axiom-free, and derive the Pascal recurrence corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| stars-and-bars-weak-compositions-oq-01 | parent: closed-form / generating-function count | generating functions |
| stars-and-bars-weak-compositions | base bijective stars-and-bars | bijection |
| pascal-triangle (binomial identities) | source of the Pascal corollary | induction |

## Initial Thoughts

### Potential Approaches

1. **Reindex + hockey-stick**: express the sum $\sum_{j} \binom{(n-j)+(k-2)}{n-j}$ and
   apply a hockey-stick identity after a `Finset.range` reindexing.
   - Why it might work: Mathlib already has the collapsing lemma.
   - Risk: matching index conventions (`n+k-1` vs `n+k-2`) needs care.

2. **Induction on `k`**: base `k=1` is the constant sum $\sum_{j\le n}1 = n+1$; step uses
   the convolution.
   - Why it might work: clean structural induction.
   - Risk: bookkeeping on the inner sum.

### Key Difficulties

- Off-by-one in the negative-binomial index (`n+k-1`).
- Choosing between `Finset.range (n+1)` and `Finset.Iic n`.

### What Would a Proof Need?

- Key lemma: hockey-stick `∑ i in range (m+1), choose (i+r) r = choose (m+r+1) (r+1)`.
- Reindexing `j ↦ n-j` on `Finset.range (n+1)`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Mathlib supplies the hockey-stick collapse and Pascal's rule directly.
- The recurrence is a finite sum identity provable by induction on `k` or one reindex.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Combinatorics.Choose.Sum` — hockey-stick and `Nat.sum_range_choose`.
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose_succ_succ` (Pascal's rule).

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - generating-functions
  - stars-and-bars
related_proofs:
  - stars-and-bars-weak-compositions-oq-01
  - stars-and-bars-weak-compositions
difficulty: medium
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 7/10
