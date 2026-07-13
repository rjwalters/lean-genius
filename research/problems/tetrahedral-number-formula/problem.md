# Problem: Sum of Triangular Numbers Equals the Tetrahedral Number

**Slug**: tetrahedral-number-formula
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{k=1}^{n} T_k \;=\; \binom{n+2}{3} \;=\; \frac{n(n+1)(n+2)}{6},
\qquad\text{where } T_k = \binom{k+1}{2} = \frac{k(k+1)}{2}.
$$

The goal is a machine-checked proof, over $\mathbb{N}$, that the partial sums of the
triangular numbers $T_k$ are exactly the tetrahedral numbers $\mathrm{Te}_n = \binom{n+2}{3}$.
An integer-division-free formulation is preferred: prove the cleared-denominator identity
$6\sum_{k=1}^{n} T_k = n(n+1)(n+2)$, or work directly with `Nat.choose` so no division
appears.

### Plain Language

A *triangular number* $T_k = 1 + 2 + \dots + k$ counts the dots in a triangular arrangement
with $k$ dots per side. If you stack these triangles into a tetrahedron — a triangle of
$1$ dot on top, then $3$, then $6$, and so on — the total number of dots after $n$ layers is
the *tetrahedral number*. This problem asks us to prove that the running total of the first
$n$ triangular numbers is always $\binom{n+2}{3}$, i.e. $n(n+1)(n+2)/6$.

### Why This Matters

This is the second rung of the figurate-number ladder (linear $\to$ triangular $\to$
tetrahedral), the $d=3$ case of the general simplicial identity
$\sum_{k} \binom{k+d-2}{d-1} = \binom{n+d-1}{d}$ (a hockey-stick identity). Formalizing it
gives a clean, reusable "sum of a column of Pascal's triangle" lemma and a self-contained
counterpart to the existing `arithmetic-series` (sum of $1..n$) and
`nicomachus-sum-of-cubes` entries, rounding out the gallery's coverage of elementary
closed-form summation.

## Known Results

### What's Already Proven

- Triangular closed form $\sum_{k=1}^n k = \binom{n+1}{2}$ — gallery `arithmetic-series`.
- Hockey-stick identity $\sum_{i} \binom{i}{r} = \binom{n+1}{r+1}$ in Mathlib
  (`Nat.sum_range_choose`, `Nat.sum_Icc_choose` / `Nat.add_choose` family).
- Pascal's rule `Nat.choose_succ_succ` — supplies the inductive step directly.

### What's Still Open (for this entry)

- A formal Lean statement of $\sum_{k=1}^{n} T_k = \binom{n+2}{3}$ and its equivalence to
  the polynomial form $n(n+1)(n+2)/6$.
- The optional generalization to arbitrary simplicial dimension $d$.

### Our Goal

Prove, axiom-free and `sorry`-free, that
`∑ k in Finset.range (n+1), (k+1).choose 2 = (n+2).choose 3` (or the equivalent
`Finset.Icc 1 n` form), and derive the polynomial closed form
`6 * ∑ k in Finset.range (n+1), k*(k+1)/2 = n*(n+1)*(n+2)`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arithmetic-series | previous rung: $\sum k = \binom{n+1}{2}$ (triangular numbers) | induction / Gauss pairing |
| nicomachus-sum-of-cubes-oq-01 | sibling elementary closed-form power/figurate sum | induction, `ring` |
| binomial-theorem | source of the `Nat.choose` identities used | binomial coefficients |

## Initial Thoughts

### Potential Approaches

1. **Direct induction on `n`**: base $n=0$ is $0 = \binom{2}{3} = 0$; step adds $T_{n+1}$
   and closes with `Nat.choose_succ_succ` / `ring` after clearing denominators.
   - Why it might work: fully elementary, no division if phrased via `Nat.choose`.
   - Risk: `Nat` truncated division in the $k(k+1)/2$ form — prefer the `choose` phrasing
     or multiply through by 6.

2. **Hockey-stick collapse**: rewrite $T_k = \binom{k+1}{2}$ and apply Mathlib's
   `Nat.sum_range_choose`-style column-sum lemma to land on $\binom{n+2}{3}$ in one step.
   - Why it might work: Mathlib already has the collapsing identity.
   - Risk: matching index conventions (`range (n+1)` vs `Icc`, and the `+2` / `+1` offsets).

### Key Difficulties

- Avoiding `Nat` integer-division pitfalls in $k(k+1)/2$: either stay in `Nat.choose`
  or prove the $\times 6$ cleared form and divide once at the end.
- Index/offset bookkeeping between `Finset.range` and `Finset.Icc`.

### What Would a Proof Need?

- Key lemma: $T_k = \binom{k+1}{2}$ (so the sum is a column of Pascal's triangle).
- Key lemma: hockey-stick $\sum_{k\le n}\binom{k+1}{2} = \binom{n+2}{3}$.
- `ring`/`omega` to reconcile $\binom{n+2}{3}$ with $n(n+1)(n+2)/6$.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Pure finite-sum identity with a one-line inductive step.
- Mathlib supplies both the hockey-stick collapse and Pascal's rule.
- Directly analogous to the solved `arithmetic-series` and `nicomachus-sum-of-cubes` entries.

**Estimated Effort**:
- Exploration: hours
- If tractable: under a day

## References

### Online Resources
- OEIS A000292 (tetrahedral numbers) — closed form and figurate-number background.

### Mathlib
- `Mathlib.Combinatorics.Choose.Sum` — hockey-stick / `Nat.sum_range_choose`.
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose_succ_succ` (Pascal's rule).
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum` manipulation.

## Metadata

```yaml
tags:
  - combinatorics
  - figurate-numbers
  - binomial-coefficients
  - finite-sums
related_proofs:
  - arithmetic-series
  - nicomachus-sum-of-cubes-oq-01
  - binomial-theorem
difficulty: low
source: gallery-gap
created: 2026-07-04
```

**Significance**: 4/10
**Tractability**: 8/10
