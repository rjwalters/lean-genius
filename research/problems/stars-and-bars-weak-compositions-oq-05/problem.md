# Problem: Marginal Count of Weak Compositions with a Fixed First Part

**Slug**: stars-and-bars-weak-compositions-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: stars-and-bars-weak-compositions

## Problem Statement

### Formal Statement

For $k\ge 1$ and $d\le n$, the number of weak compositions $f:\{0,\dots,k-1\}\to\mathbb N$
with $\sum_i f_i = n$ and first part $f_0 = d$ equals the number of *unrestricted* weak
compositions of $n-d$ into $k-1$ parts:

$$
\#\{\,f:\textstyle\sum_i f_i = n,\ f_0 = d\,\}
\;=\;\binom{(n-d)+(k-1)-1}{(k-1)-1}
\;=\;\binom{n-d+k-2}{\,n-d\,}.
$$

Summing over $d$ from $0$ to $n$ recovers the parent's total $\binom{n+k-1}{k-1}$ (a
hockey-stick / Vandermonde consistency check).

### Plain Language

The parent entry `stars-and-bars-weak-compositions` proves the master count
$\binom{n+k-1}{k-1}$ for weak compositions of $n$ into $k$ parts. This child proves the
natural **conditional** refinement: if you *fix* the first part to a value $d$, the remaining
parts form a weak composition of $n-d$ into $k-1$ parts, so the conditioned count is just the
stars-and-bars number one dimension down. The engine is a bijection "drop the first
coordinate," transported through `Fintype.card_congr`, and then the parent theorem applied to
the smaller instance.

### Why This Matters

Marginals of the stars-and-bars distribution are the building blocks for generating-function
proofs, for the negative-hypergeometric distribution, and for the hockey-stick identity
(summing the marginal over $d$ reproves the total). Mathlib counts multisets/weak compositions
via `Nat.multichoose` and `Sym`, but has **no** lemma for a count conditioned on one
coordinate's value. The bijection is short but genuinely new content, and it must be composed
with the parent's master count — not a single lookup.

## Known Results

### What's Already Proven

- Parent `stars-and-bars-weak-compositions` is verified (0-axiom): the master count
  `#{f : Fin k → ℕ // ∑ f = n} = (n + k - 1).choose (k - 1)`.
- Mathlib: `Fintype.card_congr` (transport cardinality across an equiv), `Nat.multichoose_eq`
  (`multichoose n k = (n+k-1).choose k`), `Finset.Nat.antidiagonal`/`Finset.sum_range_choose`
  and hockey-stick `Nat.sum_range_choose_mul_pow` (for the summation check).

### What's Still Open

- The conditioned marginal count and the summation consistency (currently `sorry`).

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**enumerative combinatorics / refinement completion**.

## Target Lean Sketch

```lean
open Finset

/-- Weak compositions of `n` into `k` parts whose first part is exactly `d`
    biject with weak compositions of `n - d` into `k - 1` parts. -/
def dropFirstEquiv (k n d : ℕ) (hk : 1 ≤ k) (hd : d ≤ n) :
    {f : Fin k → ℕ // (∑ i, f i = n) ∧ f 0 = d} ≃
    {g : Fin (k - 1) → ℕ // ∑ i, g i = n - d} := by
  sorry
  -- forward: `g = fun i => f i.succ` (using `Fin.tail`); ∑ g = n - d because f 0 = d.
  -- inverse: `f = Fin.cons d g`; ∑ = d + (n-d) = n and (Fin.cons d g) 0 = d.

/-- Marginal count: fixing the first part to `d` gives a `(k-1)`-part stars-and-bars number. -/
theorem card_weakComposition_first_eq (k n d : ℕ) (hk : 1 ≤ k) (hd : d ≤ n) :
    Fintype.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ f 0 = d}
      = (n - d + (k - 1) - 1).choose ((k - 1) - 1) := by
  sorry
  -- `Fintype.card_congr (dropFirstEquiv ...)` then the parent master count on (k-1, n-d).

/-- Consistency: summing the marginal over `d = 0..n` recovers the parent's total. -/
theorem sum_marginals_eq_total (k n : ℕ) (hk : 1 ≤ k) :
    (∑ d ∈ range (n + 1),
        Fintype.card {f : Fin k → ℕ // (∑ i, f i = n) ∧ f 0 = d})
      = (n + k - 1).choose (k - 1) := by
  sorry
  -- Rewrite each summand with the previous theorem, then a hockey-stick/Vandermonde identity.
```

Add worked `example`s: `k = 3, n = 4` — marginals over `d = 0..4` are `15,10,6,3,1` summing to
`35 = C(6,2)`; the boundary `d = n` gives count `1`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `stars-and-bars-weak-compositions` | Parent: master count `C(n+k-1,k-1)` | bijective combinatorics |
| `combinations-formula` | Binomial coefficient identities | combinatorics |
| `subset-count` | Counting via `Fintype.card` bijections | finite cardinality |

## Tractability Assessment

**Difficulty**: Low-Medium

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The bijection is `Fin.cons`/`Fin.tail` bookkeeping; the count follows by
`Fintype.card_congr` and the parent theorem. The summation check is a standard hockey-stick
identity. No analysis, no deep algebra.

### Suggested First Steps

1. Build `dropFirstEquiv` with `Fin.cons`/`Fin.tail`; discharge the sum conditions with
   `Fin.sum_cons` and `Nat.add_sub_cancel'` (needs `hd : d ≤ n`).
2. Derive `card_weakComposition_first_eq` via `Fintype.card_congr` + parent count.
3. Prove `sum_marginals_eq_total` by rewriting and applying a hockey-stick lemma.

## References

### Mathlib

- `Fintype.card_congr` — Data/Fintype/Card.lean
- `Fin.cons`, `Fin.tail`, `Fin.sum_cons` — Data/Fin/Tuple/Basic.lean, Algebra/BigOperators/Fin.lean
- `Nat.multichoose_eq`, `Nat.succ_sub_one` — Data/Nat/Choose/Multinomial.lean
- Hockey-stick `Nat.sum_range_choose` — Data/Nat/Choose/Sum.lean

### Literature

- Stanley, *Enumerative Combinatorics* Vol. 1, §1.2 (weak compositions and their marginals);
  the fixed-part refinement is a standard exercise underlying the negative-hypergeometric law.

## Metadata

```yaml
tags:
  - combinatorics
  - stars-and-bars
  - bijective-proof
  - binomial-coefficients
related_proofs:
  - stars-and-bars-weak-compositions
  - combinations-formula
  - subset-count
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
