# Problem: Row sum of the unsigned Stirling numbers of the first kind equals n!

**Slug**: bell-numbers-oq-01-oq-03
**Created**: 2026-07-02T11:12:11-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\sum_{k=0}^{n} \left[{n \atop k}\right] = n!,
$$

where $\left[{n \atop k}\right]$ (Mathlib's `Nat.stirlingFirst n k`) is the *unsigned* Stirling
number of the first kind — the number of permutations of an $n$-element set having exactly $k$
disjoint cycles. In Lean the target statement is

```lean
theorem stirlingFirst_row_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n.factorial
```

### Plain Language

Every permutation of $n$ objects decomposes uniquely into disjoint cycles. If we sort permutations
by *how many* cycles they have, $\left[{n \atop k}\right]$ counts those with exactly $k$ cycles.
Since there are $n!$ permutations in total and each has some number of cycles between $1$ and $n$
(and $0$ cycles only when $n = 0$), adding up the counts across all possible cycle-numbers must
recover the total: $\sum_k \left[{n \atop k}\right] = n!$. This is the first-kind companion of the
parent entry's second-kind row sum $B_n = \sum_k S(n,k)$, where partitions replace permutations and
Bell numbers replace $n!$.

### Why This Matters

The two families of Stirling numbers are the connection coefficients between the standard, rising,
and falling factorial bases of the polynomial ring, and their row sums are the most basic sanity
identity each family satisfies. The second-kind row sum ($=B_n$) is already formalized in the parent
entry `bell-numbers-oq-01`; the first-kind row sum ($=n!$) is its natural twin and is likewise
*absent from pinned Mathlib*. Formalizing it completes the pair, exercises the same conditioning /
recurrence toolkit on Mathlib's `Nat.stirlingFirst`, and provides a reusable lemma
($\sum_k \left[{n \atop k}\right] = n!$) that the library currently lacks.

## Known Results

### What's Already Proven

- **Parent second-kind row sum** `bell-numbers-oq-01` — $B_n = \sum_{k} S(n,k)$, established by a
  "horizontal" recurrence obtained by conditioning on the block of the last point. — gallery entry
  `src/data/proofs/bell-numbers-oq-01/`.
- **Mathlib's `Nat.stirlingFirst`** — the recursive definition, its boundary values, and the
  triangular recurrence $\left[{n+1 \atop k+1}\right] = n\left[{n \atop k+1}\right] + \left[{n \atop k}\right]$
  (`Nat.stirlingFirst_succ_succ`), the vanishing $\left[{n \atop k}\right]=0$ for $k>n$
  (`Nat.stirlingFirst_eq_zero_of_lt`), the diagonal `Nat.stirlingFirst_self`, and the first column
  `Nat.stirlingFirst_one_right : stirlingFirst (n+1) 1 = n!`. —
  `Mathlib.Combinatorics.Enumerative.Stirling`.

### What's Still Open

- The row-sum identity $\sum_{k=0}^{n} \left[{n \atop k}\right] = n!$ itself: Mathlib has the
  first-kind recurrence and boundary lemmas but **no lemma summing a row to $n!$** (grep of
  `Mathlib/Combinatorics/Enumerative/Stirling.lean` for a row-sum / factorial identity returns
  nothing beyond `stirlingFirst_one_right`).

### Our Goal

Formalize in Lean 4 / Mathlib the single theorem
`∑ k ∈ Finset.range (n+1), Nat.stirlingFirst n k = n.factorial`, mirroring the conditioning /
recurrence style of the parent proof. A short, self-contained file (comparable in size to the
parent's ~120 lines, likely smaller) with 0 sorries and 0 axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bell-numbers-oq-01 | Direct parent: second-kind companion row sum $B_n=\sum_k S(n,k)$; same conditioning argument on the last point | triangular/horizontal recurrence, `Finset.sum_range_succ'`, `sum_comm`, `sum_subset`, strong induction, `omega` |
| bell-numbers-oq-01-oq-01 | Sibling OQ: EGF $\sum B_n x^n/n! = \exp(e^x-1)$ of the same Bell/Stirling material | formal power series, `PowerSeries.exp` |
| bell-numbers-oq-01-oq-02 | Sibling OQ: Dobiński's formula for the Bell numbers | analytic/series estimates |

## Initial Thoughts

### Potential Approaches

1. **Approach A — induction on $n$ via the triangular recurrence (recommended)**:
   Prove $\sum_{k=0}^{n} \left[{n \atop k}\right] = n!$ by induction on $n$. Base: $n=0$ gives the
   single term $\left[{0 \atop 0}\right]=1=0!$. Step: split the sum at $k=0$ (which vanishes for
   $n+1>0$ by `stirlingFirst_succ_zero`), re-index the remaining terms with
   `Finset.sum_range_succ'`, apply `Nat.stirlingFirst_succ_succ` to each term to get
   $\sum_k\left(n\left[{n \atop k+1}\right] + \left[{n \atop k}\right]\right)$, distribute the sum
   (`Finset.sum_add_distrib`), factor out $n$ (`Finset.mul_sum`), telescope the shifted
   $\sum_k \left[{n \atop k+1}\right]$ back to the full row using
   `Nat.stirlingFirst_eq_zero_of_lt` to add/drop the vanishing tail term, and apply the inductive
   hypothesis to both blocks. This yields $n\cdot n! + n! = (n+1)\cdot n! = (n+1)!$
   (`Nat.factorial_succ`), closed by `ring`/`omega`.
   - Why it might work: this is exactly the parent proof's recurrence-matching mechanic (peel $k=0$,
     re-index, apply recurrence, fold using the vanishing tail), and every Mathlib ingredient
     (`stirlingFirst_succ_succ`, `stirlingFirst_eq_zero_of_lt`, `factorial_succ`) already exists.
   - Risk: index bookkeeping when shifting between $\sum_{k\in\text{range}(n+1)}\left[{n \atop k+1}\right]$
     and the full row $\sum_{k\in\text{range}(n+2)}\left[{n \atop k}\right]$; must carefully add the
     zero tail term via `Finset.sum_range_succ` + `stirlingFirst_eq_zero_of_lt`.

2. **Approach B — bijective / conditioning argument on the last point (companion to the parent)**:
   Mirror the parent's combinatorial conditioning: a permutation of $\{0,\dots,n\}$ is built from a
   permutation of $\{0,\dots,n-1\}$ by inserting $n$ either as a new fixed-point cycle (adds a cycle:
   the $\left[{n \atop k}\right]$ term) or immediately after one of the $n$ existing elements in some
   cycle (keeps the cycle count: the $n\left[{n \atop k+1}\right]$ term). Summing over $k$ gives
   $(n+1)! = (n+1)\cdot n!$, i.e. the total count $\sum_k \left[{n+1 \atop k}\right] = (n+1)!$.
   - Why it might work: it is the "analogous conditioning argument" the OQ explicitly requests and
     matches the parent's narrative most faithfully.
   - Risk: a fully bijective formalization (via `Equiv.Perm` and cycle types) is substantially more
     work than Approach A; the recurrence $\left[{n+1 \atop k+1}\right] = n\left[{n \atop k+1}\right] + \left[{n \atop k}\right]$
     is the algebraic shadow of exactly this conditioning, so Approach A already captures its content.

### Key Difficulties

- Re-indexing the shifted row $\sum_k \left[{n \atop k+1}\right]$ back to the full row, which
  requires inserting/deleting the zero tail term via `Nat.stirlingFirst_eq_zero_of_lt` — the same
  padded-range subtlety the parent handles with `Finset.sum_subset`.
- Keeping the two summands ($n\left[{n \atop k+1}\right]$ and $\left[{n \atop k}\right]$) aligned
  over the correct `Finset.range` after `sum_range_succ'` peels the $k=0$ term.

### What Would a Proof Need?

- Key lemma 1: `Nat.stirlingFirst_succ_succ` — the triangular recurrence, applied termwise inside
  the sum.
- Key lemma 2: `Nat.stirlingFirst_eq_zero_of_lt` — to pad/unpad the shifted row so the inductive
  hypothesis applies to a full `range (n+1)` sum.
- Technical requirements: `Nat.factorial_succ`, `Finset.sum_range_succ` / `Finset.sum_range_succ'`,
  `Finset.sum_add_distrib`, `Finset.mul_sum`, and `omega`/`ring` for the final arithmetic
  $n\cdot n! + n! = (n+1)!$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The identity is classical and elementary; the only real work is Lean-side sum re-indexing.
- The parent entry `bell-numbers-oq-01` solved the *harder* second-kind companion (whose target is
  $B_n$, requiring a bespoke horizontal recurrence) with the very same toolkit; the first-kind case
  is simpler because the target $n!$ satisfies the clean recurrence $(n+1)! = (n+1)\cdot n!$ that
  falls straight out of the row recurrence with no auxiliary "horizontal" identity needed.
- All required Mathlib lemmas (`stirlingFirst_succ_succ`, `stirlingFirst_eq_zero_of_lt`,
  `factorial_succ`, the `Finset.sum` re-indexing API) are already present and were exercised in the
  parent proof.

**Estimated Effort**:
- Exploration: 2–4 hours
- If tractable: 1–2 days
- If hard: about a week (only if a fully bijective `Equiv.Perm` cycle-type route is pursued instead
  of Approach A)

## References

### Papers
- Stanley, R. P., *Enumerative Combinatorics, Volume 1*, 2nd ed., Cambridge University Press (2011),
  §1.3 — permutations by cycle type; the (signless) Stirling numbers of the first kind $c(n,k)$ and
  the row sum $\sum_k c(n,k) = n!$.
- Graham, Knuth, Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley (1994), §6.1 — Stirling
  numbers, the recurrence $\left[{n \atop k}\right] = (n-1)\left[{n-1 \atop k}\right] + \left[{n-1 \atop k-1}\right]$, and $\sum_k \left[{n \atop k}\right] = n!$.

### Online Resources
- https://oeis.org/A130534 — triangle of unsigned Stirling numbers of the first kind; the row sums
  are $n!$ (A000142).
- https://en.wikipedia.org/wiki/Stirling_numbers_of_the_first_kind — recurrence and the row-sum
  identity $\sum_{k=0}^{n} \left[{n \atop k}\right] = n!$.

### Mathlib
- `Mathlib.Combinatorics.Enumerative.Stirling` — defines `Nat.stirlingFirst` and provides
  `stirlingFirst_succ_succ` (triangular recurrence), `stirlingFirst_eq_zero_of_lt`,
  `stirlingFirst_self`, and `stirlingFirst_one_right`; contains **no** row-sum-to-$n!$ lemma (the gap
  this problem fills).
- `Mathlib.Data.Nat.Factorial.Basic` — `Nat.factorial` and `Nat.factorial_succ` for the target $n!$
  and its recurrence.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_range_succ'`, `Finset.sum_add_distrib`,
  `Finset.mul_sum` for the sum manipulations.

## Metadata

```yaml
tags:
  - combinatorics
  - stirling-numbers
  - permutations
  - cycles
  - factorial
  - finite-sums
related_proofs:
  - bell-numbers-oq-01
  - bell-numbers-oq-01-oq-01
  - bell-numbers-oq-01-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-07-02T11:12:11-07:00
```

**Significance**: 6/10
**Tractability**: 7/10
