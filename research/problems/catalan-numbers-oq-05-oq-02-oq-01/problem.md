# Problem: Row sums of Catalan's triangle: Σₖ T(n,k) = C(2n+1, n)

**Slug**: catalan-numbers-oq-05-oq-02-oq-01
**Created**: 2026-07-09T16:43:20-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\sum_{k=0}^{n} T(n,k) \;=\; \binom{2n+1}{n},
\qquad\text{where}\quad
T(n,k) \;=\; \binom{n+k}{k} - \binom{n+k}{n+1}.
$$

Equivalently, letting `ballotNumber n k` denote the exact-ℕ Catalan-triangle
entry of the parent gallery proof, the goal is

$$
\sum_{k=0}^{n} \operatorname{ballotNumber}(n,k) \;=\; \binom{2n+1}{n}.
$$

### Plain Language

Catalan's triangle is a two-parameter array of "ballot numbers" `T(n,k)`, each
counting the monotone lattice paths from `(0,0)` to `(n,k)` that never rise above
the main diagonal. Its diagonal entries `T(n,n)` are exactly the Catalan numbers.
This problem asks us to add up an entire row of the triangle. When you sum the
row `T(n,0) + T(n,1) + ⋯ + T(n,n)`, the individual difference-of-binomial terms
telescope and aggregate into a single clean central-binomial value, `C(2n+1, n)`.
Intuitively, summing over all valid endpoints on the row aggregates every
diagonal-bounded path of the appropriate length, so the total is again a natural
"ballot" count. The task is to prove this row-sum identity in Lean 4, on top of
the parent's already-verified `ballotNumber` object and its closed form.

### Why This Matters

Row sums close the loop between a combinatorial array and the sequence it is
built from: they show that aggregating the reflection-principle counts across a
whole row reproduces a central binomial coefficient, tying Catalan's triangle
back to the Catalan/central-binomial family that generates it. This is the
natural next structural fact after the parent established the individual entries,
their closed form, and the lattice-path recurrence. Formalizing it exercises
finite-sum manipulation over binomial coefficients — telescoping and hockey-stick
style aggregation — which are recurring patterns in enumerative combinatorics and
currently have no dedicated Catalan-triangle instance in Mathlib.

## Known Results

### What's Already Proven

- `ballotNumber n k = C(n+k,k) − C(n+k,n+1)` and its scaled closed form `(n+1)·T(n,k) = (n+1−k)·C(n+k,k)` — parent proof `catalan-numbers-oq-05-oq-02` (`Proofs/CatalanNumbersOQ05OQ02.lean`).
- The reflection-principle recurrence `T(n+1,k+1) = T(n+1,k) + T(n,k+1)` and diagonal `T(n,n) = catalan n` — same parent proof.
- Pascal's rule `Nat.choose_succ_succ` and hockey-stick / column-sum lemmas over binomials — `Mathlib.Data.Nat.Choose.Basic` and `Mathlib.Data.Nat.Choose.Sum`.

### What's Still Open

- The closed evaluation of the full row sum `Σ_{k=0}^{n} T(n,k)` as `C(2n+1, n)` is not formalized in the gallery or Mathlib.
- The bridge relating `C(2n+1, n)` to the succeeding Catalan number `catalan (n+1)` (the ballot-aggregation reading of the identity) is not yet recorded.

### Our Goal

Prove, in Lean 4 over ℕ, the single identity
`∑ k in Finset.range (n+1), ballotNumber n k = (2*n+1).choose n`,
reusing the parent's `ballotNumber` definition and closed form. The scope is the
row-sum evaluation itself; a genuine bijective (Finset-of-paths) proof is out of
scope and left to a separate leaf.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| catalan-numbers-oq-05-oq-02 | Parent: defines `ballotNumber n k` and proves its closed form, recurrence, and diagonal — the exact object this row sum aggregates | Reflection principle, `Nat.choose_succ_right_eq`, `Nat.choose_symm`, Pascal splits, `omega` over ℕ subtraction |

## Initial Thoughts

### Potential Approaches

1. **Approach A — telescoping the difference form**: Substitute
   `T(n,k) = C(n+k,k) − C(n+k,n+1)` under the sum and split into two sums,
   `Σ C(n+k,k) − Σ C(n+k,n+1)`. Reindex each with hockey-stick-style column
   identities (`Mathlib.Data.Nat.Choose.Sum`) so that the two aggregated binomial
   sums collapse; the reflected-term sum cancels most of the direct-term sum,
   leaving `C(2n+1,n)`.
   - Why it might work: the closed forms are already binomials, and Mathlib has
     column/antidiagonal sum lemmas for `Nat.choose`.
   - Risk: ℕ subtraction inside the sum — must justify termwise `T ≥ 0`
     (available as `ballotNumber_le`) before commuting `Σ` past the subtraction.

2. **Approach B — induction on `n` via the recurrence**: Define `S(n) = Σ_{k≤n} T(n,k)`
   and use the parent's path recurrence `T(n+1,k+1) = T(n+1,k) + T(n,k+1)` plus
   the boundary values `T(n,0)=1`, `T(n,1)=n` to relate `S(n+1)` to `S(n)`, then
   match the target ratio `C(2n+3,n+1) / C(2n+1,n)`.
   - Why it might work: the recurrence is already proven; induction reduces the
     identity to one algebraic step per row.
   - Risk: bookkeeping the shifted index ranges and the boundary corrections is
     delicate; the per-step binomial ratio identity still needs a factorial lemma.

### Key Difficulties

- Truncated ℕ subtraction inside `ballotNumber` forces care when moving `Finset.sum`
  across the difference; the well-posedness inequality `ballotNumber_le` must be
  invoked termwise.
- Mathlib has hockey-stick and column-sum lemmas for `Nat.choose`, but the exact
  reindexing needed to collapse `Σ C(n+k,k)` and `Σ C(n+k,n+1)` may require
  reindexing (`Finset.sum_range_succ`, `Finset.sum_bij`) rather than a single lemma.

### What Would a Proof Need?

- Key lemma 1: termwise nonnegativity / well-posedness so the sum of differences
  equals the difference of sums (from parent `ballotNumber_le`).
- Key lemma 2: a hockey-stick / column-sum evaluation of `Σ_{k=0}^{n} C(n+k,k)`
  and `Σ_{k=0}^{n} C(n+k,n+1)` in terms of `C(2n+1, ·)`.
- Technical requirements: `Finset.sum_range_succ`, `Nat.sum_range_choose`-style
  identities, and factorial/binomial arithmetic closed by `omega` on the atoms.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The target object and all its algebraic building blocks (closed form,
  recurrence, monotonicity, boundary values) are already verified in the parent,
  so this is a self-contained aggregation step rather than new theory.
- Similar finite-sum-over-binomial identities are routinely formalized with
  Mathlib's `Nat.Choose.Sum` machinery.
- The main friction is ℕ subtraction under the sum and locating the right
  reindexing, both of which are known, surmountable Lean idioms.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 3–5 days
- If hard: 1–2 weeks

## References

### Papers
- André, Désiré, "Solution directe du problème résolu par M. Bertrand", 1887 — the reflection principle producing the ballot numbers `T(n,k)` whose row we sum.
- Stanley, Richard P., "Catalan Numbers", 2015 — treatment of Catalan's triangle, its row sums, and central-binomial connections.

### Online Resources
- OEIS A009766 (Catalan's triangle) — records the row-sum and recurrence structure of `T(n,k)`.

### Mathlib
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose`, `Nat.choose_succ_succ`, `Nat.choose_symm`, `Nat.choose_succ_right_eq`.
- `Mathlib.Data.Nat.Choose.Sum` — hockey-stick and range-sum identities for `Nat.choose`.
- `Mathlib.Data.Nat.Choose.Central` — `Nat.centralBinom` and its relation to `(2n).choose n`.
- `Mathlib.Combinatorics.Enumerative.Catalan` — `catalan`, `succ_mul_catalan_eq_centralBinom`.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_range_succ`, `Finset.sum_bij` for reindexing sums.

## Metadata

```yaml
tags:
  - combinatorics
  - catalan-numbers
  - catalan-triangle
  - ballot-numbers
  - central-binomial
  - binomial-coefficients
  - reflection-principle
  - ballot-problem
  - lattice-paths
  - research
related_proofs:
  - catalan-numbers-oq-05-oq-02
difficulty: medium
source: catalan-numbers-oq-05-oq-02
created: 2026-07-09T16:43:20-07:00
```
