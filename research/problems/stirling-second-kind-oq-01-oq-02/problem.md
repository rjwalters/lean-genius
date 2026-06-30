# Problem: The General Finite-Difference Formula for Stirling Numbers S(n,k)

**Slug**: stirling-second-kind-oq-01-oq-02
**Created**: 2026-06-23
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
S(n,k) \;=\; \frac{1}{k!}\sum_{j=0}^{k} (-1)^j \binom{k}{j}\,(k-j)^n,
$$

equivalently the integer identity (clearing the factorial)

$$
k!\,S(n,k) \;=\; \sum_{j=0}^{k} (-1)^j \binom{k}{j}\,(k-j)^n,
$$

and the specialization recovering the parent's two-block column

$$
S(n,2) = 2^{n-1} - 1 \quad (n \ge 1).
$$

### Plain Language

The Stirling number of the second kind $S(n,k)$ counts partitions of an
$n$-element set into exactly $k$ non-empty blocks. The parent entry
(`stirling-second-kind-oq-01`) proved the single column $S(n,2) = 2^{n-1} - 1$.
We want the general closed form: an inclusion–exclusion (finite-difference) sum
that gives $S(n,k)$ for all $k$, and we want to show it collapses to the parent's
formula when $k = 2$.

### Why This Matters

The finite-difference formula is the canonical closed form for $S(n,k)$ and the
standard bridge between the combinatorial definition (set partitions) and the
analytic one (surjection counting). Formalizing it provides a reusable surjection-
counting / inclusion–exclusion identity and validates the parent column as a true
special case rather than an isolated computation.

## Known Results

### What's Already Proven

- `stirling-second-kind-oq-01` (parent) — $S(n,2) = 2^{n-1} - 1$.
- Mathlib `Nat.stirling` / `stirlingSecond` API (if present) or the surjection
  count $k!\,S(n,k) = $ number of surjections $[n] \twoheadrightarrow [k]$.
- Inclusion–exclusion over `Finset` and the binomial theorem
  (`Finset.sum_range_choose_mul_pow`, `Int.alternating_sum_range_choose`).

### What's Still Open

- A Lean statement and proof of $k!\,S(n,k) = \sum_j (-1)^j \binom{k}{j}(k-j)^n$.
- The reduction showing this recovers $S(n,2) = 2^{n-1} - 1$.

### Our Goal

Formalize the integer (factorial-cleared) finite-difference identity to avoid
rational division, then derive the $k = 2$ column to reconnect with the parent.
Decide whether to define $S(n,k)$ via surjection counts or via Mathlib's existing
Stirling API, and prove the identity accordingly.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| stirling-second-kind-oq-01 | Parent; the $k=2$ column this generalizes | recurrence, induction |
| binomial-theorem (and oq descendants) | Supplies the alternating binomial sum machinery | `Finset` binomial identities |

## Initial Thoughts

### Potential Approaches

1. **Surjection-count route**: Use $k!\,S(n,k) = |\text{Surj}([n],[k])|$ and prove
   $|\text{Surj}([n],[k])| = \sum_j (-1)^j \binom{k}{j}(k-j)^n$ by inclusion–exclusion
   over the $k$ "missed value" events. Risk: assembling the inclusion–exclusion sum
   in Mathlib's `Finset` framework.

2. **Direct induction on the recurrence** $S(n+1,k) = k\,S(n,k) + S(n,k-1)$, matching
   it against the difference of the RHS sum. Risk: index shuffling in the sum.

### Key Difficulties

- Avoiding rational/`ℚ` division — work with the factorial-cleared integer form.
- The $(k-j)^n$ term and the $k=0$ / $n=0$ boundary conventions.

### What Would a Proof Need?

- Key lemma 1: inclusion–exclusion surjection count, or the recurrence match.
- Key lemma 2: $\sum_{j=0}^{2}(-1)^j\binom{2}{j}(2-j)^n = 2^n - 2 = 2(2^{n-1}-1)$.
- Technical requirements: `Finset.sum`, `Nat.choose`, alternating-sign sums.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Inclusion–exclusion and binomial sums are well supported in Mathlib.
- The $k=2$ reduction is an elementary computation.
- Main risk is plumbing the surjection inclusion–exclusion, not new mathematics.

**Estimated Effort**:
- Exploration: hours to a day
- If tractable: 2–5 days
- If hard: unknown (if the surjection count needs to be built from scratch)

## References

### Papers
- Graham, Knuth, Patashnik, *Concrete Mathematics* — Stirling numbers and the finite-difference formula.

### Online Resources
- Standard inclusion–exclusion derivation of surjection counts.

### Mathlib
- `Mathlib.Combinatorics` Stirling/partition API and `Fintype.card` of surjections.
- `Mathlib.Algebra.BigOperators` — `Finset.sum`, alternating binomial identities.

## Metadata

```yaml
tags:
  - combinatorics
  - stirling-numbers
  - set-partitions
  - inclusion-exclusion
related_proofs:
  - stirling-second-kind-oq-01
  - binomial-theorem
difficulty: medium
source: proof-suggestion
created: 2026-06-23
```
