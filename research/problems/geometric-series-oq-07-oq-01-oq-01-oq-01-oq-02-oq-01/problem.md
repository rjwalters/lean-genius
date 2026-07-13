# Problem: Eulerian Numbers — Non-negativity and Descent Count of the Alternating Binomial Sum

**Slug**: geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
A(n,k) \;=\; \sum_{i=0}^{k} (-1)^{i}\binom{n+1}{i}(k+1-i)^{n} \;\geq\; 0,
$$
and $A(n,k)$ equals the number of permutations of $\{1,\dots,n\}$ with exactly $k$ descents (the Eulerian number $\left\langle {n \atop k} \right\rangle$).

### Plain Language

The alternating binomial sum on the left is the closed-form Worpitzky/inclusion–exclusion expression for the Eulerian number $\left\langle {n \atop k}\right\rangle$. Two things are claimed: (1) the sum is non-negative — not obvious from its alternating form — and (2) it counts exactly the permutations of $\{1,\dots,n\}$ having $k$ descents (positions $i$ with $\sigma(i) > \sigma(i+1)$). The non-negativity follows from the combinatorial interpretation, tying the integer inclusion–exclusion count proved in the parent entry to the surjection / cell-count model.

### Why This Matters

Eulerian numbers are central to combinatorics (descent statistics, the Worpitzky identity, the Eulerian polynomial generating function) and connect to the geometry of the permutohedron and to interpolation. Proving the closed-form sum is non-negative and matches the descent count makes the combinatorial meaning of an a-priori-signed expression rigorous in Lean.

## Known Results

### What's Already Proven

- Parent `geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02` proves the integer inclusion–exclusion count (the explicit alternating-sum formula).
- Classical: the Worpitzky identity and the descent-count interpretation of Eulerian numbers.
- Mathlib does not currently carry a full Eulerian-number development.

### What's Still Open

- A Lean proof that the alternating sum is $\geq 0$.
- The bijection / counting equality with permutations having exactly $k$ descents.

### Our Goal

Prove $A(n,k) \geq 0$ and that $A(n,k)$ equals $|\{\sigma \in S_n : \mathrm{des}(\sigma) = k\}|$, connecting the formula proved by the parent to the descent statistic.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02 | Direct parent: closed-form alternating sum | inclusion–exclusion |
| combinations-formula-oq-05-oq-01 | Alternating binomial row sums | telescoping / binomial identities |

## Initial Thoughts

### Potential Approaches

1. **Combinatorial bijection**: Define descents on `Equiv.Perm (Fin n)`, count permutations with $k$ descents, and show this equals $A(n,k)$ via the surjection model; non-negativity is then immediate.
   - Why it might work: non-negativity is free once the count is established.
   - Risk: setting up descent statistics and the surjection counting in Lean is substantial.

2. **Recurrence**: Prove the Eulerian recurrence $A(n,k) = (k+1)A(n-1,k) + (n-k)A(n-1,k-1)$ from the sum, then induct for non-negativity.
   - Why it might work: keeps everything algebraic; non-negativity by induction.
   - Risk: matching the recurrence to the descent count still needs a combinatorial step.

### Key Difficulties

- Formalizing the descent statistic on permutations and its distribution.
- Reconciling the signed closed form with a manifestly non-negative count.

### What Would a Proof Need?

- Key lemma: Eulerian recurrence from the alternating sum.
- Key lemma: descent-count = $A(n,k)$ (Worpitzky / surjection model).
- Technical requirements: `Finset` counting over `Equiv.Perm`, binomial identities.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent already proves the closed-form identity, so the algebra is in place.
- The recurrence route gives non-negativity by a short induction.
- The full descent-count bijection is the harder half; the non-negativity goal alone is quite tractable.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: several days (non-negativity sooner, descent count later)

## References

### Papers
- Worpitzky, 1883 — the Worpitzky identity for Eulerian numbers.
- Graham, Knuth, Patashnik, "Concrete Mathematics" — Eulerian numbers and descents.

### Mathlib
- `Mathlib.Combinatorics` and `Mathlib.GroupTheory.Perm` — permutations and descents.
- `Mathlib.Data.Nat.Choose` — binomial coefficient identities.

## Metadata

```yaml
tags:
  - combinatorics
  - eulerian-numbers
  - descents
related_proofs:
  - geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02
  - combinations-formula-oq-05-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
