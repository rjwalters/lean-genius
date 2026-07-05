# Problem: Derangement Quotient Recurrence

**Slug**: derangements-convergence-oq-04-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For } n \ge 2,\ (n-1)\mid D(n),\quad \text{and the quotient } q(n) := \frac{D(n)}{n-1} \text{ satisfies } q(n) = D(n-2) + D(n-1).
$$

### Plain Language

The derangement numbers $D(n)$ (permutations with no fixed point) obey the classic
recurrence $D(n) = (n-1)\bigl(D(n-1) + D(n-2)\bigr)$. The parent entry proves the
divisibility $(n-1)\mid D(n)$ for $n \ge 2$. This problem asks to make the quotient
explicit: define $q(n) = D(n)/(n-1)$ and prove the clean second-order identity
$q(n) = D(n-2) + D(n-1)$. Then identify the resulting integer sequence in the OEIS.

### Why This Matters

It upgrades a divisibility statement into an exact structural description of the
cofactor, exhibiting $D(n)/(n-1)$ as itself a sum of two consecutive derangement
numbers — a small but sharp closed form that makes the "$(n-1)$ divides" fact
combinatorially transparent.

## Known Results

### What's Already Proven

- $D(n) = (n-1)(D(n-1) + D(n-2))$ for $n \ge 2$ — standard derangement recurrence (Mathlib `Nat.derangements` / `numDerangements_add_two`).
- $(n-1) \mid D(n)$ for $n \ge 2$ — parent entry `derangements-convergence-oq-04`.
- $D(n) \equiv (-1)^n \pmod n$ — companion congruence from the parent.

### What's Still Open

- The explicit quotient identity $q(n) = D(n-2) + D(n-1)$ has not been formalized.
- OEIS identification and a closed form / generating function for $q(n)$.

### Our Goal

Formalize $q(n) := D(n)/(n-1)$ as a natural number (via the parent divisibility) and
prove $q(n) = D(n-2) + D(n-1)$ directly from the recurrence. Optionally record the
OEIS entry for $q$ in the write-up.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| derangements-convergence-oq-04 | Parent: proves $(n-1)\mid D(n)$ | recurrence, divisibility |
| derangements-convergence-oq-04-oq-02 | Sibling: combined modulus $n(n-1)$ via CRT | CRT, congruences |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Direct algebra on Mathlib's `numDerangements`.
   - Why it might work: `numDerangements (n+2) = (n+1) * (numDerangements (n+1) + numDerangements n)` is definitional/lemma; the quotient identity is then immediate by `Nat.mul_div_cancel_left` after rewriting $n-1$.
   - Risk: index bookkeeping (`n` vs `n+2`) and the `n ≥ 2` guard for natural subtraction.

2. **Approach B**: State over `ℤ` with `q(n) * (n-1) = D(n)` to sidestep `Nat` division.
   - Why it might work: avoids `Nat.sub`/division pitfalls; `linarith`/`ring` friendly.
   - Risk: casting between `ℕ` and `ℤ` for `numDerangements`.

### Key Difficulties

- Natural-number subtraction `n-1` and division require the `n ≥ 2` hypothesis threaded carefully.
- Aligning Mathlib's `numDerangements (n+2)` offset with the `q(n)` indexing.

### What Would a Proof Need?

- Key lemma 1: `numDerangements (n+2) = (n+1) * (numDerangements (n+1) + numDerangements n)`.
- Key lemma 2: divisibility witness `(n-1) ∣ D(n)` (reuse parent) to define `q`.
- Technical requirements: `Nat.mul_div_cancel_left`, or a `q(n)*(n-1)=D(n)` formulation.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- [Reason for assessment] Pure consequence of a recurrence already in Mathlib; a few rewrites.
- [Similar problems that have been solved] The parent divisibility and CRT sibling are both verified 0-axiom.
- [Techniques available in Mathlib] `Nat.numDerangements`, `numDerangements_add_two`, basic `Nat`/`Int` arithmetic.

**Estimated Effort**:
- Exploration: hours
- If tractable: hours to a day
- If hard: n/a

## References

### Papers
- Comtet, *Advanced Combinatorics*, 1974 — derangement recurrences.

### Online Resources
- https://oeis.org — identify $q(n) = D(n-2)+D(n-1)$.

### Mathlib
- `Mathlib.Combinatorics.Derangements.Finite` — `numDerangements` and its recurrence.

## Metadata

```yaml
tags:
  - combinatorics
  - derangements
  - recurrence
related_proofs:
  - derangements-convergence-oq-04
  - derangements-convergence-oq-04-oq-02
difficulty: low
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 7/10
