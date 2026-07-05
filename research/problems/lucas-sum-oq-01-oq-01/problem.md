# Problem: Even/Odd-Indexed and Alternating Lucas Partial Sums

**Slug**: lucas-sum-oq-01-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{k=1}^{n} L_{2k} = L_{2n+1} - 1,\qquad
\sum_{k=1}^{n} L_{2k-1} = L_{2n} - 2,\qquad
\sum_{k=0}^{n} (-1)^k L_k = (-1)^n F_{2n+1} \cdot(\pm 1)\ \text{(closed form)}.
$$

(The alternating sum's exact closed form is to be pinned down during OBSERVE; the
even/odd-indexed sums are as stated.)

### Plain Language

The parent entry sums the Lucas numbers $\sum_{k} L_k$ by a subtraction-free
telescoping engine. This problem applies the same engine to the even-indexed sum
$\sum L_{2k}$, the odd-indexed sum $\sum L_{2k-1}$, and the alternating sum
$\sum (-1)^k L_k$, giving each a Lucas/Fibonacci closed form.

### Why This Matters

These are the standard companion identities to the plain Lucas sum and complete the
"partial-sum" family for Lucas numbers, mirroring the Fibonacci partial-sum identities
and exercising the same telescoping technique in three new index patterns.

## Known Results

### What's Already Proven

- $\sum_{k=1}^{n} L_k = L_{n+2} - 3$ (or the entry's exact form) — parent `lucas-sum-oq-01`.
- Lucas recurrence $L_{n+2} = L_{n+1} + L_n$, $L_0 = 2$, $L_1 = 1$ — Mathlib `Nat.lucas` / defined via `Nat.fib`.
- Bridge $L_{n+1} = F_n + F_{n+2}$ relating Lucas and Fibonacci.

### What's Still Open

- The even-indexed, odd-indexed, and alternating Lucas partial sums as verified identities.

### Our Goal

Formalize $\sum_{k=1}^{n} L_{2k} = L_{2n+1} - 1$, $\sum_{k=1}^{n} L_{2k-1} = L_{2n} - 2$,
and the alternating sum's closed form, by telescoping the Lucas recurrence.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lucas-sum-oq-01 | Parent: plain Lucas partial sum by telescoping | recurrence, `Finset.sum` telescoping |
| lucas-sum-oq-01-oq-02 | Sibling in the Lucas-sum family | telescoping, Lucas identities |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Induction on $n$ with the Lucas recurrence.
   - Why it might work: each identity's inductive step is one application of $L_{n+2}=L_{n+1}+L_n$; `omega`/`ring` closes the arithmetic.
   - Risk: even/odd index reindexing (`2k`, `2k-1`) and the `Finset.range` vs `Finset.Icc` bookkeeping.

2. **Approach B**: Telescoping via `Finset.sum_range_succ` and a difference identity $L_{2k} = A_{k+1}-A_k$.
   - Why it might work: subtraction-free, mirrors the parent engine directly.
   - Risk: finding the right telescoping term for the alternating case.

### Key Difficulties

- Reindexing even/odd subsequences within Mathlib `Finset` sums.
- Pinning the exact closed form of the alternating sum (parity split).

### What Would a Proof Need?

- Key lemma 1: Lucas recurrence and base values in the chosen Mathlib encoding.
- Key lemma 2: telescoping difference for each index pattern.
- Technical requirements: `Finset.sum_range_succ`, induction, `omega`/`ring`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- [Reason for assessment] Direct reuse of the parent's telescoping technique on new index patterns.
- [Similar problems that have been solved] The parent Lucas sum and many Fibonacci partial-sum identities are formalized.
- [Techniques available in Mathlib] `Nat.fib`/Lucas API, `Finset.sum_range_succ`, induction.

**Estimated Effort**:
- Exploration: hours
- If tractable: hours to a day
- If hard: n/a

## References

### Papers
- Koshy, *Fibonacci and Lucas Numbers with Applications*, 2001 — partial-sum identities.

### Online Resources
- https://en.wikipedia.org/wiki/Lucas_number — summation identities.

### Mathlib
- `Mathlib.Combinatorics.Fibonacci` / `Nat.fib` — Fibonacci/Lucas recurrences.

## Metadata

```yaml
tags:
  - number-theory
  - lucas-numbers
  - summation
related_proofs:
  - lucas-sum-oq-01
  - lucas-sum-oq-01-oq-02
difficulty: low
source: gallery-gap
created: 2026-07-02
```

**Significance**: 5/10
**Tractability**: 7/10
