# Problem: erdos-728-factorial-divisibility-oq-04 — extending the #728 techniques to Erdős #729

## Statement

### Plain Language
Open question (generalization) spawned from the gallery proof
`erdos-728-factorial-divisibility`: **how do the techniques of the #728 resolution
extend to related problems like Erdős #729?**

### The two problems
- **Erdős #728** (resolved affirmatively, Jan 2026, GPT-5.2 + Aristotle): for any
  fixed `0 < ε < 1/2` and `C > 0` there are infinitely many triples `(a,b,n)` with
  range constraints and `a + b > n + C log n` satisfying `a! b! ∣ n! (a+b−n)!`.
- **Erdős #729** (resolved by Barreto–Leeham, with a *modification* of the #728
  argument): are there infinitely many `a, b, n` with `a + b > n + C log n` such
  that the denominator of `n! / (a! b!)` contains only primes `≪_C 1`?  Equivalently:
  `a! b! ∣ n!` "ignoring small primes" — for every prime `p ≫_C 1`,
  `v_p(a!) + v_p(b!) ≤ v_p(n!)`.

### The baseline both break
Erdős's elementary theorem: if `a! b! ∣ n!` then `a + b ≤ n + O(log n)`.  Proof uses
the prime `2` alone via Legendre's formula `v₂(m!) = m − s₂(m)`.  #728/#729 show this
`O(log n)` barrier is sharp only because of *small* primes; restricting to large
primes (the carry analysis) lets `a + b` exceed `n + C log n`.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - number-theory
  - combinatorics
  - erdos
  - factorial
  - p-adic
  - ai-solved
```

**Significance**: 6/10
**Tractability**: 5/10

## Why This Matters
Reuses the verified Kummer/Legendre carry-counting infrastructure of the #728
resolution; #729 is the closest cousin and was solved by an explicit modification of
the same method, so it is the most tractable generalization target.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-728-factorial-divisibility | Parent: the resolved #728, supplies `kappa`/`W`/Kummer-carry infrastructure |

## References
- arXiv:2601.07421 — write-up of Aristotle's Lean proof of #728.
- erdosproblems.com/728, /729.
