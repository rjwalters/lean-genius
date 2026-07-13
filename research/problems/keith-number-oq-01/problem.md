# Problem: 14 Is the Smallest Keith Number

**Slug**: keith-number-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $n$ be a positive integer with decimal digits $d_{k-1} d_{k-2}\cdots d_0$
(so $k = \#\text{digits}_{10}(n) \ge 2$). Seed a linear recurrence with these
$k$ digits: $a_0 = d_{k-1}, \dots, a_{k-1} = d_0$ (most-significant digit first),
and for $i \ge k$,
$$
a_i = a_{i-1} + a_{i-2} + \cdots + a_{i-k}
$$
(the sum of the previous $k$ terms). Call $n$ a *Keith number* (or *repfigit*) if
$n$ itself appears as some term $a_i$ of this sequence.

Claim: $14$ is the smallest Keith number. Its digit seed is $1, 4$, generating
$1, 4, 5, 9, 14, \dots$ — and $14$ appears. Moreover no integer $10 \le n \le 13$
is Keith, and single-digit $n$ are excluded ($k \ge 2$ required).

### Plain Language

Take a number, use its digits to start a Fibonacci-like sequence (each new term
is the sum of as many previous terms as the number has digits), and ask whether
the original number ever shows up. $14$ gives $1,4,5,9,14$ — and there it is.
We want a machine-checked proof that $14$ is the first number with this property.

### Why This Matters

Keith numbers tie a number's *digit expansion* to a *linear recurrence on those
digits* — a rare and pretty interaction. Because membership is decided by
iterating the recurrence only until terms exceed $n$, the property is decidable
by a bounded search, making it an excellent `decide`/`Decidable`-instance target
that also exercises `Nat.digits` reasoning.

## Known Results

### What's Already Proven

- Classical enumeration: Keith numbers begin $14, 19, 28, 47, 61, 75, 197, 742,
  1104, \dots$ (OEIS A007629); $14$ is the smallest. They are computationally
  rare (only a few thousand below $10^{20}$).
- No closed form is known; membership is by construction/iteration.

### What's Still Open (engineering)

- No Lean/Mathlib or gallery formalization of Keith numbers or the "smallest = 14"
  fact.

### Our Goal

Formalize the digit-seeded recurrence `keithSeq n : ℕ → ℕ`, define
`IsKeith n := 2 ≤ (Nat.digits 10 n).length ∧ ∃ i, keithSeq n i = n`, give it a
`Decidable` instance via a bounded search (iterate until the term exceeds $n$),
prove `IsKeith 14`, and prove `∀ n, n < 14 → ¬ IsKeith n` to conclude $14$ is the
least Keith number.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| narcissistic-number-oq-01 | digit-expansion property decided by bounded search | `Nat.digits`, decidability |
| kaprekar-constant-oq-01 | digit-driven iteration reaching a target | digit maps, finite iteration |
| sylvester-sequence-oq-01 | reasoning about a recursively defined integer sequence | recurrence induction |

## Initial Thoughts

### Potential Approaches

1. **Bounded-iteration decision procedure**: since the recurrence is strictly
   increasing once terms pass the seed, iterate until $a_i \ge n$ and check
   equality; this gives a terminating, `Decidable` membership test. Then
   `IsKeith 14` and `¬ IsKeith n` for $n < 14$ both fall to `decide`.
   - Why it might work: everything is a finite computation over small numbers.
   - Risk: defining `keithSeq` so it both reduces under `decide` and is easy to
     reason about (a `List`-of-last-$k$-terms fold is convenient).

2. **Explicit witness for 14, exhaustive check below**: exhibit
   $1,4,5,9,14$ directly for $14$; for $10\!\le\! n\!\le\!13$ list the short
   sequences and observe $n$ is skipped (e.g. $13 \to 1,3,4,7,11,18$, jumps over
   $13$).

### Key Difficulties

- Extracting digits in the correct (most-significant-first) order from
  `Nat.digits 10 n` (which is little-endian) — a `.reverse`.
- Phrasing the recurrence as a fold over the last $k$ terms so `decide` evaluates
  and the strict-growth termination bound is clear.

### What Would a Proof Need?

- `keithSeq n : ℕ → ℕ` from the reversed digit seed, summing the previous $k$
- `IsKeith n := 2 ≤ k ∧ ∃ i, keithSeq n i = n`, with a bounded `Decidable` instance
- `IsKeith 14` by `decide`; `∀ n < 14, ¬ IsKeith n` by `decide`/`interval_cases`

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The mathematics is elementary; the work is engineering a clean, `decide`-able
  recurrence and the digit-seed extraction.
- All target numbers are tiny, so computation is trivial once the definition
  reduces.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days (definition + decidability + smallest-is-14).

## References

### Online Resources
- OEIS A007629 (Keith numbers / repfigits): 14, 19, 28, 47, 61, 75, ...
- Keith (1987), "Repfigit numbers", *J. Recreational Math.*

### Mathlib
- `Mathlib.Data.Nat.Digits` — `Nat.digits`, digit-length lemmas (note: digits are
  little-endian, reverse for the seed).
- `Decidable`, `decide`, `interval_cases` — bounded-search decision over small $n$.

## Metadata

```yaml
tags:
  - number-theory
  - digits
  - keith
  - repfigit
  - recurrence
  - decidable
related_proofs:
  - narcissistic-number-oq-01
  - kaprekar-constant-oq-01
  - sylvester-sequence-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
