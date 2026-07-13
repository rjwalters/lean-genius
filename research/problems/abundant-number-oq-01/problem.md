# Problem: 12 Is the Smallest Abundant Number

**Slug**: abundant-number-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a positive integer $n$ let $\sigma(n) = \sum_{d \mid n} d$ be the sum of its
divisors. Call $n$ *abundant* if $\sigma(n) > 2n$ (equivalently, the sum of its
*proper* divisors exceeds $n$). Then:

1. $12$ is abundant: $\sigma(12) = 1+2+3+4+6+12 = 28 > 24 = 2\cdot 12$.
2. No integer $1 \le n \le 11$ is abundant; hence $12$ is the **smallest**
   abundant number.
3. There are infinitely many abundant numbers: every multiple $6k$ with $k \ge 2$
   is abundant, so abundance is not a finite phenomenon.

### Plain Language

A number is "abundant" when its divisors (other than itself) add up to more than
the number. For example $12$'s proper divisors $1,2,3,4,6$ sum to $16 > 12$. We
want a machine-checked proof that $12$ is the first such number, every smaller
number falls short, and abundant numbers never run out.

### Why This Matters

Abundant numbers are the third class in the classical perfect/deficient/abundant
trichotomy ($\sigma(n)$ versus $2n$). A crisp "smallest example + infinitude"
theorem is an ideal `decide`-style bounded-search result that also exercises
Mathlib's `Nat.sigma`/`ArithmeticFunction.sigma` divisor-sum API. It complements
the existing perfect-number gallery entries.

## Known Results

### What's Already Proven

- Classical: the smallest abundant number is $12$; the smallest *odd* abundant
  number is $945$. The natural density of abundant numbers is known to be
  $\approx 0.2476$ (Behrend / Davenport), but that is far deeper than this task.
- Mathlib has `Nat.sigma` / `ArithmeticFunction.sigma 1` and `Nat.divisors`.

### What's Still Open (engineering)

- No Lean/Mathlib or gallery formalization identifying $12$ as the least abundant
  number, nor an explicit infinitude witness.

### Our Goal

Define `Abundant n := sigma n > 2 * n` (using `Nat.sigma 1` or a `Finset`
divisor-sum), prove `Abundant 12`, prove `∀ n, 1 ≤ n → n ≤ 11 → ¬ Abundant n`
(a finite `decide`/`interval_cases` check), conclude $12$ is least, and prove
`∀ k, 2 ≤ k → Abundant (6 * k)` for infinitude.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| perfect-numbers-oq-03 | same $\sigma(n)$ vs $2n$ divisor-sum framework | divisor sums, `Nat.sigma` |
| narcissistic-number-oq-01 | bounded-search decision over small $n$ | `decide`, `interval_cases` |
| kaprekar-constant-oq-01 | fixed/threshold property by finite check | decidability |

## Initial Thoughts

### Potential Approaches

1. **Direct divisor-sum + interval check**: prove `Abundant 12` by `decide`
   (or by computing `Nat.divisors 12`), and `¬ Abundant n` for `n ≤ 11` via
   `interval_cases n <;> decide`.
   - Why it might work: everything is a finite, decidable computation.
   - Risk: choosing the cleanest `sigma`/divisor-sum definition so `decide`
     reduces efficiently.

2. **Infinitude via multiples of 6**: show $\sigma(6k) \ge 1 + 2 + 3 + k + 2k + 3k
   + 6k$ for $k \ge 2$ with these divisors distinct, giving $\sigma(6k) > 12k$.
   A clean sufficient condition is $6 \mid n \Rightarrow$ proper divisors include
   $\{1,2,3,n/6,n/3,n/2\}$ summing past $n$.
   - Risk: handling small overlaps when $k = 1$ (excluded) and proving
     distinctness.

### Key Difficulties

- Picking a `sigma` definition that both `decide`s for $12$ and supports the
  general multiple-of-6 lower bound.
- Establishing divisor distinctness in the infinitude lemma without heavy
  divisor-set manipulation.

### What Would a Proof Need?

- `def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d` (or `Nat.sigma 1 n`)
- `Abundant n := 2 * n < sigma n`
- `Abundant 12` and `∀ n ≤ 11, ¬ Abundant n` ⟹ least element
- `∀ k ≥ 2, Abundant (6 * k)` ⟹ `{n | Abundant n}.Infinite`

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The "smallest = 12" half is a pure finite decision (`interval_cases`/`decide`).
- The infinitude half is a short divisor-sum lower bound; Mathlib's
  `Nat.sigma`/`Nat.divisors` lemmas supply the needed API.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days (both halves).

## References

### Online Resources
- OEIS A005101 (abundant numbers): 12, 18, 20, 24, 30, ...
- OEIS A005231 (odd abundant numbers): 945, 1575, ...

### Mathlib
- `Mathlib.NumberTheory.Divisors` — `Nat.divisors`, `Nat.sigma`, divisor-sum lemmas.
- `Mathlib.NumberTheory.ArithmeticFunction` — `ArithmeticFunction.sigma`.
- `Set.Infinite` — packaging infinitude from an injective family of witnesses.

## Metadata

```yaml
tags:
  - number-theory
  - divisor-sum
  - abundant
  - sigma
  - decidable
related_proofs:
  - perfect-numbers-oq-03
  - narcissistic-number-oq-01
  - kaprekar-constant-oq-01
difficulty: low
source: gallery-gap
created: 2026-06-16
```
