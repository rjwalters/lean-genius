# Problem: Narcissistic (Armstrong) Numbers Form a Finite Set

**Slug**: narcissistic-number-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a positive integer $m$ with $k = \#\text{digits}_{10}(m)$ decimal digits
$d_0,\dots,d_{k-1}$, call $m$ *narcissistic* if
$$
m = \sum_{i=0}^{k-1} d_i^{\,k}.
$$
The set of narcissistic numbers is finite. In particular, if $m$ has $k$ digits
then $m \ge 10^{k-1}$ while $\sum d_i^k \le k\cdot 9^k$, and $k\cdot 9^k < 10^{k-1}$
for all $k \ge 61$, so every narcissistic number has at most $60$ digits.

### Plain Language

A number like $153 = 1^3 + 5^3 + 3^3$ or $8208 = 8^4+2^4+0^4+8^4$ reproduces
itself when each digit is raised to the power equal to the digit count. We want a
machine-checked proof that only finitely many such numbers exist, by bounding the
digit count, plus verification of the small base-10 cases.

### Why This Matters

A crisp finiteness theorem from a growth-rate comparison ($k\cdot 9^k$ vs
$10^{k-1}$). Good showcase of digit-expansion reasoning and a bounded-search
decision procedure.

## Known Results

### What's Already Proven

- There are exactly 88 base-10 narcissistic numbers (classical enumeration); the
  largest is the 39-digit $115132219018763992565095597973971522401$.
- The finiteness bound is elementary; the count is by exhaustive search.

### What's Still Open (engineering)

- No Lean/Mathlib or gallery formalization of the digit-power-sum map's
  finiteness.

### Our Goal

Formalize the digit-power-sum map $S_k(m) = \sum d_i^k$, prove the key inequality
$k \cdot 9^k < 10^{k-1}$ for $k \ge 61$ (hence narcissistic numbers have $< 61$
digits), and conclude finiteness. Optionally verify small cases (1–9 trivially;
153, 370, 371, 407 for $k=3$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| kaprekar-constant-oq-01 | digit-map fixed points, decidability | digit expansion, finite search |
| perfect-numbers | finite arithmetic characterization | divisor sums |

## Initial Thoughts

### Potential Approaches

1. **Digit-count bound + finiteness**: prove $m$ narcissistic $\Rightarrow$
   digits$(m) \le 60$ via the growth inequality, so the set injects into a finite
   range; conclude `Set.Finite`.
   - Why it might work: inequality is provable by induction / `Nat` arithmetic.
   - Risk: the inequality $k\cdot9^k < 10^{k-1}$ needs a clean induction step.

2. **Decidable small-case enumeration** for fixed $k$ (e.g. $k=3$) to exhibit the
   classical examples.

### Key Difficulties

- Relating `Nat.digits 10 m` length to the magnitude bound $10^{k-1} \le m$.
- Inductive proof of the exponential inequality.

### What Would a Proof Need?

- `S k m := ((Nat.digits 10 m).map (· ^ k)).sum`
- Lemma: `(Nat.digits 10 m).length = k → 10^(k-1) ≤ m`
- Lemma: `k ≥ 61 → k * 9^k < 10^(k-1)`
- Conclusion: `{m | narcissistic m}.Finite`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Finiteness is a clean growth-rate argument; Mathlib has `Nat.digits` API.
- Full enumeration of all 88 is heavier; scope can be limited to finiteness +
  small cases.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days (finiteness); enumeration is optional/longer.

## References

### Online Resources
- OEIS A005188 (narcissistic numbers) — full list.

### Mathlib
- `Mathlib.Data.Nat.Digits` — `Nat.digits`, `Nat.digits_lt_base`, length lemmas.
- `Set.Finite`, `Finset` — finiteness packaging.

## Metadata

```yaml
tags:
  - number-theory
  - digits
  - narcissistic
  - armstrong
  - fixed-point
  - decidable
related_proofs:
  - kaprekar-constant-oq-01
  - perfect-numbers
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
