# Problem: Fibonacci Product-Sum — Alternating and Weighted Variants

**Slug**: fibonacci-identities-oq-05-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent proves the telescoping product-sum identity for consecutive Fibonacci
products $\sum_{k=1}^{n} F_k F_{k+1}$. This problem asks for the two natural
variants listed as its first open question:

1. **Alternating product sum.** Find and prove a closed form for
$$\sum_{k=1}^{n} (-1)^k F_k F_{k+1}.$$

2. **Weighted (linear) product sum.** Find and prove a closed form for
$$\sum_{k=1}^{n} k\, F_k F_{k+1}.$$

Both closed forms should be expressed in terms of Fibonacci numbers $F_m$ (and at
most a linear polynomial in $n$), and proved by induction in Lean 4.

### Plain Language

The parent identity sums consecutive Fibonacci products $F_k F_{k+1}$. Here we
twist the same sum two ways: alternate the sign of each term, and weight each term
by its index $k$. Each variant collapses to a clean expression in Fibonacci
numbers; the goal is to discover the exact form and certify it in Lean.

### Why This Matters

Demonstrates that the same telescoping machinery behind the parent identity is
robust under sign-twisting and linear weighting — a recurring pattern in the
combinatorics of linear recurrences (Cassini / d'Ocagne family).

## Known Results

### What's Already Proven

- `fibonacci-identities-oq-05` (verified, 0-axiom) — base product-sum staircase.
- Mathlib `Nat.fib`, `Nat.fib_add_two`, Cassini/d'Ocagne identities.

### What's Still Open

- The two closed forms above (this problem).

### Our Goal

State both identities over `ℤ` and prove them by `Finset.range` induction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fibonacci-identities-oq-05 | direct parent | telescoping product-sum |
| fibonacci-identities-oq-04-oq-03 | Gibonacci Gelin–Cesàro | recurrence algebra |

## Initial Thoughts

### Potential Approaches

1. **Direct induction**: `Finset.sum_range_succ` + `Nat.fib_add_two`, close step with `ring`.
   - Why it might work: each term is polynomial in shifted Fibonacci values.
   - Risk: discovering the exact closed form first (conjecture from data).

2. **Abel summation** for the weighted sum against the parent's telescoped partials.

### Key Difficulties

- Sign handling forces working over `ℤ` (cast from `Nat.fib`).
- Conjecturing the precise closed form before proving.

### What Would a Proof Need?

- Key lemma: parent product-sum closed form (import or re-derive).
- Numerical conjecture of both forms from first 6–8 partial sums.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Pure `Nat.fib` induction, no transcendental input.
- Mathlib has the full Fibonacci identity API.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Algebra.BigOperators.Fib` / `Nat.fib` — Fibonacci API.

## Metadata

```yaml
tags:
  - number-theory
  - combinatorics
  - fibonacci
related_proofs:
  - fibonacci-identities-oq-05
difficulty: low
source: gallery-gap
created: 2026-06-24
```
