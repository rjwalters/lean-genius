# Problem: Gelin–Cesàro Identity for Fibonacci Numbers

**Slug**: fibonacci-identities-oq-01-oq-04
**Created**: 2026-07-05T02:36:42-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For all $n \ge 2$,

$$
F_{n-2}\,F_{n-1}\,F_{n+1}\,F_{n+2} \;=\; F_n^{4} - 1,
$$

where $F_k$ denotes the $k$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$, `Nat.fib` in Mathlib).

### Plain Language

Take a Fibonacci number $F_n$ and the four Fibonacci numbers that flank it symmetrically —
the two just below ($F_{n-1}, F_{n-2}$) and the two just above ($F_{n+1}, F_{n+2}$). Their
product is exactly one less than the fourth power of the central term $F_n$. It is a compact
quartic companion to Cassini's identity $F_{n-1}F_{n+1} - F_n^2 = (-1)^n$.

### Why This Matters

The Gelin–Cesàro identity is a classical showcase of how a nonlinear Fibonacci relation collapses
to a clean closed form. Formalizing it exercises the interaction between Cassini/Catalan-type
sign identities and integer-vs-natural arithmetic (the product is $F_n^4 - 1$, so the derivation is
naturally carried out over $\mathbb{Z}$). It rounds out the Cassini family already present in the
gallery (Cassini, Catalan, d'Ocagne) with the last of the four canonical low-order identities.

## Known Results

### What's Already Proven

- **Cassini's identity** $F_{n-1}F_{n+1} - F_n^2 = (-1)^n$ — gallery `fibonacci-identities-oq-01`.
- **Catalan's identity** $F_n^2 - F_{n-r}F_{n+r} = (-1)^{\,n-r}F_r^2$ — gallery
  `fibonacci-identities-oq-01-oq-01`. This is the direct parent lemma.
- Mathlib: `Nat.fib`, `Nat.fib_add_two`, `Nat.fib_add`, `Int.fib` / integer casting lemmas.

### What's Still Open

- Nothing mathematically deep — this is a formalization gap. No Lean statement of the
  Gelin–Cesàro identity exists in the gallery or Mathlib.

### Our Goal

Prove `F_{n-2} * F_{n-1} * F_{n+1} * F_{n+2} = F_n^4 - 1` (stated over `ℤ` for `n ≥ 2`, or with a
`Nat` reformulation `F_{n-2} F_{n-1} F_{n+1} F_{n+2} + 1 = F_n^4` to avoid truncated subtraction),
verified with 0 sorries / 0 axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fibonacci-identities-oq-01 | Cassini ($r=1$ special case) | induction, sign-tracking |
| fibonacci-identities-oq-01-oq-01 | Catalan identity — parent lemma | strong induction / matrix |
| fibonacci-identities-oq-01-oq-02 | d'Ocagne — sibling Cassini-family identity | index shifting |

## Initial Thoughts

### Potential Approaches

1. **Reduce to Catalan (recommended)**: Apply the Catalan identity twice.
   - $r=1$: $F_{n-1}F_{n+1} = F_n^2 + (-1)^n$ (Cassini).
   - $r=2$: $F_{n-2}F_{n+2} = F_n^2 - (-1)^{n}F_2^2 = F_n^2 - (-1)^n$ (since $F_2 = 1$).
   - Multiply: $(F_{n-1}F_{n+1})(F_{n-2}F_{n+2}) = (F_n^2 + (-1)^n)(F_n^2 - (-1)^n) = F_n^4 - 1$.
   - Why it works: both factors already proven; the finish is a difference-of-squares `ring` step.
   - Risk: minimal — index bookkeeping for $n-2$ and the $(-1)^{2n} = 1$ simplification.

2. **Direct strong induction** on the four-term product.
   - Why it might work: self-contained, no dependence on Catalan generality.
   - Risk: messier algebra than Approach 1; more `ring`/`omega` wrangling.

### Key Difficulties

- Natural-number subtraction: work over `ℤ` (`Int.ofNat`/casts) to keep `F_n^4 - 1` honest.
- The $r=2$ Catalan instance needs $F_2 = 1$ substituted and the sign $(-1)^{n-2} = (-1)^n$.

### What Would a Proof Need?

- Catalan's identity available over `ℤ` for $r \in \{1,2\}$ (or reprove the two instances inline).
- A difference-of-squares `ring` closing step.
- Index-arithmetic lemmas for $n-2, n-1, n+1, n+2$ with $n \ge 2$.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Entirely reducible to the already-proven Catalan identity via two instantiations plus `ring`.
- The Cassini family is well-trodden in the gallery; identical machinery applies.
- No new theory, no analysis, purely algebraic manipulation over `ℤ`.

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: under a day

## References

### Papers
- E. Gelin / E. Cesàro, classical Fibonacci identity (late 19th c.) — origin of the name.
- Vajda, *Fibonacci & Lucas Numbers, and the Golden Section* (1989) — Catalan/Cassini family.

### Online Resources
- Standard treatments of Cassini/Catalan/Gelin–Cesàro identities (e.g. Wikipedia "Cassini and Catalan identities").

### Mathlib
- `Mathlib.Combinatorics.Fibonacci` / `Nat.fib` — Fibonacci definitions and recurrences.
- `Nat.fib_add`, `Nat.fib_add_two` — index-shift lemmas for the derivation.

## Metadata

```yaml
tags:
  - number-theory
  - fibonacci
  - identity
related_proofs:
  - fibonacci-identities-oq-01
  - fibonacci-identities-oq-01-oq-01
difficulty: low
source: gallery-gap
created: 2026-07-05T02:36:42-07:00
```

**Significance**: 6/10
**Tractability**: 8/10
