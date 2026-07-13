# Problem: Exponential generating function of the Bell numbers, Σ Bₙxⁿ/n! = exp(eˣ − 1)

**Slug**: bell-numbers-oq-01-oq-01
**Created**: 2026-07-02T02:47:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\sum_{n=0}^{\infty} B_n \frac{x^n}{n!} = e^{\,e^x - 1},
$$

where `Bₙ` is the `n`-th Bell number (the number of partitions of an `n`-element set). Formalize
this exponential generating function (EGF) identity, and derive from it the row-sum recurrence
`B_{n+1} = Σ_{k=0}^{n} C(n,k) Bₖ` (equivalently the Stirling row-sum `Bₙ = Σₖ S(n,k)`).

### Plain Language

The Bell numbers count the ways to partition a set. Their EGF has the famously compact closed form
`exp(eˣ − 1)`. The parent entry (`bell-numbers-oq-01`) establishes the Bell numbers and the
binomial recurrence combinatorially; this open question asks to package that analytically as the
EGF identity and recover the recurrence as the coefficient form of the differential relation
`y' = eˣ y` satisfied by `y = exp(eˣ − 1)`.

### Why This Matters

The EGF is the analytic heart of the theory of Bell numbers and set partitions: it makes Dobiński's
formula, asymptotics, and umbral identities accessible. Formalizing it connects the gallery's
combinatorial Bell-number material to Mathlib's formal power series / exponential machinery and
gives a reusable EGF object.

## Known Results

### What's Already Proven

- Parent `bell-numbers-oq-01` — Bell numbers, the binomial recurrence
  `B_{n+1} = Σ C(n,k) Bₖ`, and finite-sum / induction infrastructure.
- Mathlib `PowerSeries`, `PowerSeries.exp`, and the exponential formula relating EGFs of "connected"
  and "all" structures (`PowerSeries` composition / `exp` of a series with zero constant term).

### What's Still Open

- The EGF identity itself as a Lean statement over `PowerSeries ℚ` (this problem), and the derivation
  of the recurrence from it.

### Our Goal

State `bellEGF = PowerSeries.exp (PowerSeries.exp X - 1)` (over `ℚ`), prove its coefficients are
`Bₙ / n!`, and show the coefficient extraction reproduces the parent's binomial recurrence.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bell-numbers-oq-01 | Parent; Bell numbers and binomial recurrence | combinatorics, induction |
| exponential-generating-function entries (if present) | EGF machinery | formal power series |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Derive from the ODE `y' = eˣ y`.
   - Why it might work: `y = exp(eˣ − 1)` satisfies `y' = eˣ · y`; matching `xⁿ/n!` coefficients on
     both sides gives exactly the binomial recurrence `B_{n+1} = Σ C(n,k) Bₖ`. Mathlib supports
     formal derivatives of `PowerSeries` and `PowerSeries.exp`.
   - Risk: relating `PowerSeries.exp` composition (`exp ∘ (exp X - 1)`) to coefficients may need
     care with the exponential-formula lemmas.

2. **Approach B**: Exponential formula (species) directly.
   - Why it might work: set partitions are "sets of nonempty blocks", so `EGF = exp(EGF of nonempty
     sets) = exp(eˣ − 1)` by the exponential formula.
   - Risk: Mathlib's exponential-formula support may be thinner than the direct ODE route.

### Key Difficulties

- Working over `PowerSeries ℚ` and handling `n!` denominators (division by factorials) cleanly.
- Connecting `PowerSeries.exp (PowerSeries.exp X - 1)` coefficients to the integer Bell numbers.

### What Would a Proof Need?

- Key lemma 1: coefficient/derivative rules for `PowerSeries.exp` (`derivative (exp f) = derivative f * exp f`).
- Key lemma 2: the parent's binomial recurrence to identify coefficients.
- Technical requirements: `PowerSeries`, `PowerSeries.exp`, `PowerSeries.derivative`, `Nat.factorial`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib has `PowerSeries.exp` and formal derivative infrastructure, so the ODE route is viable.
- The parent already supplies the recurrence, which is the coefficient content of the identity.
- Similar EGF identities (e.g. for derangements) have appeared in the gallery.

**Estimated Effort**:
- Exploration: days
- If tractable: days to a week
- If hard: unknown (if the `exp`-composition coefficient lemmas need to be built from scratch)

## References

### Papers
- G. Dobiński (1877) — Dobiński's formula for Bell numbers (context for the EGF).
- Stanley, *Enumerative Combinatorics* Vol. 1 — exponential formula and set-partition EGFs.

### Online Resources
- https://en.wikipedia.org/wiki/Bell_number — EGF `exp(eˣ − 1)` and recurrences.

### Mathlib
- `Mathlib.RingTheory.PowerSeries.WellKnown` — `PowerSeries.exp` and its properties.
- `Mathlib.RingTheory.PowerSeries.Basic` — coefficients and formal derivative.

## Metadata

```yaml
tags:
  - combinatorics
  - bell-numbers
  - stirling-numbers
  - set-partitions
  - generating-functions
  - power-series
related_proofs:
  - bell-numbers-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02T02:47:19-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
