# Problem: Axiom Elimination for iteratedIntervalIntegral_order_independent

**Slug**: greens-theorem-oq-01-oq-01-oq-01-oq-01
**Created**: 2026-05-06T14:27:30+03:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Can `iteratedIntervalIntegral_order_independent` be proved without the axiom, using
`Mathlib.MeasureTheory.Integral.Marginal.lmarginal_union`?

### Plain Language

The parent proof `greens-theorem-oq-01-oq-01-oq-01` (N-Dimensional Fubini for Iterated
Interval Integrals) was recently completed with 0 sorries. It contains a theorem
`iteratedIntervalIntegral_order_independent` that states: for a continuous function f,
the value of its iterated interval integral does not depend on the order of integration.
This theorem currently may be assumed (axiomatized) rather than proved. The goal is to
eliminate that assumption by leveraging `Mathlib.MeasureTheory.Integral.Marginal.lmarginal_union`
which provides the abstract measure-theoretic machinery for marginal integrals.

### Why This Matters

- Reduces the axiom count in the greens-theorem gallery chain
- Connects the concrete interval integral formulation to Mathlib's abstract measure theory
- Strengthens the formalization toward full verification (currently has leanFile.sorries: 0
  but top-level status fields not yet set)

## Known Results

### What's Already Proven

- `greens-theorem-oq-01-oq-01-oq-01`: N-Dimensional Fubini, 0 sorries — `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01/meta.json`
- `Mathlib.MeasureTheory.Integral.Marginal.lmarginal_union`: marginal integrals on product spaces
- Fubini's theorem: `MeasureTheory.integral_prod` in Mathlib

### What's Still Open

- Whether `lmarginal_union` applies directly or needs adaptation for interval integrals
- Whether the proof is purely definitional or requires new lemmas

### Our Goal

Prove `iteratedIntervalIntegral_order_independent` from first principles (no `axiom` keyword),
using Mathlib's marginal integral library to discharge the order-independence assumption.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| greens-theorem-oq-01-oq-01-oq-01 | Direct parent — proof to extend | Fubini, interval integrals |
| greens-theorem-oq-01-oq-01-oq-02 | Sibling — standalone intervalIntegral_swap | Interval integral commutativity |
| greens-theorem | Original Green's theorem | Differential forms |

## Initial Thoughts

### Potential Approaches

1. **Marginal approach**: Use `lmarginal_union` to reduce to measure-theoretic Fubini
   - Why it might work: direct connection suggested by the OQ text
   - Risk: interval integrals vs abstract measure spaces may need coercion lemmas

2. **Direct Fubini**: Use `MeasureTheory.integral_prod` + continuity to swap order
   - Why it might work: continuous functions satisfy Tonelli/Fubini hypotheses
   - Risk: need to connect `intervalIntegral` to `integral` on product

### Key Difficulties

- Bridging `intervalIntegral` (Lean specific) to abstract `lmarginal`
- Multiple orderings (n! permutations for n-dimensional case)

### What Would a Proof Need?

- Key lemma: `iteratedIntervalIntegral_eq_integral_prod` (connect to measure theory)
- Mathlib's `lmarginal_union`: `Mathlib.MeasureTheory.Integral.Marginal`
- Continuity hypotheses to invoke Fubini

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Parent proof already completed (0 sorries), so the context is well-understood
- Mathlib has strong Fubini support
- The specific OQ text points to an exact Mathlib lemma (`lmarginal_union`)
- Connecting interval integrals to abstract measure theory may require some bridging lemmas

**Estimated Effort**:
- Exploration: 1-2 hours (read parent proof, find Mathlib lemmas)
- If tractable: 2-4 days

## References

### Mathlib
- `Mathlib.MeasureTheory.Integral.Marginal` — lmarginal_union and marginal integrals
- `Mathlib.MeasureTheory.Integral.SetIntegral` — Fubini-type theorems
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` — intervalIntegral API

## Metadata

```yaml
tags:
  - analysis
  - measure-theory
  - interval-integrals
  - axiom-elimination
  - fubini
related_proofs:
  - greens-theorem-oq-01-oq-01-oq-01
  - greens-theorem-oq-01-oq-01-oq-02
difficulty: medium
source: gallery-gap
created: 2026-05-06T14:27:30+03:00
```

**Significance**: 6/10
**Tractability**: 6/10
