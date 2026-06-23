# Problem: Thomae's Function — Riemann Integrability via Lebesgue's Criterion

**Slug**: lebesgue-measure-oq-01-oq-01-oq-01
**Created**: 2026-04-21T22:19:23+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Formalize that Thomae's function $f : [0,1] \to \mathbb{R}$ is Riemann integrable via Lebesgue's criterion:

$$f(x) = \begin{cases} 1/q & \text{if } x = p/q \text{ in lowest terms} \\ 0 & \text{if } x \in \mathbb{R} \setminus \mathbb{Q} \end{cases}$$

**Lebesgue's criterion**: A bounded function on $[a,b]$ is Riemann integrable iff its set of discontinuities has Lebesgue measure zero.

The set of discontinuities of Thomae's function is exactly $\mathbb{Q} \cap [0,1]$, which is countable, hence measure zero. Therefore $f$ is Riemann integrable with $\int_0^1 f \, dx = 0$.

### Plain Language

Thomae's function is famously continuous at every irrational and discontinuous at every rational. Lebesgue's criterion says: Riemann integrability is equivalent to continuity almost everywhere. Since rationals form a measure-zero set, Thomae's function is Riemann integrable. This problem formalizes this argument in Lean 4 using Mathlib's measure theory.

### Why This Matters

- Bridges the Riemann and Lebesgue theories in a pedagogically important example
- Demonstrates `MeasureTheory.Measure.countable_zero` and related Mathlib lemmas in action
- The gallery entry `lebesgue-measure-oq-01-oq-01` already formalizes the Lebesgue integral; this extends it to Riemann integrability

## Known Results

### What's Already Proven

- In gallery `lebesgue-measure-oq-01-oq-01`: Thomae's function has Lebesgue integral zero
- Mathlib: `MeasureTheory.Measure.countable_zero` — countable sets have measure zero
- Mathlib: Lebesgue's criterion for interval integrability
- Rationals are countable: `Rat.countable` in Mathlib

### What's Still Open

- Formal proof connecting discontinuity set with countability → measure zero → Riemann integrable

### Our Goal

Prove `IntervalIntegrable thomae MeasureTheory.volume 0 1` by applying Lebesgue's criterion: bounded function + measure-zero discontinuity set ⟹ Riemann integrable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lebesgue-measure-oq-01-oq-01 | Direct parent — Lebesgue integral of Thomae | measure-zero, ae-equality |
| lebesgue-measure-oq-01 | Lebesgue integral foundations | MeasureTheory |

## Initial Thoughts

### Potential Approaches

1. **Direct via Lebesgue criterion**: Use Mathlib's `intervalIntegrable_of_ae_continuousOn` or the criterion that `f` is Riemann integrable iff its discontinuity set is null.
   - Why it might work: Mathlib has the Lebesgue criterion for interval integrability
   - Risk: The exact Mathlib lemma name and hypotheses need to be found

2. **Squeeze from above**: Define step functions above Thomae's function converging to 0.
   - Why it might work: Avoids the criterion and uses basic integral estimates
   - Risk: More work but more elementary

### Key Difficulties

- Finding the right Mathlib lemma for "bounded + ae-continuous → Riemann integrable"
- Connecting `RiemannIntegral` with Mathlib's `intervalIntegral`
- Formally establishing discontinuities of Thomae's function are exactly `ℚ ∩ [0,1]`

### What Would a Proof Need?

- `Set.Countable.measure_zero` or `MeasureTheory.Measure.countable_zero`
- `MeasureTheory.intervalIntegrable_of_ae_continuousOn` or similar
- Thomae's function definition and its continuity-at-irrationals proof from gallery

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is clean: countable → measure zero → Riemann integrable
- Mathlib has all the components; the challenge is assembling them correctly
- Gallery entry `lebesgue-measure-oq-01-oq-01` provides the Lean 4 definition

## References

### Mathlib
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` — Riemann integral equivalence
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — measure of countable sets
- `Mathlib.Topology.Order.Basic` — continuity criteria

## Metadata

```yaml
tags:
  - measure-theory
  - lebesgue-integral
  - real-analysis
  - thomae-function
  - riemann-integral
  - almost-everywhere
related_proofs:
  - lebesgue-measure-oq-01-oq-01
  - lebesgue-measure-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-21T22:19:23+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
