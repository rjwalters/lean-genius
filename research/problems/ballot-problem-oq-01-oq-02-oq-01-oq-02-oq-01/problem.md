# Problem: Uniform Fiber Transfer via MeasureTheory.Measure.map

**Slug**: ballot-problem-oq-01-oq-02-oq-01-oq-02-oq-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $f : A \to T$ be a measurable surjection between finite (or measurable) sets all of whose fibers have equal cardinality $c$. Then pushing the restricted counting measure along $f$ scales it by $c$:
$$
\bigl(\operatorname{Measure.count}\restriction A\bigr).\mathrm{map}\, f \;=\; c \cdot \bigl(\operatorname{Measure.count}\restriction T\bigr),
$$
and consequently the induced uniform probability measure `uniformOn A` pushes forward to `uniformOn T`.

### Plain Language

The parent entry ("General Uniform Fiber Transfer") proves, event by event, that an equal-fiber surjection preserves the uniform distribution — it transfers `uniformOn` on the domain to `uniformOn` on the codomain. This problem asks whether that fact can be lifted to the clean, structural statement about `MeasureTheory.Measure.map`: rather than checking each event, express the whole transfer as a single pushforward identity for `Measure.count` restricted to $A$ and $T$.

### Why This Matters

Equal-fiber counting arguments underlie the reflection/counting proofs of the ballot problem and many combinatorial-probability identities. A one-line `Measure.map` formulation is far more reusable than per-event equalities: it plugs directly into Mathlib's measure-theoretic machinery (change of variables, expectation transport) and makes the ballot-problem formalization compose with the general theory instead of re-deriving transfers by hand.

## Known Results

### What's Already Proven

- Event-wise uniform fiber transfer: `uniformOn A` maps to `uniformOn T` under an equal-fiber surjection — parent `ballot-problem-oq-01-oq-02-oq-01-oq-02`.
- `Measure.count` and its restriction API — `Mathlib.MeasureTheory.Measure.Count`.
- `Measure.map` pushforward and its behavior on measurable functions — `Mathlib.MeasureTheory.Measure.Map`.
- `uniformOn` (formerly `condCount`) as normalized restricted counting measure.

### What's Still Open

- The structural identity `(Measure.count.restrict A).map f = c • Measure.count.restrict T` for equal-fiber $f$.
- The corollary that `uniformOn A` maps to `uniformOn T` derived from that identity rather than event-wise.

### Our Goal

Prove the `Measure.map` pushforward identity for equal-fiber measurable surjections and recover the parent's uniform-transfer statement as a normalization corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ballot-problem-oq-01-oq-02-oq-01-oq-02 | Parent: event-wise uniform transfer | `uniformOn`, fiber cardinality |
| ballot-problem-oq-01-oq-02-oq-01 | Fiber-transfer setup | equal-fiber surjection, counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — evaluate on singletons then extend**: Compute both sides on singletons $\{t\}$: the pushforward mass at $t$ is $\operatorname{count}(f^{-1}\{t\} \cap A) = c$, matching $c \cdot \operatorname{count}\{t\}$. Extend to all measurable sets by countable additivity / the fact that counting measure is determined by its values on singletons.
   - Why it might work: `Measure.count` is a sum of Diracs, so `map` commutes with the sum and each fiber contributes exactly $c$.
   - Risk: Mathlib's `Measure.map` requires measurability of $f$; on general measurable spaces the singleton argument needs `MeasurableSingletonClass`.

2. **Approach B — via `Measure.map_apply` on preimages**: For measurable $S \subseteq T$, `(count.restrict A).map f S = count (A ∩ f⁻¹ S) = c * count S` using the equal-fiber hypothesis summed over $S$.
   - Why it might work: directly uses `Measure.map_apply` and additivity over the fibers of $S$.
   - Risk: summing fiber cardinalities over an arbitrary (possibly infinite) measurable $S$ needs `tsum` bookkeeping.

### Key Difficulties

- Measurability side-conditions for `Measure.map` (needs $f$ measurable, likely `MeasurableSingletonClass` on $T$).
- Turning "every fiber has cardinality $c$" into a summed identity Mathlib can discharge with `tsum`/`Finset.sum`.

### What Would a Proof Need?

- Key lemma 1: `(Measure.count.restrict A) (f⁻¹ S) = c * Measure.count S` for measurable $S \subseteq T$, from equal fibers.
- Key lemma 2: `Measure.map_apply` reduces the pushforward to preimage measure, closing the identity.
- Technical requirements: `MeasurableSingletonClass`, `Measure.count` as a sum of Diracs, `uniformOn` normalization.

## Tractability Assessment

**Difficulty**: Medium (leaning tractable)

**Justification**:
- The mathematical content is already validated event-wise in the parent; this is a reformulation into Mathlib's canonical `Measure.map` idiom.
- `Measure.count` and `Measure.map` both have solid Mathlib APIs.
- Main friction is measurability plumbing and `tsum` summation, not deep mathematics.

**Estimated Effort**:
- Exploration: half a day to a day mapping `Measure.count` / `Measure.map` lemmas.
- If tractable: 2–4 days for the pushforward identity plus the `uniformOn` corollary.
- If hard: only if infinite-support measurability cases prove awkward.

## References

### Papers
- Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1 — ballot problem and reflection/counting arguments.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/ — `MeasureTheory.Measure.count`, `MeasureTheory.Measure.map`, `uniformOn`.

### Mathlib
- `Mathlib.MeasureTheory.Measure.Count` — counting measure.
- `Mathlib.MeasureTheory.Measure.Map` — pushforward `Measure.map`, `Measure.map_apply`.
- `Mathlib.Probability.UniformOn` — uniform distribution on finite sets.

## Metadata

```yaml
tags:
  - probability
  - combinatorics
  - ballot-problem
  - measure-theory
  - fiber-transfer
related_proofs:
  - ballot-problem-oq-01-oq-02-oq-01-oq-02
  - ballot-problem-oq-01-oq-02-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
