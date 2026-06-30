# Problem: Make the Polygonal Buffon's Noodle Theorem Axiom-Free

**Slug**: buffons-noodle-oq-02
**Created**: 2026-06-19T17:27:54-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a polygonal noodle composed of straight segments of lengths $\ell_1, \dots, \ell_k$ dropped on a
floor ruled with parallel lines distance $d$ apart (segments shorter than $d$), the expected number
of line crossings is

$$
\mathbb{E}[\text{crossings}] = \sum_{i=1}^{k} p(\ell_i), \qquad p(\ell) = \frac{2\ell}{\pi d},
$$

where $p(\ell)$ is the single-segment (Buffon's Needle) crossing probability. The current gallery
entry takes $p(\ell)$ — `segmentCrossingProb` — as a **definitional/axiomatized input**. The goal is
to **derive** $p(\ell) = \tfrac{2\ell}{\pi d}$ from the registered measure-theoretic Buffon's Needle
entry, eliminating the axiom so the polygonal noodle theorem is verified end to end.

### Plain Language

Buffon's Noodle says the expected number of times a dropped curve crosses the floor lines depends
only on its length, by linearity of expectation over its pieces. The polygonal-case proof already
establishes the linearity step rigorously, but it *assumes* the per-segment crossing probability
$2\ell/(\pi d)$ rather than proving it. We want to plug in the existing Buffon's Needle formalization
so nothing is assumed.

### Why This Matters

The base entry `buffons-noodle` currently carries `status: axiomatized`, `badge: axiom` solely
because of this one definitional input. Closing this gap upgrades a known, attractive result to a
fully machine-checked `verified` proof, and demonstrates composition of two gallery entries
(Needle → Noodle) — a clean integral-geometry pipeline.

## Known Results

### What's Already Proven

- **Polygonal noodle linearity** — `buffons-noodle` gallery entry: expected crossings = sum of
  per-segment expected crossings (linearity of expectation; no independence needed).
- **Buffon's Needle** — the registered Buffon's Needle entry provides $p(\ell) = 2\ell/(\pi d)$ for a
  single short segment (the measure-theoretic crossing probability).

### What's Still Open

- The *bridge*: instantiate the Noodle's abstract `segmentCrossingProb` with the Needle entry's
  proven probability, discharging the axiom.
- Confirm the short-segment hypothesis ($\ell_i \le d$) is threaded consistently between the two
  entries.

### Our Goal

Replace `segmentCrossingProb` with the Buffon's Needle result and re-verify the polygonal noodle
theorem with **0 axioms, 0 sorries**, updating the base entry's `meta.json` to `verified`/`original`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| buffons-noodle | The entry being completed | linearity of expectation, integral geometry |
| buffons-needle (registered Needle entry) | Supplies $2\ell/(\pi d)$ to discharge the axiom | measure theory, expected value |

## Initial Thoughts

### Potential Approaches

1. **Direct substitution bridge**: Import the Needle entry, prove `segmentCrossingProb ℓ = 2*ℓ/(π*d)`
   as a lemma from it, and rewrite the noodle sum.
   - Why it might work: linearity scaffolding already exists; only the leaf value is axiomatized.
   - Risk: definitional/normalization mismatch between the two entries' floor parametrizations.

2. **Cauchy–Crofton route**: Derive the per-segment probability via the Cauchy–Crofton arc-length
   formula already tagged on this problem.
   - Why it might work: gives length-only dependence intrinsically.
   - Risk: more Mathlib integral-geometry machinery than currently available.

### Key Difficulties

- Reconciling the angle/offset measure conventions between Needle and Noodle entries.
- Ensuring the short-segment assumption is identical (so $p(\ell)\le 1$ holds piecewise).

### What Would a Proof Need?

- Key lemma: `segmentCrossingProb ℓ = 2 * ℓ / (π * d)` proven from the Needle entry.
- Technical requirement: a shared or compatible probability space for "drop a segment".

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard analytic content (Needle probability; noodle linearity) is already formalized — this is
  primarily a composition/bridging task.
- Risk concentrated in convention-matching, not new mathematics.
- Mathlib provides the measure-theory and `Real.pi` infrastructure needed.

**Estimated Effort**:
- Exploration: hours (read both entries, align conventions)
- If tractable: days
- If hard: a week if the two entries' probability spaces don't compose cleanly

## References

### Papers
- J.-A. Barbier (1860) — original noodle/needle length argument.

### Online Resources
- Buffon's noodle (Wikipedia) — statement and elementary derivation.

### Mathlib
- `MeasureTheory` / probability — expected value and crossing-probability formalization.
- `Real.pi`, `Real.sin` — for the $2\ell/(\pi d)$ constant.

## Metadata

```yaml
tags:
  - geometric-probability
  - integral-geometry
  - buffon
  - linearity-of-expectation
  - cauchy-crofton
  - arc-length
related_proofs:
  - buffons-noodle
  - buffons-needle
difficulty: medium
source: proof-suggestion
created: 2026-06-19T17:27:54-07:00
```
