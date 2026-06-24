# Problem: Divisibility package for primitive Pythagorean triples (60 ∣ xyz)

**Slug**: pythagorean-triples-oq-06-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every primitive Pythagorean triple $(x, y, z)$ with $x^2 + y^2 = z^2$, $\gcd(x,y) = 1$:

$$
4 \mid x \text{ or } 4 \mid y, \quad 3 \mid xy, \quad 5 \mid xyz, \quad \text{hence } 60 \mid xyz.
$$

### Plain Language

The parent entry (`pythagorean-triples-oq-06-oq-01`) proves the parity dichotomy: exactly one
leg of a primitive triple is even. This leaf strengthens that to the full elementary
divisibility package: the even leg is in fact divisible by **4**, exactly one of the two legs
is divisible by **3**, exactly one of the three sides is divisible by **5**, and therefore the
product of the three sides is always divisible by $60 = 4 \cdot 3 \cdot 5$.

### Why This Matters

It packages a classic collection of competition/elementary-number-theory facts into a single
machine-checked statement, completing the modular picture begun by the parent's parity result.

## Known Results

### What's Already Proven

- Parent `pythagorean-triples-oq-06-oq-01`: parity dichotomy — exactly one leg is even (verified, 0-axiom).
- Mathlib `PythagoreanTriple` API: `PythagoreanTriple.coprime_classification`, the
  `m, n` parametrization $x = m^2 - n^2$, $y = 2mn$, $z = m^2 + n^2$ with `m`, `n` coprime and
  opposite parity.

### What's Still Open

- The mod-4, mod-3, mod-5 refinements and their combination into `60 ∣ xyz` (this entry).

### Our Goal

Prove `4 ∣ (even leg)`, `3 ∣ xy`, `5 ∣ xyz`, and conclude `60 ∣ x*y*z` for every primitive
triple, building on the parent's parity result and Mathlib's `PythagoreanTriple` parametrization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pythagorean-triples-oq-06-oq-01 | Direct parent; parity dichotomy | PythagoreanTriple parametrization, parity |
| pythagorean-triples-oq-06 | Grandparent; primitive triple structure | m,n parametrization |

## Initial Thoughts

### Potential Approaches

1. **Residue case analysis via the m,n parametrization**: from $y = 2mn$ with $m,n$ of opposite
   parity, one of $m,n$ is even so $4 \mid y$. For mod 3 and mod 5, do a finite `decide`/`omega`
   case split on $m, n$ residues using $x = m^2 - n^2$, $y = 2mn$.
   - Why it might work: residues mod 3, 4, 5 are finite; quadratic residues are easy to enumerate.
   - Risk: bridging Mathlib's `PythagoreanTriple` parametrization to concrete `ZMod` casts.

### Key Difficulties

- Marshalling the parametrization hypotheses (coprimality, opposite parity) into the residue split.

### What Would a Proof Need?

- Key lemma: `4 ∣ y` from `y = 2mn` and opposite parity of `m,n`.
- Key lemma: `3 ∣ xy` and `5 ∣ xyz` via `ZMod 3` / `ZMod 5` `decide` over residue classes.
- Combine via coprimality of 4, 3, 5 ⇒ `60 ∣ xyz`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Pure elementary number theory; all obstructions are finite residue checks (`decide`/`omega`).
- Parent already supplies the structural parametrization and parity result.
- Mathlib's `PythagoreanTriple` and `ZMod` decidability cover the machinery.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.NumberTheory.PythagoreanTriples` — primitive triple classification and parametrization.
- `Mathlib.Data.ZMod.Basic` — `decide` over residue classes for the mod-3/4/5 refinements.

## Metadata

```yaml
tags:
  - number-theory
  - pythagorean-triples
  - divisibility
  - elementary
related_proofs:
  - pythagorean-triples-oq-06-oq-01
  - pythagorean-triples-oq-06
difficulty: low
source: gallery-gap
created: 2026-06-24
```
