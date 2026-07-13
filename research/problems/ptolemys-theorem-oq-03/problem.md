# Problem: Sine addition formula from Ptolemy's theorem

**Slug**: ptolemys-theorem-oq-03
**Created**: 2026-06-15T06:15:07.078468+00:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Cyclic quadrilateral: } AC\cdot BD = AB\cdot CD + AD\cdot BC\ \Longrightarrow\ \sin(\alpha+\beta) = \sin\alpha\cos\beta + \cos\alpha\sin\beta
$$

### Plain Language

Ptolemy's theorem states that for a cyclic quadrilateral inscribed in a circle, the product of the diagonals equals the sum of the products of opposite sides: AC·BD = AB·CD + AD·BC. This task formalizes the classical derivation of the sine addition formula sin(α+β) = sinα cosβ + cosα sinβ from Ptolemy's theorem, by inscribing an appropriate quadrilateral (with a diameter) in a unit circle, recovering the historical link between ancient chord tables and modern trigonometry.

### Why This Matters

Ptolemy is a Wiedijk-100 target; deriving the angle-addition law from it links classical geometry to the trigonometric identities used throughout Mathlib.

## Classification

```yaml
tier: C
significance: 5
tractability: 6
```

**Significance**: 5/10
**Tractability**: 6/10

## Known Results

### What's Already Proven

- Ptolemy's theorem for cyclic quadrilaterals (gallery base result).
- sin/cos addition formulas (in Mathlib) — here re-derived geometrically.

### What's Still Open

- A Lean derivation of sin(α+β) from Ptolemy via an inscribed diameter quadrilateral.
- Matching the chord-length picture to Mathlib's analytic sin/cos.

### Our Goal

Formalize the geometric derivation of the sine addition formula from Ptolemy's theorem.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| ptolemys-theorem | Parent gallery proof this open question extends |

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Ptolemy is already available; the derivation is a concrete construction on the unit circle.
- Chord length = 2 sin(half-arc) connects geometry to Mathlib trig.
- Main work is the inscribed-quadrilateral setup and chord-to-sine bookkeeping.

## Metadata

```yaml
tags:
  - geometry
  - circle
  - trigonometry
  - wiedijk-100
  - challenging
  - connection
  - gallery-extracted
  - seeker-selected
  - research
related_proofs:
  - ptolemys-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-15T06:15:07.078468+00:00
```
