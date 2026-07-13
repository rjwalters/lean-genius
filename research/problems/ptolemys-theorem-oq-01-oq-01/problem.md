# Problem: Ptolemy Converse — Equality Characterizes Cyclic Quadrilaterals

**Slug**: ptolemys-theorem-oq-01-oq-01
**Created**: 2026-04-21T20:38:01+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $A, B, C, D$ be four distinct points on the unit circle $S^1 \subset \mathbb{C}$. If
$$AC \cdot BD = AB \cdot CD + AD \cdot BC$$
then $A, B, C, D$ appear in cyclic order (either all CCW or all CW).

### Plain Language

Ptolemy's theorem says that for four points on a circle listed in cyclic order, the product of diagonals equals the sum of the products of opposite sides. The **converse** says that equality in $AC \cdot BD \leq AB \cdot CD + AD \cdot BC$ forces the points to lie in cyclic order on a common circle.

### Why This Matters

The converse of Ptolemy's theorem provides a **characterization** of cyclic quadrilaterals: a quadrilateral is cyclic if and only if $AC \cdot BD = AB \cdot CD + AD \cdot BC$. The parent proof `ptolemys-theorem-oq-01` established the forward direction for unit circle points; this completes the bidirectional picture.

## Known Results

### What's Already Proven

- `ptolemys-theorem-oq-01`: Forward direction — CCW order on unit circle implies Ptolemy equality. (verified, 0 sorries)
- `ptolemys-theorem`: Ptolemy's theorem for inscribed quadrilaterals via complex numbers.
- `ptolemys-complex-proof-oq-01`: Complex number proof variant.

### What's Still Open

- The **converse direction**: Ptolemy equality → cyclic order.

### Our Goal

Prove that if $|A-C| \cdot |B-D| = |A-B| \cdot |C-D| + |A-D| \cdot |B-C|$ for four distinct unit circle points, then they appear in CCW or CW order.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `ptolemys-theorem-oq-01` | Forward direction (CCW → equality) | Complex product formulas |
| `ptolemys-theorem` | Main Ptolemy result | `Complex.abs`, cross-ratio |
| `ptolemys-complex-proof-oq-01` | Algebraic complex proof | Ring lemmas, `norm_smul` |

## Initial Thoughts

### Potential Approaches

1. **Cross-ratio approach**: Ptolemy equality ↔ real positive cross-ratio ↔ cyclic order.
   - Why it might work: Cross-ratio characterizes cyclic order completely.
   - Risk: Mathlib may lack the cross-ratio connection lemma.

2. **Algebraic manipulation**: Expand using $|z_i - z_j|^2$ and show equality forces correct angular positions.
   - Why it might work: The forward proof used explicit complex computations; reversibility may follow.
   - Risk: The inequality direction requires careful case analysis.

3. **Inversion argument**: Map to a configuration where the result is obvious, transfer back.

### Key Difficulties

- The converse requires showing Ptolemy equality is a **rigid** condition with only cyclic configurations.
- Need to handle CW vs CCW order symmetry.

### What Would a Proof Need?

- Lemma: The only unit-circle configurations satisfying Ptolemy equality are cyclic orderings.
- Technical: Angular ordering via `Complex.arg` or `Complex.normSq`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The forward direction was already formalized in `ptolemys-theorem-oq-01` — similar techniques apply in reverse.
- Mathlib has good support for `Complex.abs`, `norm_smul`, and circle geometry.

## References

### Mathlib
- `Complex.abs_sub_comm` — symmetry of complex distance
- `Complex.normSq_sub` — norm computation
- `Complex.arg` — angular order

## Metadata

```yaml
tags:
  - geometry
  - ptolemy
  - cyclic-quadrilaterals
  - complex-numbers
related_proofs:
  - ptolemys-theorem-oq-01
  - ptolemys-theorem
difficulty: medium
source: gallery-gap
created: 2026-04-21T20:38:01+02:00
```

**Significance**: 8/10
**Tractability**: 7/10
