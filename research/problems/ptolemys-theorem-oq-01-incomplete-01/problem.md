# Problem: Ptolemy Inequality: Concyclicity Characterization via Strict Inequality

**Slug**: ptolemys-theorem-oq-01-incomplete-01
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall z_1, z_2, z_3, z_4 \in \mathbb{C} \text{ distinct},
$$
$$
|z_1 - z_3| \cdot |z_2 - z_4| \leq |z_1 - z_2| \cdot |z_3 - z_4| + |z_1 - z_4| \cdot |z_2 - z_3|
$$
$$
\text{with equality } \iff z_1, z_2, z_3, z_4 \text{ lie on a common circle (or line) in convex position}
$$

### Plain Language

Ptolemy's theorem says: for four points on a circle, the product of the diagonals equals the
sum of the products of opposite sides. The stronger **Ptolemy inequality** says: for ANY four
points (not necessarily concyclic), the diagonal product is at most the sum of the side
products. Equality holds precisely when the points are concyclic (or collinear) in convex order.

The research task is to formalize this full inequality+characterization in Lean 4, building on
the existing gallery proofs:
- `ptolemys-theorem` — equality theorem for cyclic quadrilaterals
- `ptolemys-theorem-oq-01` — the CCW/CW order characterization for unit-circle points
- `ptolemys-theorem-oq-01-incomplete-01` — the converse direction (equality → cyclic order)
- `ptolemys-complex-proof` — complex algebraic identity proof

The remaining gap: prove the **strict inequality** for non-concyclic points, i.e., that equality
FAILS when the four points are not concyclic. This completes the biconditional characterization.

Additionally: can the non-degeneracy hypotheses (`hdenom ≠ 0`, `hnumer ≠ 0`) in the existing
converse proof be shown to follow automatically from distinctness?

### Why This Matters

1. **Completing the characterization**: The gallery has equality (→ direction) and converse
   (← direction for unit-circle) but not the strict inequality for general position.
2. **Inversive geometry**: Ptolemy's inequality is fundamental to inversive distance and
   Möbius transformations; a Lean formalization advances the inversive geometry library.
3. **Concrete gap**: The strict inequality is a concrete, checkable statement that would
   round out the Ptolemy collection with a uniform, general theorem.

## Known Results

### What's Already Proven (in gallery)

- `ptolemys-theorem`: For four concyclic points in order, AC·BD = AB·CD + AD·BC
- `ptolemys-complex-proof`: The complex identity (z₁-z₃)(z₂-z₄) = (z₁-z₂)(z₃-z₄)+(z₁-z₄)(z₂-z₃)
  implies Ptolemy equality for cyclic points
- `ptolemys-theorem-oq-01`: CCW order → Ptolemy ratio is positive (forward direction)
- `ptolemys-theorem-oq-01-incomplete-01` (gallery): Ptolemy equality → CCW or CW order (converse)
  using the full 8-case sign analysis; yields `ptolemy_equality_iff_ccw_or_cw`

### What's Still Open

1. **Strict inequality for non-concyclic points**: Show that if z₁, z₂, z₃, z₄ are NOT on
   any common circle/line, then the strict inequality holds.
2. **Degeneracy removal**: Show that `hdenom ≠ 0` and `hnumer ≠ 0` in the existing proof
   follow from the points being distinct.
3. **General position version**: Lift from unit circle to arbitrary circles/lines.

### Our Goal

Prove in Lean 4:
```lean
theorem ptolemy_inequality (z₁ z₂ z₃ z₄ : ℂ) (hd : Pairwise (· ≠ ·)) :
    Complex.abs (z₁ - z₃) * Complex.abs (z₂ - z₄) ≤
    Complex.abs (z₁ - z₂) * Complex.abs (z₃ - z₄) +
    Complex.abs (z₁ - z₄) * Complex.abs (z₂ - z₃)

theorem ptolemy_equality_iff_concyclic (z₁ z₂ z₃ z₄ : ℂ) (hd : Pairwise (· ≠ ·)) :
    Complex.abs (z₁ - z₃) * Complex.abs (z₂ - z₄) =
    Complex.abs (z₁ - z₂) * Complex.abs (z₃ - z₄) +
    Complex.abs (z₁ - z₄) * Complex.abs (z₂ - z₃) ↔
    ∃ (c : ℂ) (r : ℝ), r > 0 ∧ ∀ i ∈ [z₁, z₂, z₃, z₄], Complex.abs (i - c) = r
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `ptolemys-theorem` | Base equality theorem | Cyclic polygon, chord product |
| `ptolemys-complex-proof` | Complex identity approach | Complex.abs, algebraic identities |
| `ptolemys-theorem-oq-01` | CCW order characterization | arg, IsCCWOrder, ratio positivity |
| `ptolemys-theorem-oq-01-incomplete-01` | Converse: equality → cyclic order | 8-case sign analysis, sin_half_sign_iff |
| `ptolemys-complex-proof-oq-02` | Extension to spherical/hyperbolic | Metrics, non-Euclidean analogues |

## Initial Thoughts

### Potential Approaches

1. **Inversion approach**: Apply a Möbius inversion mapping one point to ∞, reducing to the
   triangle inequality for three points and their inversive images.
   - Why it might work: Classic proof of Ptolemy's inequality in inversive geometry
   - Risk: Lean Möbius inversion infrastructure may not exist; would need custom development
   
2. **Direct complex inequality**: Use the complex identity
   (z₁-z₃)(z₂-z₄) = (z₁-z₂)(z₃-z₄) + (z₁-z₄)(z₂-z₃)
   and apply the triangle inequality for Complex.abs.
   - Why it might work: |A+B| ≤ |A| + |B|, and the identity gives exact equality condition
   - Risk: The equality case requires characterizing WHEN |A+B| = |A| + |B|, which needs
     A and B to be non-negative real multiples of each other — this is the concyclicity condition

3. **Build from existing ratio positivity**: Use `ptolemy_ratio_pos_of_ccw` and
   `ptolemy_equality_implies_ccw_or_cw` from the gallery, combine with the general complex
   identity to get the full inequality.
   - Why it might work: Reuses already-verified theorems
   - Risk: The strict inequality for non-concyclic case still needs a fresh argument

### Key Difficulties

- **Equality characterization**: |A+B| = |A| + |B| iff A = 0, B = 0, or A/B is real and positive.
  The concyclicity characterization requires this to be matched to the geometric condition.
- **General circles vs unit circle**: The existing work is for unit-circle points; lifting
  to general position requires Möbius invariance or direct generalization.

### What Would a Proof Need?

- Key lemma 1: `Complex.abs_add_eq_iff` — characterize when |A + B| = |A| + |B|
- Key lemma 2: The complex identity as an algebraic identity (already in `ptolemys-complex-proof`)
- Key lemma 3: Concyclicity ↔ cross-ratio is real (classical Möbius characterization)
- Technical requirements: `Complex.abs` triangle inequality from Mathlib

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The inequality itself follows immediately from `Complex.abs_add` (triangle inequality) applied
  to the complex algebraic identity — this part is likely 1-2 hours.
- The equality characterization is harder: it requires identifying the equality case of the
  complex triangle inequality and connecting it to concyclicity.
- The existing gallery infrastructure (complex identity, CCW order theorems) provides a strong
  foundation.
- Mathlib has `Complex.abs_add` and related lemmas; the main challenge is the equality
  characterization which requires custom geometric reasoning.

**Estimated Effort**:
- Exploration (OBSERVE): 1-2 hours — survey Mathlib for abs_add equality and cross-ratio tools
- If tractable (the direct approach works): 2-4 days
- If hard (equality case requires new inversive geometry): 1-2 weeks

## References

### Papers
- Ptolemy, *Almagest* (ca. 150 AD) — original statement
- Standard: Inequality follows from |A+B| ≤ |A|+|B| applied to the complex identity

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — exp, arg, unit circle
- `Mathlib.Analysis.Complex.Basic` — Complex.abs, triangle inequality
- `Proofs.PtolemysComplexProof` — the algebraic identity (ptolemy_identity_prod)
- `Proofs.PtolemysTheoremOQ01` — CCW order and ratio positivity
- `Proofs.PtolemysTheoremOQ01Incomplete01` — converse: equality implies cyclic order

## Metadata

```yaml
tags:
  - geometry
  - complex-analysis
  - ptolemy
  - inequality
  - concyclicity
  - inversive-geometry
related_proofs:
  - ptolemys-theorem
  - ptolemys-complex-proof
  - ptolemys-theorem-oq-01
  - ptolemys-theorem-oq-01-incomplete-01
difficulty: medium
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 7/10
