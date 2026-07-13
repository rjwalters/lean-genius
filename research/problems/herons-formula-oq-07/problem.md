# Problem: Weitzenböck's Inequality from Heron's Formula

**Slug**: herons-formula-oq-07
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: herons-formula

## Problem Statement

### Formal Statement

$$
a^2 + b^2 + c^2 \ge 4\sqrt{3}\cdot \text{Area},\qquad
\text{Area} = \sqrt{s(s-a)(s-b)(s-c)},\ \ s = \tfrac{a+b+c}{2}
$$

with equality iff the triangle is equilateral (IMO 1961, Problem 2).

### Plain Language

For any nondegenerate triangle with side lengths $a, b, c$, the sum of the squares of the
sides bounds the area from above: $a^2 + b^2 + c^2 \ge 4\sqrt{3}\,\text{Area}$, where Area
is Heron's formula. The proof squares both sides — reducing to $48\,\text{Area}^2 \le
(a^2+b^2+c^2)^2$ — expands $16\,\text{Area}^2 = 2a^2b^2 + 2b^2c^2 + 2c^2a^2 - a^4 - b^4 - c^4$
by `ring`, and finishes with the sum-of-squares fact
$a^4 + b^4 + c^4 \ge a^2b^2 + b^2c^2 + c^2a^2$, i.e.
$\tfrac12((a^2-b^2)^2 + (b^2-c^2)^2 + (c^2-a^2)^2) \ge 0$.

### Why This Matters

Weitzenböck's inequality is a distinct classical named result (IMO 1961) relating the
**sum of squared sides** to area. The eight siblings cover Brahmagupta (oq-01), Kahan
stability (oq-03), the isoperimetric max-area result (oq-04), Cayley–Menger (oq-05,
oq-05-oq-03), and the circum/inradius family (oq-06 branch) — none is Weitzenböck.
It exercises a different SOS mechanism than the perimeter-fixing AM-GM of oq-04 and
touches neither $R$ nor $r$.

## Known Results

### What's Already Proven

- Parent entry `herons-formula` is verified (0-axiom) and supplies the area formula.
- The `Real.sqrt` lemmas below are grep-confirmed in `Mathlib/Data/Real/Sqrt.lean`.

### What's Still Open

- The target inequality below (currently `sorry`).

### Our Goal

Prove the sketch below as a verified (0-axiom) child of `herons-formula`.
Category: **extension** (geometric inequality).

## Target Lean Sketch

```lean
open Real

theorem weitzenboeck (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    4 * Real.sqrt 3 *
        Real.sqrt ((a + b + c) / 2 * ((a + b + c) / 2 - a) *
          ((a + b + c) / 2 - b) * ((a + b + c) / 2 - c))
      ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `herons-formula` | Parent: Area = √(s(s−a)(s−b)(s−c)) | Heron's formula |
| `herons-formula-oq-04` | Sibling: isoperimetric max area (fixes perimeter) | AM-GM |
| `herons-formula-oq-05` | Sibling: Cayley–Menger determinant | determinant area |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 7/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: Both sides are nonnegative, so squaring reduces the goal to a polynomial
inequality dischargeable by `nlinarith` with three explicit SOS hints. Only three `Real.sqrt`
rewrite lemmas are needed.

### Suggested First Steps

1. State with Area = `Real.sqrt` of the explicit Heron product; note both sides nonneg.
2. Rewrite `4·√3·√(hp) = √(48·hp)` via `Real.sqrt_mul`, and `a²+b²+c² = √((a²+b²+c²)²)`
   via `Real.sqrt_sq`; then apply `Real.sqrt_le_sqrt`.
3. Discharge `48·hp ≤ (a²+b²+c²)²` by `ring_nf` +
   `nlinarith [sq_nonneg (a^2-b^2), sq_nonneg (b^2-c^2), sq_nonneg (c^2-a^2)]`.

## References

### Mathlib

- `Real.sqrt_mul` — Data/Real/Sqrt.lean (√(x·y) = √x·√y for 0 ≤ x)
- `Real.sqrt_sq` — Data/Real/Sqrt.lean (√(x²) = x for 0 ≤ x)
- `Real.sqrt_le_sqrt` — Data/Real/Sqrt.lean
- `Real.sqrt_nonneg` — Data/Real/Sqrt.lean
- `sq_nonneg` — Mathlib (SOS hints for `nlinarith`)

## Metadata

```yaml
tags:
  - geometry
  - triangle-inequality
  - weitzenboeck
  - sum-of-squares
  - imo
related_proofs:
  - herons-formula
  - herons-formula-oq-04
  - herons-formula-oq-05
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
