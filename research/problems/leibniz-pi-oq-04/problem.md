# Problem: Euler's Two-Term Machin-Like Identity π/4 = arctan(1/2) + arctan(1/3)

**Slug**: leibniz-pi-oq-04
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: leibniz-pi

## Problem Statement

### Formal Statement

$$
\frac{\pi}{4} \;=\; \arctan\!\tfrac12 \;+\; \arctan\!\tfrac13
\qquad\text{(Euler, 1738),}
$$

and, as a genuinely three-term companion,

$$
\frac{\pi}{4} \;=\; \arctan\!\tfrac13 \;+\; \arctan\!\tfrac14 \;+\; \arctan\!\tfrac29 .
$$

Both follow by iterating the arctangent addition law
$\arctan x + \arctan y = \arctan\!\frac{x+y}{1-xy}$ (valid when $xy<1$) down to
$\arctan 1 = \pi/4$.

### Plain Language

The parent entry `leibniz-pi` proves the Gregory–Leibniz series
$\pi/4 = 1 - \tfrac13 + \tfrac15 - \cdots$, which converges very slowly. Machin-like identities
express $\pi/4$ with arctangents of *small* arguments, whose Taylor series converge
geometrically — the classical route to computing $\pi$ by hand. This child proves **Euler's**
clean two-term identity $\pi/4 = \arctan\tfrac12 + \arctan\tfrac13$ (a single application of
the addition law, since $\tfrac12\cdot\tfrac13 = \tfrac16 < 1$ and the combined argument is
exactly $1$), and a genuinely three-term companion
$\arctan\tfrac13+\arctan\tfrac14+\arctan\tfrac29$ requiring **two** folds.

### Why This Matters

Machin-like formulas are the canonical worked application of the arctangent addition law and
the historical engine of $\pi$ computation. Mathlib provides the addition law
(`Real.arctan_add`) and `Real.arctan_one = π/4`, but **no** named identity of this kind; each
must be assembled from one or more applications of the addition law plus `norm_num`
side-condition checks. Euler's identity is distinct from every existing `leibniz-pi` sibling
(Machin `4·arctan(1/5)−arctan(1/239)`, Dase `arctan(1/2)+arctan(1/5)+arctan(1/8)`,
Leibniz-rate, Dirichlet-beta, series-acceleration).

## Known Results

### What's Already Proven

- Parent `leibniz-pi` is verified (0-axiom): the Gregory–Leibniz alternating series for `π/4`.
- Siblings cover Machin's formula (`oq-01-oq-01`) and Dase's three-term formula (`oq-01-oq-03`);
  **neither** is Euler's `arctan(1/2)+arctan(1/3)` nor the `1/3,1/4,2/9` triple below.
- Mathlib: `Real.arctan_add` (addition law with the `xy < 1` hypothesis),
  `Real.arctan_one` (`arctan 1 = π/4`), `norm_num` for the rational arithmetic.

### What's Still Open

- The two exact closed identities below (currently `sorry`), proved by iterating the
  addition law.

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**real analysis / identity completion**.

## Target Lean Sketch

```lean
open Real

/-- Euler's identity: a single fold collapses the sum to `arctan 1 = π/4`. -/
theorem euler_pi_div_four :
    arctan (1/2 : ℝ) + arctan (1/3) = π / 4 := by
  sorry
  -- `Real.arctan_add (by norm_num : (1/2 : ℝ) * (1/3) < 1)` rewrites the LHS to
  -- `arctan ((1/2 + 1/3)/(1 - 1/2*1/3)) = arctan ((5/6)/(5/6)) = arctan 1`; then
  -- `norm_num` simplifies the argument to `1` and `Real.arctan_one` gives `π/4`.

/-- A genuinely three-term companion needing two folds. -/
theorem machin_three_term :
    arctan (1/3 : ℝ) + arctan (1/4) + arctan (2/9) = π / 4 := by
  sorry
  -- Fold 1: arctan(1/3) + arctan(1/4) = arctan(7/11)   (xy = 1/12 < 1,
  --         (1/3+1/4)/(1 − 1/12) = (7/12)/(11/12) = 7/11).
  -- Fold 2: arctan(7/11) + arctan(2/9) = arctan 1       (xy = 14/99 < 1,
  --         (7/11 + 2/9)/(1 − 14/99) = (85/99)/(85/99) = 1).
  -- Then `Real.arctan_one`. Discharge each `xy < 1` and simplification with `norm_num`.
```

Add worked `example`s: numerically check `arctan(1/2)+arctan(1/3) ≈ 0.7854` and
`arctan(1/3)+arctan(1/4)+arctan(2/9) ≈ 0.7854`; state the intermediate fold
`arctan(1/2)+arctan(1/5) = arctan(7/9)` as a reusable warm-up lemma.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `leibniz-pi` | Parent: Gregory–Leibniz series for `π/4` | real analysis, series |
| `leibniz-pi-oq-01-oq-01` | Machin's formula (sibling, addition-law method) | arctangent identities |
| `euler-identity` | Trig/exponential identities | complex analysis |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 5/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: Euler's identity is one `Real.arctan_add` + `norm_num` + `Real.arctan_one`;
the three-term companion is two folds of the same shape. No convergence analysis, no calculus —
short, robust proofs mirroring the existing Machin entry.

### Suggested First Steps

1. Prove `euler_pi_div_four`: apply `Real.arctan_add` (side-goal `1/2*1/3 < 1` by `norm_num`),
   simplify the argument to `1`, finish with `Real.arctan_one`.
2. Prove the fold `arctan(1/3) + arctan(1/4) = arctan(7/11)` as a lemma.
3. Chain with the second fold to `arctan 1` and finish `machin_three_term`.

## References

### Mathlib

- `Real.arctan_add` — Analysis/SpecialFunctions/Trigonometric/Arctan.lean
- `Real.arctan_one` — Analysis/SpecialFunctions/Trigonometric/Arctan.lean
- `Real.tan_arctan`, `Real.arctan_lt_pi_div_two` — Analysis/SpecialFunctions/Trigonometric/Arctan.lean

### Literature

- Euler's 1738 identity `π/4 = arctan(1/2) + arctan(1/3)`; the family of Machin-like formulas
  is standard in any treatment of `π` computation (Borwein & Borwein, *Pi and the AGM*).

## Metadata

```yaml
tags:
  - real-analysis
  - leibniz-pi
  - arctangent
  - machin-formula
related_proofs:
  - leibniz-pi
  - leibniz-pi-oq-01-oq-01
  - euler-identity
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
