# Problem: Vieta Jumping on the Markov Equation Generates New Solutions

**Slug**: markov-equation-oq-06
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: markov-equation

## Problem Statement

### Formal Statement

$$
a^2 + b^2 + c^2 = 3abc \implies a^2 + b^2 + (3ab - c)^2 = 3ab\,(3ab - c).
$$

That is, the **Vieta jump** `c ↦ 3ab − c` maps Markov triples to Markov triples; the two
values `c` and `c' = 3ab − c` are the two roots of `x² − 3ab·x + (a² + b²) = 0`, so
`c + c' = 3ab` and `c·c' = a² + b²`.

### Plain Language

The Markov equation `a² + b² + c² = 3abc` is the seed of *Vieta jumping*, the technique that
generated the whole "Markov tree" of solutions and famously appears in olympiad number
theory. This child formalizes the fundamental step: **fixing two coordinates and replacing
the third by its Vieta conjugate keeps you on the Markov surface.** From `(1,1,1)` this
single move already reaches `(1,1,2)`, then `(1,2,5)`, `(2,5,29)`, … — the entire tree of
Markov numbers.

### Why This Matters

Vieta jumping is a landmark proof technique with no formal counterpart in Mathlib — there is
**no Markov-equation development at all**. The core jump is a pure polynomial identity
(provable by `linear_combination` off the hypothesis), so it is fully verifiable and
0-axiom, yet it opens a genuinely rich thread (the branching structure, positivity/descent,
unicity conjecture) for later children. This is a high-leverage, low-cost seed.

## Known Results

### What's Already Proven

- Parent `markov-equation` is verified (0-axiom).
- Mathlib has **no** Markov-equation or Vieta-jumping API (confirmed by source search); the
  jump is proved by `ring`/`linear_combination` only.

### What's Still Open

- The Vieta-jump theorems below (currently `sorry`), and the observation that the jump on a
  positive triple stays in the positive integers (`c' = (a²+b²)/c > 0`).

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**technique / generative identity**.

## Target Lean Sketch

```lean
/-- The Vieta jump `c ↦ 3ab - c` preserves the Markov equation. -/
theorem markov_vieta_jump (a b c : ℤ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c) :
    a ^ 2 + b ^ 2 + (3 * a * b - c) ^ 2 = 3 * a * b * (3 * a * b - c) := by
  linear_combination h
  -- Key identity: (a² + b² + c'² - 3ab·c') - (a² + b² + c² - 3ab·c) = 0 for c' = 3ab - c,
  -- so the new equation holds iff the old one does.

/-- Vieta's relations for the two roots `c`, `c' = 3ab - c` of `x² - 3ab·x + (a²+b²)`. -/
theorem markov_roots_sum_prod (a b c : ℤ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c) :
    c + (3 * a * b - c) = 3 * a * b ∧ c * (3 * a * b - c) = a ^ 2 + b ^ 2 := by
  refine ⟨by ring, ?_⟩
  linear_combination h
```

Add worked `example`s tracing the tree: `(1,1,1)` (`3 = 3`), jump `c` → `(1,1,2)` (`6 = 6`),
jump `b` on `(1,1,2)` → `(1,5,2)` i.e. the triple `(1,2,5)` (`30 = 30`), and one more step to
`(2,5,29)`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `markov-equation` | Parent: the Markov equation | Diophantine analysis |
| `vietas-formulas` | Sum/product-of-roots identity used by the jump | polynomial roots |
| `pell-equation` | Recurrence-generated solution families | Diophantine equations |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 7/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: The jump is a single `linear_combination h`; the Vieta relations are `ring`
+ `linear_combination`. It is a genuine Mathlib gap (no Markov content) with an unambiguous
0-axiom proof, and it seeds a much larger structural thread (positivity, descent, the tree).

### Suggested First Steps

1. Prove `markov_vieta_jump` with `linear_combination h` (verify the coefficient is `1`; if
   `ring_nf` leaves a residual, use `nlinarith [h]`).
2. Prove `markov_roots_sum_prod` (sum by `ring`, product by `linear_combination h`).
3. Add the tree-tracing `example`s from `(1,1,1)` outward via `decide`/`norm_num`.

## References

### Mathlib

- No Markov-equation API exists; proofs use `linear_combination`, `ring`, `nlinarith`.
- `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic` (for the conceptual Vieta framing).

### Literature

- A. A. Markov (1879–1880) on the minima of binary quadratic forms; Vieta jumping and the
  Markov tree of solutions. See also the Markov uniqueness conjecture.

## Metadata

```yaml
tags:
  - number-theory
  - markov-equation
  - vieta-jumping
  - diophantine-equations
related_proofs:
  - markov-equation
  - vietas-formulas
  - pell-equation
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
