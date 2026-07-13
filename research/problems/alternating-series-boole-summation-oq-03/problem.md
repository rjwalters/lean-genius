# Problem: Exact Closed Form for the Alternating Sum of a Quadratic Sequence (Boole Polynomial Ladder, degree 2)

**Slug**: alternating-series-boole-summation-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: alternating-series-boole-summation

## Problem Statement

### Formal Statement

$$
\sum_{j=n}^{m-1} (-1)^j\,(\alpha + \beta j + \gamma j^2)
  = \tfrac12\big((-1)^n a_n - (-1)^m a_m\big)
    - \tfrac14\big((-1)^n (\Delta a)_n - (-1)^m (\Delta a)_m\big)
    + \tfrac14\,\gamma\big((-1)^n - (-1)^m\big),
$$

where $a_j = \alpha + \beta j + \gamma j^2$ and $\Delta a_j = (\beta+\gamma) + 2\gamma j$.

### Plain Language

The parent entry proves the exact finite Boole summation engine and, as its terminal
application, `altSum_affine`: the alternating sum of an **affine** sequence $a_j=\alpha+\beta j$
is a pure endpoint expression, because $\Delta^2(\alpha+\beta j)\equiv 0$ terminates the order-2
Boole formula. This problem takes the next rung of the polynomial ladder — a **quadratic**
sequence $a_j=\alpha+\beta j+\gamma j^2$. Its forward differences are $\Delta a_j=(\beta+\gamma)+2\gamma j$
(affine), $\Delta^2 a_j=2\gamma$ (constant), $\Delta^3 a_j=0$, so the order-3 Boole formula
`boole_exact_of_iterate_fdiff_zero` terminates and evaluates completely to a pure endpoint
expression with no remainder. Prove this closed form and a worked instance for $\sum(-1)^j j^2$.

### Why This Matters

Establishes the parent's finite Boole engine as a reusable *evaluator*: any polynomial
alternating sum collapses to endpoint difference-data once a high enough forward difference
vanishes, with each new degree assembled by reusing lower-difference lemmas rather than
re-deriving the engine. The Boole weights $(-1)^k/2^{k+1}$ appear concretely as $\tfrac12,\tfrac14,\tfrac18$
closing the degree-2 sum, foreshadowing a uniform degree-$d$ closed form.

## Known Results

### What's Already Proven

- Parent entry `alternating-series-boole-summation` is verified (0-axiom): supplies `altSum`,
  `fdiff`, `boole_general`, `boole_exact_of_iterate_fdiff_zero`, `fdiff_affine`,
  `iterate_fdiff_two_affine`, and the degree-1 result `altSum_affine`.

### What's Still Open (before this entry)

- The degree-2 closed form and its squares corollary.

### Our Goal

Prove the target as a self-contained, verified (0-axiom) child of the parent. Category:
**application / specialization**.

## Target Lean Sketch

```lean
theorem fdiff_quadratic (α β γ : ℝ) :
    fdiff (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)
      = fun (j : ℕ) => (β + γ) + 2 * γ * (j : ℝ)

theorem fdiff_two_quadratic (α β γ : ℝ) :
    fdiff^[2] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2) = fun _ => 2 * γ

theorem iterate_fdiff_three_quadratic (α β γ : ℝ) :
    ∀ j, (fdiff^[3] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)) j = 0

theorem altSum_quadratic (α β γ : ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2) n m
      = (1/2) * ((-1:ℝ)^n * (α + β*n + γ*n^2) - (-1:ℝ)^m * (α + β*m + γ*m^2))
        - (1/4) * ((-1:ℝ)^n * ((β+γ) + 2*γ*n) - (-1:ℝ)^m * ((β+γ) + 2*γ*m))
        + (1/4) * γ * ((-1:ℝ)^n - (-1:ℝ)^m)

theorem altSum_sq (n m : ℕ) (h : n ≤ m) :   -- α=β=0, γ=1 corollary
    altSum (fun j => (j : ℝ) ^ 2) n m = ...
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `alternating-series-boole-summation` | Parent: finite Boole engine + degree-1 `altSum_affine` | finite differences, summation by parts |
| `alternating-series-boole-summation-oq-01` | Sibling: m→∞ limit passage | tsum, Filter.Tendsto |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 5/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: Direct reuse of the verified parent engine; the only new inputs are three
finite-difference computations, the last two of which reuse `fdiff_affine`.

### Suggested First Steps

1. `fdiff_quadratic` by unfolding `fdiff` and `ring` — annotate the result binder `(j : ℕ)`
   so the inner `(j : ℝ)` cast does not make Lean infer an ℝ-domain function.
2. `fdiff_two_quadratic` = apply parent's `fdiff_affine` to the affine first difference.
3. `iterate_fdiff_three_quadratic` = `Δ` of the constant `2γ` is `0` (`sub_self`).
4. `altSum_quadratic` = `boole_exact_of_iterate_fdiff_zero … 3`, unfold with
   `Finset.sum_range_succ`/`sum_range_one`, `simp only [...fdiff lemmas...]`, `push_cast; ring`.

## References

### Mathlib
- `Finset.sum_range_succ`, `Finset.sum_range_one` — unfold the length-3 Boole sum
- `Function.iterate_succ'`, `Function.iterate_one`, `Function.iterate_zero` — iterate handling
- `ring`, `push_cast` — close the endpoint algebra

## Metadata

```yaml
tags:
  - analysis
  - series
  - alternating-series
  - boole-summation
  - euler-maclaurin
  - finite-difference
  - closed-form
  - polynomial
related_proofs:
  - alternating-series-boole-summation
  - alternating-series-boole-summation-oq-01
difficulty: low
source: proof-suggestion
created: 2026-07-02
```
