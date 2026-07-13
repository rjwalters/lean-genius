# Problem: Two-Sided Derivative Bounds Sandwich the Increment

**Slug**: mean-value-theorem-oq-06
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: mean-value-theorem

## Problem Statement

### Formal Statement

$$
m \le f'(x) \le M \ \forall x \in (a,b)
\ \Rightarrow\
m\,(b-a) \le f(b) - f(a) \le M\,(b-a)
$$

### Plain Language

If $f$ is continuous on $[a,b]$ ($a \le b$) and differentiable on $(a,b)$ with derivative
bounded between constants $m \le f'(x) \le M$, then the total increment is sandwiched:
$m(b-a) \le f(b) - f(a) \le M(b-a)$. This is the signed, two-sided quantitative form of the
Mean Value Theorem — it turns pointwise upper *and* lower derivative bounds into global
lower and upper bounds on the finite difference. It specializes: $m > 0$ gives a strict
increase gap, $M < 0$ a strict decrease, and $m = -M = C$ recovers the scalar Lipschitz
bound $|f(b) - f(a)| \le C(b-a)$.

### Why This Matters

Sibling oq-03 (Vector-Valued Mean Value Inequality) proves only the *absolute* upper bound
$\|f(b)-f(a)\| \le C(b-a)$ — a one-sided magnitude bound that discards sign and gives no
lower bound. This child proves the **signed, two-sided** sandwich for scalar $f$, capturing
the lower bound and direction (oq-03's norm inequality is the $m = -M$ special case). It is
also distinct from oq-02 (Taylor/Lagrange remainder), oq-04 (FTC), oq-04-oq-03 (trapezoidal
rule), and oq-05 (Darboux). No sibling formalizes the increment sandwich.

## Known Results

### What's Already Proven

- Parent entry `mean-value-theorem` is verified (0-axiom).
- Mathlib supplies `Convex.mul_sub_le_image_sub_of_le_deriv` and
  `Convex.image_sub_le_mul_sub_of_deriv_le`, both built on the core MVT.

### What's Still Open

- The target theorem below (currently `sorry`) plus a monotonicity/Lipschitz corollary.

### Our Goal

Prove the sketch below as a verified (0-axiom) child of `mean-value-theorem`.
Category: **extension** (real analysis).

## Target Lean Sketch

```lean
open Set

theorem deriv_bounds_imply_increment_bounds {a b m M : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hm : ∀ x ∈ Set.Ioo a b, m ≤ deriv f x)
    (hM : ∀ x ∈ Set.Ioo a b, deriv f x ≤ M) :
    m * (b - a) ≤ f b - f a ∧ f b - f a ≤ M * (b - a) := by
  sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `mean-value-theorem` | Parent: MVT / Rolle | mean value theorem |
| `mean-value-theorem-oq-03` | Sibling: vector-valued MVT inequality (absolute, one-sided) | norm bound |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 5/10  |  **Tractability**: 9/10  |  **Tier**: C

**Justification**: Both bounds are direct applications of named Mathlib `Convex.*` lemmas
after rewriting `Ioo a b = interior (Icc a b)`. Assembly-level.

### Suggested First Steps

1. `rw [← interior_Icc] at hfd hm hM` so the `Convex.*` lemmas apply directly.
2. Split with `refine ⟨?_, ?_⟩`; discharge the lower bound with
   `(convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hfc hfd hm ...` and the upper bound
   with `(convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hfc hfd hM ...`.
3. Add a corollary: quantitative strict monotonicity ($m > 0 \Rightarrow f a < f b$) or
   recover $|f(b)-f(a)| \le C(b-a)$ from $m = -C, M = C$ via `abs_le`.

## References

### Mathlib

- `Convex.mul_sub_le_image_sub_of_le_deriv` — Analysis/Calculus/Deriv/MeanValue.lean
- `Convex.image_sub_le_mul_sub_of_deriv_le` — Analysis/Calculus/Deriv/MeanValue.lean
- `convex_Icc` — Analysis/Convex/Basic.lean
- `interior_Icc` — Topology/Order/DenselyOrdered.lean
- `exists_deriv_eq_slope` — Analysis/Calculus/Deriv/MeanValue.lean (core MVT engine)

## Metadata

```yaml
tags:
  - calculus
  - real-analysis
  - mean-value-theorem
  - derivative-bounds
  - monotonicity
related_proofs:
  - mean-value-theorem
  - mean-value-theorem-oq-03
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
