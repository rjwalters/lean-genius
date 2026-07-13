# Session 7 — K-side uniform bound (`boundDIntegrandK`) infrastructure

**Date**: 2026-05-08
**Researcher**: researcher-9
**Phase**: ACT
**Outcome**: New §11 added; +1 def, +3 lemmas, +0 axioms, +0 sorries; ~132 lines.

## Goal

Provide the K-side analog of §9 (E-side uniform bound) so that the
seven-hypothesis discharge of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
for `ellipticK` has its `h_bound` and `bound_integrable` ingredients
ready when the (still-pending) K-side algebraic split + integral
identity is in place. This is one of the four remaining items called out
in the post-S6 sharpening of the plan ("K-side bound infrastructure
… ~80 lines").

## Mathematical content

For `0 ≤ M` with `M² < 1` and any `κ` with `κ² ≤ M²`, every `θ ∈ ℝ`:

  |dIntegrandK κ θ|  ≤  M · sin²θ / [(1 − M² sin²θ) · √(1 − M² sin²θ)]
                    =:  boundDIntegrandK M θ.

The denominator on the M-side is positive (we only use this for
`M² < 1`), and `boundDIntegrandK M` is continuous in `θ`, hence
interval-integrable on `[0, π/2]`.

The proof has the same shape as `dIntegrandE_abs_le_bound` (§9):

* numerator monotonicity:  `|κ| · sin²θ ≤ M · sin²θ`  (uses `|κ| ≤ M`,
  `sin²θ ≥ 0`);
* denominator antitonicity:  `(1 − M² sin²θ) ≤ (1 − κ² sin²θ)`  (from
  `κ² ≤ M²`), hence
  `√(1 − M² sin²θ) ≤ √(1 − κ² sin²θ)`, hence the **product**
  `(1 − M²sin²θ) · √(1 − M²sin²θ) ≤ (1 − κ²sin²θ) · √(1 − κ²sin²θ)` by
  `mul_le_mul` (both sides nonneg/positive).

These two inequalities discharge `div_le_div`. The numerator on the
LHS is `|κ · sin²θ| = |κ| · sin²θ` (one fewer `abs_neg` than §9, since
`dIntegrandK` has no leading minus sign). The denominator under the `|·|`
is positive, so `abs_div` followed by `abs_of_pos` removes the absolute
values.

## Mathlib API surface

Zero new lemmas. Reuses:

* `Continuous.div₀`, `continuous_const`, `continuous_sin`,
  `Real.continuous_sqrt`, `Continuous.intervalIntegrable`
  (continuity / integrability of `boundDIntegrandK`);
* `AmgmInequalityOQ04OQ01.denom_pos`, `AmgmInequalityOQ04OQ01.sqrt_denom_pos`
  (imported, identical to §9's usage);
* `Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`, `Real.sqrt_sq`
  (the `|κ| ≤ M` reduction from `κ² ≤ M²`);
* `abs_div`, `abs_mul`, `abs_of_nonneg`, `abs_of_pos`
  (absolute-value rewrites);
* `div_le_div`, `mul_le_mul`, `mul_le_mul_of_nonneg_right`,
  `mul_pos`, `mul_nonneg` (the divisor / divided inequality plumbing).

No new imports.

## File-level deltas

* `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`: 697 → 829 lines (+132).
* `src/data/proofs/amgm-inequality-oq-04-oq-02/meta.json`:
  `lineCount` 697 → 829; `theoremCount` 33 → 36; `definitionCount` 8 → 9.
* New definition: `boundDIntegrandK`.
* New lemmas: `boundDIntegrandK_continuous`, `boundDIntegrandK_integrable`,
  `dIntegrandK_abs_le_bound`.
* `legendre_relation` axiom unchanged (1 axiom, 0 sorries).

## Independence from other in-flight S-PRs

This section uses only §10 (K-side chain rule, merged in PR #17373) and
the imported `denom_pos` / `sqrt_denom_pos` from `AmgmInequalityOQ04OQ01`.
It is independent of the still-open PR #17371 (`dE_dk` E-side
assembly) — that PR touches §1/§8/§9 only and adds a new §10 on the
E-side that is already locally renamed. No conflict.

## Next action (S8)

Of the four remaining items in the post-S6 plan, two are now done
(S6 K-side chain rule = §10; S7 K-side bound = §11). Open work:

1. **K-side algebraic split + integral identity** (~80–120 lines).
   This is the *non-pointwise* IBP step on
   `∫ k sin²θ (1 − k²sin²θ)^{−3/2} dθ`. State:

       ∫₀^{π/2} dIntegrandK k θ dθ
         = (E(k) − (1 − k²) K(k)) / (k (1 − k²)).

   Substitute `u = sin θ`, `du = cos θ dθ`; IBP with
   `v = sin θ / √(1 − k² sin²θ)` and `dw = sin θ dθ`. Key Mathlib
   lemmas: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`
   (integration by parts), `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
   (substitution).

2. **`dE_dk` assembly** (PR #17371; ~30 lines). When that lands,
   `dK_dk` follows the same template using §10 (chain rule), §11 (this
   PR, the K-side bound), and the K-side integral identity from item 1.

3. **Wronskian closure** (~50 lines): once both `dE_dk` and `dK_dk`
   are theorems, `Mathlib.Analysis.Calculus.eq_of_hasDerivAt_eq_zero`
   shows that `f(k) = E·K' + E'·K − K·K'` is constant on `(0, 1)`;
   evaluating at `k = 1/√2` (where `f = 2KE − K²`) and using
   `legendre_relation_symmetric` (§7) pins the constant to `π/2`,
   discharging the `legendre_relation` axiom.

## Build status

Build pending. The §11 lemmas mirror §9's pattern essentially line for
line, and §9 was build-verified in PR #17358 (S5). The only new
denominator structure (`(1 − u) · √(1 − u)` instead of `√(1 − u)`) was
already introduced in §10 and build-verified in PR #17373 (S6). No new
imports, no new Mathlib API.
