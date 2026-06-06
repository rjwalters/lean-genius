# S6c ACT-2 — `complex_gaussian_integral_norm_sq` + `schur_orthogonality_complex_gaussian_diag`

**Researcher**: researcher-1
**Date**: 2026-06-06
**Mode**: ACT (Lean code, two new theorems). Sorry-free, axiom-free.
**Predecessor**: S6c ACT-1 (`sessions/2026-06-04-s6c-act-1-integral-sq-exp-neg-sq.md`).

## Summary

Closes the S6c programme by shipping the two follow-on theorems that
were deferred at S6c ACT-1 close:

1. `complex_gaussian_integral_norm_sq : ∫_ℂ ‖w‖² · exp(-‖w‖²) dw = π`
   (the 1-D complex second moment, ~70 LOC including helper and
   docstring).
2. `schur_orthogonality_complex_gaussian_diag {n : ℕ} (i : Fin n) :
   ∫_{ℂⁿ} ‖z_i‖² · (1/π)ⁿ · exp(-∑_k ‖z_k‖²) dz = 1` (n-dim diagonal
   case, ~55 LOC including docstring).

Cumulative Lean state after this PR: **1098 LOC / 29 theorems +
2 private helpers (+2 new) / 0 sorries / 0 axioms** in
`proofs/Proofs/AreaOfCircleOQ05OQ04.lean`. New `Part 9 — S6c ACT-2`
section sits between `Part 8` (S6c ACT-1) and the `## Status` block.

## Theorem 1: `complex_gaussian_integral_norm_sq`

**Statement**

```
∫ w : ℂ, ‖w‖^2 * Real.exp (-‖w‖^2) = Real.pi
```

**Proof route** (PREP-3 §5 route, unchanged)

1. Convert `‖w‖² = w.re² + w.im²` via `Complex.normSq_eq_norm_sq` and
   `Complex.normSq_apply`.
2. Transport `∫_ℂ` to `∫_{ℝ × ℝ}` via
   `Complex.volume_preserving_equiv_real_prod.integral_comp'`.
3. Factor `(p.1² + p.2²) · exp(-(p.1² + p.2²))` as a sum of two
   product summands:
   `p.1² · exp(-p.1²) · exp(-p.2²) + exp(-p.1²) · (p.2² · exp(-p.2²))`.
4. Switch to product measure (`volume_eq_prod ℝ ℝ`).
5. Split the sum via `integral_add` using `Integrable.mul_prod` on
   each summand.
6. Apply `integral_prod_mul` to each summand.
7. Evaluate `∫ x² · exp(-x²) = √π / 2` (from `integral_sq_exp_neg_sq`,
   S6c ACT-1) and `∫ exp(-x²) = √π` (from `integral_b_gaussian 1`,
   from S3).
8. Algebraic close: `(√π/2) · √π + √π · (√π/2) = π` via
   `Real.mul_self_sqrt Real.pi_nonneg` + `linarith`.

**Supporting helpers** (private, in `section DiagonalSchur`)

- `integrable_sq_mul_exp_neg_sq` : `Integrable fun x : ℝ => x² · exp(-x²)`,
  via `integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := 2)` +
  `simp_rw [Real.rpow_two, neg_one_mul]`.
- `integrable_exp_neg_sq` : `Integrable fun x : ℝ => exp(-x²)`,
  via `integrable_exp_neg_mul_sq (b := 1)` + `simp_rw [neg_one_mul]`.

## Theorem 2: `schur_orthogonality_complex_gaussian_diag`

**Statement**

```
{n : ℕ} (i : Fin n) :
∫ z : Fin n → ℂ, ‖z i‖^2 * ((1 : ℝ) / Real.pi)^n *
  Real.exp (-(∑ k, ‖z k‖^2)) = 1
```

The hypothesis `n ≥ 1` is enforced implicitly by `i : Fin n` (the
type is uninhabited at `n = 0`).

**Proof route** (PREP-3 §5 + PREP-2 §3.2, unchanged)

1. Rewrite the integrand as
   `(1/π)ⁿ · ∏_k f_k(z_k)` where
   `f_k w := if k = i then ‖w‖² · exp(-‖w‖²) else exp(-‖w‖²)`.

   This uses:
   - `Finset.sum_neg_distrib` + `Real.exp_sum` to turn
     `exp(-∑‖z_k‖²)` into `∏ exp(-‖z_k‖²)`.
   - `Finset.mul_prod_erase` (twice) to split the i-th factor out of
     both products and reduce to a `Finset.prod_congr` over the
     `erase i` complement.
   - `ring` to align factors.
2. Pull `(1/π)ⁿ` outside via `integral_const_mul`.
3. Apply heterogeneous Fubini
   (`integral_fintype_prod_volume_eq_prod`).
4. **Key observation**: BOTH branches of `f_k` integrate to `π`.
   - Axis `i` (the `‖w‖²·exp(-‖w‖²)` branch) collapses via
     `complex_gaussian_integral_norm_sq` (Theorem 1 above).
   - Axes `k ≠ i` (the `exp(-‖w‖²)` branch) collapse via
     `complex_gaussian_integral_unit_norm` (S3, line 281).
   So `∏_k ∫ w, f_k(w) = ∏_k π = πⁿ` (`Finset.prod_const` +
   `Finset.card_univ` + `Fintype.card_fin`).
5. Algebraic close: `(1/π)ⁿ · πⁿ = 1` via `div_pow`, `one_pow`,
   `div_mul_cancel₀ _ (pow_ne_zero n Real.pi_ne_zero)`.

The "both branches integrate to π" observation is what makes the
`if k = i` reformulation clean: the integrand structure is uniform
modulo a single per-axis factor of `‖z_i‖²`, and the unit-Gaussian
normalisation `1/π` exactly compensates whether or not the moment
weight is attached.

## Delta from PREP-3 §5 (skeleton)

The PREP-3 §5 skeleton sketched:
- `complex_gaussian_integral_norm_sq` at "~15-20 LOC"
- `schur_orthogonality_complex_gaussian_diag` at "~25-35 LOC"

Final size:

| Theorem | Skeleton estimate | Final body (excl. docstring) |
|---|---|---|
| `complex_gaussian_integral_norm_sq` | ~15-20 LOC | 52 LOC body |
| `schur_orthogonality_complex_gaussian_diag` | ~25-35 LOC | 50 LOC body |
| Helpers (`integrable_sq_mul_exp_neg_sq`, `integrable_exp_neg_sq`) | (not in skeleton) | 8 LOC body |

Combined body ~110 LOC vs. the PREP-3 §5 "~40-55 LOC" sketch. The
overage is concentrated in:

1. **Helper integrability lemmas** (8 LOC, not in PREP-3 §5 sketch).
   PREP-3 noted "no `MemLp 2` integrability hypothesis needed" for
   the ACT-1 1-D real moment — true there because `gaussianReal`'s
   variance lemma carries its own. For ACT-2's `integral_add` split,
   we need integrability on `ℝ × ℝ` explicitly; the cleanest path is
   two `private lemma`s feeding `Integrable.mul_prod`.
2. **Pointwise factorisation steps** for `complex_gaussian_integral_norm_sq`
   (~30 LOC of `have h_norm`, `have h_eq`, `have h_pull`, `have h_factor`).
   These match the existing S3 `complex_gaussian_integral_scaled` template
   line-by-line and are not "novel proof work" — they're the unavoidable
   measurableEquiv chain.
3. **The `Finset.mul_prod_erase` two-step split** for the n-dim Schur
   reformulation (~15 LOC). PREP-3 §5 listed this as "Step 2.
   integral_fintype_prod_volume_eq_prod with the i-th factor being..."
   without unpacking the `if k = i` algebra.

None of these introduce new proof ideas; they're concrete-tactic
unrolling of PREP-3 §5's two-step assembly plan.

## Bearer recheck (PREP-3 §2.2 + new)

All cited Mathlib bearers were confirmed live at the slug's pinned
SHA `2df2f0150c` (v4.26.0). New bearers introduced by this ACT-2:

| Identifier                                          | Module                                                         | Status |
|-----------------------------------------------------|----------------------------------------------------------------|--------|
| `integrable_rpow_mul_exp_neg_mul_sq`                | `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:109` | ✓ used |
| `integrable_exp_neg_mul_sq`                         | (same)                                                          | ✓ used |
| `Real.rpow_two`                                     | `Analysis/SpecialFunctions/Pow/Real.lean:461`                   | ✓ used |
| `Integrable.mul_prod`                               | `MeasureTheory/Integral/Prod.lean:348`                         | ✓ used |
| `integral_add`                                      | (Mathlib MeasureTheory.Integral.SetIntegral or Basic; via `open`) | ✓ used |
| `integral_fintype_prod_volume_eq_prod`              | `MeasureTheory/Integral/Pi.lean:114`                            | ✓ used |
| `Finset.mul_prod_erase`                             | `Algebra/BigOperators/Group/Finset/Basic.lean:749`              | ✓ used |
| `Finset.sum_neg_distrib`                            | (Mathlib BigOperators; via open `Finset`)                       | ✓ used |
| `Real.exp_sum`                                      | (Mathlib Real exponential)                                      | ✓ used |
| `div_mul_cancel₀`                                   | (Mathlib GroupWithZero)                                         | ✓ used |
| `pow_ne_zero`                                       | (Mathlib Monoid power)                                          | ✓ used |

## Status

- Cumulative: **0 sorries, 0 axioms** (unchanged).
- New theorems: 2 (Part 9, S6c ACT-2).
- New private helpers: 2 (`integrable_sq_mul_exp_neg_sq`,
  `integrable_exp_neg_sq`).
- Cumulative theorem count: 27 → 29 (+2).
- File LOC: 921 → 1098 (+177).
- Docker build: in progress; will note final job count + Mathlib pin
  recheck in the PR body.

## Anti-targets (this ACT-2 PR)

- Does NOT touch `problem.md`, `state.md` of the flat dir, the merged
  S4b / S6a / S6b / S6c / S6c PREP files, the gallery `meta.json`,
  or any JSON.
- Does NOT consolidate the flat-vs-canonical research directory split
  (mechanic-sweep scope per
  `feedback_researcher_canonical_vs_flat_research_problems_dir_divergence`).
- Does NOT ship the *off-diagonal* Schur orthogonality (the PREP-2 §4.1
  case via odd symmetry); that's a separate, smaller ACT-3 follow-up.
- Does NOT initialise the gallery entry
  `src/data/proofs/area-of-circle-oq-05-oq-04/` (mechanic / gallery-init
  scope).
- Does NOT lift to n-dim complex Fourier-Gaussian (orthogonal frontier;
  S6 ACT precedent makes this an independent follow-up).

## Next steps

S6c is now functionally complete on the archimedean (complex) side.
Remaining S6c work:

- **(optional) S6c ACT-3 — off-diagonal Schur**: for `i ≠ j`,
  `∫_{ℂⁿ} ⟨z_i, z_j⟩ · (1/π)ⁿ · exp(-∑‖z_k‖²) dz = 0` via per-axis
  Fubini + odd symmetry on each `z_i` axis (the linear factor `z_i`
  paired with the even `exp(-‖z_i‖²)` Gaussian integrates to zero).
  PREP-2 §4.1 sketches this; not load-bearing for "Schur orthogonality
  diagonal" milestone.

Deferred (orthogonal, multi-week — unchanged from S6c ACT-1):
- **S6d (Mathlib milestone — `Measure ℚ_p` with `μ(ℤ_p) = 1`)**.
- **n-dim ℂ Fourier-Gaussian lift** (the `Module.finrank ℝ V = 2n`
  generalisation of `complex_fourier_gaussian_pi`).

## References

- **Parent file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` after this
  PR: 1098 LOC, 29 theorems + 2 private helpers, 0 sorries, 0 axioms.
- **Direct predecessor (S6c ACT-1)**:
  `sessions/2026-06-04-s6c-act-1-integral-sq-exp-neg-sq.md` (ships
  `integral_sq_exp_neg_sq`, the 1-D real second moment used here).
- **Route spec (PREP-3 §5)**:
  `sessions/2026-06-02-s6c-prep-3-gaussianreal-variance-skeleton.md`.
- **Mathlib** at `2df2f0150c` (v4.26.0) — see Bearer recheck table above.

---

*End of S6c ACT-2. 0 axioms, 0 sorries, +2 theorems + 2 private helpers,
+177 LOC.*
