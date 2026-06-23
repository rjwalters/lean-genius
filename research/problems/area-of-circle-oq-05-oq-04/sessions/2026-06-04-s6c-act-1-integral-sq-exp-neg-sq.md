# S6c ACT-1 — `integral_sq_exp_neg_sq` via `gaussianReal` variance shortcut

**Researcher**: researcher-3
**Date**: 2026-06-04
**Mode**: ACT (Lean code + theorem proof). Single new theorem, sorry-free, axiom-free.
**Predecessor**: S6c PREP-3 (`sessions/2026-06-02-s6c-prep-3-gaussianreal-variance-skeleton.md`).

## Summary

Closes the S6c ACT-1 frontier identified by PREP-3 §10. The load-bearing 1-D
real Gaussian second moment

    ∫_ℝ x² · exp(-x²) dx = √π / 2

is now committed as the new theorem `integral_sq_exp_neg_sq` in
`proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (Part 8: Diagonal Schur prerequisite).

Cumulative Lean state: **921 LOC / 27 theorems + 2 private helpers / 0 sorries
/ 0 axioms**. Docker-verified 3208/3208 jobs at v4.26.0 / Mathlib
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## Delta from PREP-3

The PREP-3 §3 skeleton was paste-ready; the final ACT-1 proof differs only in
minor tactical polishing:

| PREP-3 §3 (illustrative)                                                  | ACT-1 (final)                                                          |
|---------------------------------------------------------------------------|-------------------------------------------------------------------------|
| `set v : ℝ≥0 := (1/2 : ℝ≥0); have hv : v ≠ 0 := by unfold_let v; norm_num` | Direct `have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num`                    |
| `simpa using integral_id_gaussianReal …` for `hmean`                      | Term-mode: `hmean := integral_id_gaussianReal` (literal match)         |
| `conv at hvar => rhs; ext x; rw [hpdf x, smul_eq_mul, mul_assoc]`         | Hoist to a per-point `hpoint` lemma, then `simp_rw [hpoint] at hvar`   |
| `field_simp at hvar; linarith [hvar]`                                    | `field_simp at hvar; linarith` (same; `field_simp` discovers `hπ_ne`)  |

These changes shave ~5 LOC vs. the skeleton (final: 22 LOC of proof body, 38 LOC
of section including docstring), keeping the proof inside the PREP-3 budget
(~20-25 LOC).

## Risk register replay (PREP-3 §3)

1. **NNReal coercion friction.** Handled cleanly by a single `hv_coe :
   ((1/2 : ℝ≥0) : ℝ) = 1/2 := by norm_cast` and `rw [hv_coe]` inside the pdf
   simplification. No `push_cast` or `simp [NNReal.coe_one_div]` needed.
2. **`smul_eq_mul` ordering.** Resolved at the per-point `hpoint` step: after
   `rw [hpdf x]`, the residual `smul` collapses to `mul` via `smul_eq_mul`,
   then `ring` closes.
3. **Final algebra.** `field_simp` clears `(√π)⁻¹` and `1/2`, leaving
   `2 * I = √π`. `linarith` then finishes (treating `√π` as an opaque variable;
   the goal `I = √π / 2 ↔ 2*I = √π` is linear).
4. **`MemLp 2` integrability.** Not needed — `variance_of_integral_eq_zero`
   does not require this hypothesis; only `AEMeasurable X μ` is taken.

## Proof structure (6 numbered steps)

1. **Parameters.** `hv : (1/2 : ℝ≥0) ≠ 0`, `hv_coe : ((1/2 : ℝ≥0) : ℝ) = 1/2`.
2. **Mean = 0.** Term-mode: `integral_id_gaussianReal` specialised at μ = 0.
3. **Variance shortcut.** `variance_of_integral_eq_zero` chains with
   `variance_id_gaussianReal` to give `∫ x² ∂gaussianReal 0 (1/2) = 1/2`.
4. **Bridge to Lebesgue.** `integral_gaussianReal_eq_integral_smul` rewrites
   the gaussianReal-integral to a pdf-weighted Lebesgue-integral.
5. **PDF closed form.** `gaussianPDFReal 0 (1/2) x = (√π)⁻¹·exp(-x²)` via
   `unfold gaussianPDFReal`, `rw [hv_coe, sub_zero]`, two `show ... from by ring`
   simplifications.
6. **Algebraic close.** Per-point `hpoint` factoring `(√π)⁻¹` out of the
   integrand, then `integral_const_mul` pulls it out of the integral, and
   `field_simp; linarith` solves the resulting linear equation.

## Bearer recheck (PREP-3 §2.2 — confirmed live at build time)

All five bearers identified by PREP-3 are present, callable, and produce the
expected signatures at SHA `2df2f0150c`:

| Identifier                              | Module                                              | Line | Status         |
|-----------------------------------------|-----------------------------------------------------|------|----------------|
| `gaussianPDFReal` (def)                 | `Probability/Distributions/Gaussian/Real.lean`      | 49   | ✓ used        |
| `integral_id_gaussianReal`              | (same)                                              | 493  | ✓ used        |
| `variance_id_gaussianReal`              | (same)                                              | 528  | ✓ used        |
| `integral_gaussianReal_eq_integral_smul`| (same)                                              | 249  | ✓ used        |
| `variance_of_integral_eq_zero`          | `Probability/Moments/Variance.lean`                 | 149  | ✓ used        |

(PREP-3 cited `gaussianPDFReal` at line 48; current file places `def` on
line 49 with a docstring comment immediately above. Semantics unchanged.)

## Linter notes

The build emits one informational warning:
- `linter.unnecessarySimpa` flagged the earlier `simpa using
  integral_id_gaussianReal …` form in `hmean`; resolved by switching to
  term-mode (the lemma's conclusion matches the hypothesis verbatim).

No other warnings on our file; the unrelated `unused variable ha` warning at
`Proofs/AreaOfCircleOQ05.lean:60:33` is pre-existing.

## Sorry / axiom delta

- Cumulative: **0 sorries, 0 axioms** (unchanged).
- New theorem: 22 LOC of proof body, 0 sorries, 0 axioms.

## Anti-targets (this ACT-1 PR)

- Does NOT touch `problem.md`, `state.md` of the flat dir, the merged S4b /
  S6a / S6b / S6c family files, the gallery `meta.json`, or any JSON.
- Does NOT consolidate the flat-vs-canonical research directory split
  (mechanic-sweep scope per
  `feedback_researcher_canonical_vs_flat_research_problems_dir_divergence`).
- Does NOT ship the n-dim Schur diagonal assembly (PREP-3 §5 → S6c ACT-2,
  separate follow-up PR).
- Does NOT initialise the gallery entry `src/data/proofs/area-of-circle-oq-05-oq-04/`
  (mechanic / gallery-init scope).

## Next steps (S6c ACT-2)

Per PREP-3 §5, ship in a follow-up PR (~40-55 LOC):

1. `complex_gaussian_integral_norm_sq : ∫ w : ℂ, ‖w‖² · exp(-‖w‖²) = π` via
   `Complex.measurableEquivRealProd` + Fubini, using `integral_sq_exp_neg_sq`
   on one axis and `integral_gaussian` (b = 1) on the perpendicular.
2. `schur_orthogonality_complex_gaussian_diag` via
   `integral_fintype_prod_volume_eq_prod` and the n-1-fold
   `complex_gaussian_integral_unit_norm`.

Both routes are unchanged from PREP-2 §3.2-3.3 and PREP-3 §5; no further PREP
needed before ACT-2.

## References

- **Parent file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (921 LOC, 27
  theorems + 2 private helpers, 0 sorries, 0 axioms after this PR).
- **Direct predecessor (PREP-3)**:
  `sessions/2026-06-02-s6c-prep-3-gaussianreal-variance-skeleton.md`.
- **Mathlib** at `2df2f0150c` (v4.26.0):
  - `Mathlib/Probability/Distributions/Gaussian/Real.lean:49,249,493,528`.
  - `Mathlib/Probability/Moments/Variance.lean:149`.

---

*End of S6c ACT-1. 0 axioms, 0 sorries, 22 LOC proof body, 3208/3208 jobs.*
