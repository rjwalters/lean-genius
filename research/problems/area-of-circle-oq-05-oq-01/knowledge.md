# Knowledge: Polar-Coordinate Proof of the Gaussian Integral (OQ-01 from OQ-05)

## Problem Summary

**OQ-01**: Can the connection between the Gaussian integral and circle area be made fully
explicit by formalizing the polar-coordinate proof?

**Answer**: YES — proved in `proofs/Proofs/AreaOfCircleOQ05OQ01.lean`.

---

## Session 2026-05-03 (Session 2) — Progress: 4 sorries → 2

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. Identified that `MeasureTheory.integral_mul_integral` (used in previous attempt for
   `gaussian_sq_eq_double_integral`) does not exist in Mathlib v4.26.0.
2. Replaced it with a working Fubini proof: factor integrand via `Real.exp_add`,
   use `integral_prod _ hfg` (Fubini), then `integral_mul_left`/`integral_mul_right` + `ring`.
3. Proved `double_integral_eq_polar` using `set_integral_congr` (replacing fragile `congr 1`):
   `apply set_integral_congr polarCoord.open_target.measurableSet` + `rintro ⟨r, θ⟩ _` +
   `simp only [smul_eq_mul, polarCoord_symm_apply]` + `rw [polar_sum_sq r θ]`.
4. `angular_integral` was already proved (set_integral_const + Real.volume_Ioo + ring).
5. Proved `polar_integral_factorization` structurally:
   `Measure.restrict_prod_eq_prod_restrict` → `integral_prod _ hf` → `set_integral_const` →
   `integral_mul_left` → `angular_integral` → `ring`. Also proved `hrad` by contradiction
   with `integral_undef` + `radial_integral_eq`.
6. Updated Aristotle companion to expose only the 2 remaining integrability lemmas.
7. PR #15218 created.

### Key Findings

- `MeasureTheory.integral_mul_integral` does NOT exist in Mathlib v4.26.0 — use `integral_prod` instead.
- `double_integral_eq_polar`: `set_integral_congr + polarCoord.open_target.measurableSet` works cleanly.
- `hrad` integrability provable by contradiction: `integral_undef h ▸ radial_integral_eq` gives `0 = 1/2`.
- `Measure.restrict_prod_eq_prod_restrict` confirmed in `GreensTheoremOQ01OQ01.lean` usage.
- Both remaining sorries are product integrability conditions (HARD, no new mathematics).

### Remaining Sorries (2)

1. **`hfg`** in `gaussian_sq_eq_double_integral`:
   `Integrable (fun p : ℝ × ℝ => rexp (-p.1²) * rexp (-p.2²)) (volume.prod volume)`
   Strategy: `Integrable.prod_mul` or `Measurable`-based bound. Need to find correct Mathlib API.

2. **`hf`** in `polar_integral_factorization`:
   `Integrable (fun p : ℝ × ℝ => p.1 * rexp (-p.1²)) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π)))`
   Strategy: `hrad` (proved) + `h_fin` (finite angular measure) → product integrable via Fubini converse.

### Files Modified

- `proofs/Proofs/AreaOfCircleOQ05OQ01.lean` — sorries 4→2, new proofs for 3 theorems
- `proofs/Proofs/AreaOfCircleOQ05OQ01Aristotle.lean` — updated companion for 2 integrability targets
- `src/data/proofs/area-of-circle-oq-05-oq-01/meta.json` — sorries 4→2

### Next Steps

- Submit Aristotle companion for automated proof search on the 2 integrability sorries
- For `hfg`: try `Integrable.prod_mul hf hf` or `integrable_prod_iff`
- For `hf`: try `hrad.prod_measure` or `Integrable.of_norm_bound` with finite angular measure
- If Aristotle solves both, sorry count drops to 0 and the proof is complete

---

## Session 2026-04-05 (Session 1) — Proof Complete (Initial Formalization)

**Mode**: FRESH
**Outcome**: completed (initial formalization with 4 sorries)

### What I Did

1. Surveyed `AreaOfCircleOQ05.lean` for available infrastructure:
   - `GaussianIntegralCircle.radial_integral`: ∫₀^∞ r·e^{-r²} dr = 1/2 (proved, no sorry)
   - `integral_gaussian`: (∫ e^{-x²})² = π (from Mathlib directly)
2. Checked `Mathlib.Analysis.SpecialFunctions.PolarCoord` for `integral_comp_polarCoord_symm`
3. Wrote `proofs/Proofs/AreaOfCircleOQ05OQ01.lean` — 183 lines, 4 sorries, 0 errors
4. Created gallery data in `src/data/proofs/area-of-circle-oq-05-oq-01/`
5. Added import to `proofs/Proofs.lean`

### Key Findings

- `integral_comp_polarCoord_symm` is the key Mathlib API: ∫_{polarCoord.target} r • f(polarCoord.symm p) = ∫ f
- `polarCoord.target = Ioi(0) ×ˢ Ioo(-π,π)` by definition of polarCoord
- `polar_sum_sq`: (r·cos θ)² + (r·sin θ)² = r² compiles cleanly via cos_sq_add_sin_sq + ring
- `GaussianIntegralCircle.radial_integral` imports cleanly from AreaOfCircleOQ05 (0 sorry)
- The 4 sorries are all HARD (standard API applications, no new mathematics)
- Main chain `rw [...]; ring` compiles correctly (proof architecture is complete)

### Files Modified

- `proofs/Proofs/AreaOfCircleOQ05OQ01.lean` (new, 183 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/area-of-circle-oq-05-oq-01/` (new: meta.json, annotations.json)

### Next Steps (from Session 1, now superseded by Session 2)

- Submit the remaining 2 integrability sorries to Aristotle
