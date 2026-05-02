# Lp Riesz Representation for Sigma-Finite Measures

**Problem**: Generalize the Riesz representation for Lp duality from finite to sigma-finite measures.

**Parent**: `cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01` (0 sorries, proved IsFiniteMeasure case).

**Status**: ACT — Lean file created, 2 lemmas proved, 3 HARD sorries blueprinted.

---

## Session 2026-05-03 (Session 1)

**Mode**: FRESH
**Outcome**: progress — gallery entry created, 2 lemmas proved, 3 HARD sorries documented

### What I Did
- Read parent file (1077 lines, 0 sorries) to understand 7-step proof structure
- Created `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01.lean` (~230 lines)
- Proved `mem_spanningSets_eventually`: every point eventually enters spanningSets
- Proved `pointwise_mul_indicator_tendsto`: f(a)·1_{Sₙ}(a) → f(a) pointwise
- Identified correct Mathlib API: `tendsto_Lp_of_tendsto_ae` (Vitali), NOT the nonexistent `tendsto_Lp_of_dominated_convergence`
- Created gallery entry at `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01/`
- Added import to `proofs/Proofs.lean`

### Key Findings
- `tendsto_Lp_of_dominated_convergence` does NOT exist in Mathlib4 — Vitali's theorem (`tendsto_Lp_of_tendsto_ae`) requires proving `UnifIntegrable` + `UnifTight`
- `UnifTight` for `|hₙ| ≤ 2|f|` follows from `unifTight_const (2f) + eLpNorm_mono` (~20 lines)
- `UnifIntegrable` for `|hₙ| ≤ 2|f|` follows from `unifIntegrable_of` + cutoff argument (~40 lines)
- `eLpNorm_eq_lintegral_rpow_enorm` converts eLpNorm to lintegral for alternative DCT approach
- Lp restriction map infrastructure (Step A) is the largest gap (~150 lines)

### Files Modified
- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01.lean` (created)
- `proofs/Proofs.lean` (added import at line 317)
- `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01/` (created)
- `src/data/research/problems/cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01.json` (created)

### Next Steps
1. Prove `lp_truncation_tendsto_zero` using `tendsto_Lp_of_tendsto_ae` + `unifIntegrable_of` + `unifTight_const` (~80 lines)
2. Port parent's `integral_representation` to `[SigmaFinite μ]` for density extension step (~50 lines)
3. Build `localization_existence` via Lp restriction map infrastructure (~150 lines)
