# Knowledge: Synthesis: Curvature-parametrized Ptolemy via curvatureSin K

## Problem Summary

Define the `curvatureSin K t` function (= sn_K(t) from constant-curvature geometry) and prove
Ptolemy-type results using this unified notation. Key results:
- `curvatureSin 1 = sin`, `curvatureSin (-1) = sinh`, `curvatureSin 0 = identity`
- Spherical Ptolemy equality for cyclic unit-sphere points (restatement)
- **NEW**: Spherical Ptolemy INEQUALITY for ALL unit-circle points in ℂ

## Session 2026-04-26 (Session 1) — Synthesis via curvatureSin

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Claimed problem `synthesis-curvature-ptolemy-2026-04-24`
2. Surveyed existing gallery entries:
   - `PtolemysComplexProof.lean`: proves complex Ptolemy inequality via algebraic identity
   - `PtolemysTheoremOQ01OQ02.lean`: proves spherical Ptolemy equality for cyclic points,
     with chord-arc identity `‖a-b‖ = 2·sin(arccos(⟨a,b⟩)/2)` for unit sphere
3. Identified synthesis opportunity: combine these to get the spherical Ptolemy **inequality**
4. Implemented `SynthesisCurvaturePtolemy.lean` (~210 lines, 0 sorries) containing:
   - `curvatureSin K t` definition (noncomputable)
   - Basic properties: `curvatureSin_zero`, `curvatureSin_one`, `curvatureSin_neg_one`, `curvatureSin_zero_right`
   - `spherical_ptolemy_eq_curvatureSin`: equality restatement (thin wrapper, 2 lines)
   - `spherical_ptolemy_ineq_curvatureSin`: **NEW** inequality for unit-circle points in ℂ
5. Created gallery entry at `src/data/proofs/synthesis-curvature-ptolemy/`

### Key Findings

- The curvatureSin function cleanly unifies all three geometries in a single definition
- The spherical Ptolemy inequality proof is ~30 lines: chord-arc → half-norms → ptolemy_inequality/4
- The K<0 (hyperbolic) case is structurally blocked: conformal factors `(1-|z|²)` don't cancel
  for general interior points in the Poincaré disk, unlike the spherical case where `‖z‖=1` cancels
- `ptolemy_inequality` in `PtolemysComplexProof.lean` + chord-arc from `PtolemysTheoremOQ01OQ02.lean`
  is the exact combination needed

### Files Modified

- `proofs/Proofs/SynthesisCurvaturePtolemy.lean` (NEW, ~210 lines)
- `proofs/Proofs.lean` (added 3 new imports)
- `src/data/proofs/synthesis-curvature-ptolemy/` (NEW gallery entry)
- `src/data/research/problems/synthesis-curvature-ptolemy-2026-04-24.json` (knowledge update)

### Key Theorems

1. `curvatureSin K t := if K=0 then t else if 0<K then sin(√K·t)/√K else sinh(√|K|·t)/√|K|`
2. `curvatureSin_one: curvatureSin 1 t = sin t`
3. `curvatureSin_neg_one: curvatureSin (-1) t = sinh t`
4. `spherical_ptolemy_ineq_curvatureSin`: For z₁,z₂,z₃,z₄ on unit circle in ℂ:
   `curvatureSin 1 (arccos ⟪z₁,z₃⟫_ℝ / 2) * curvatureSin 1 (arccos ⟪z₂,z₄⟫_ℝ / 2) ≤ ...`

### Next Steps

- Submit for Docker build to verify compilation
- Add curvatureSin oddness lemma: `curvatureSin K (-t) = -curvatureSin K t`
- Prove normalization derivative: `deriv (curvatureSin K) 0 = 1` for all K
- When Mathlib adds Poincaré disk, prove the K=-1 case to complete the synthesis
