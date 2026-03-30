# Knowledge Base: yang-mills-transfer-matrix-oq-01

**Problem**: Does the mass gap survive the infinite-volume limit?
**Status**: IN-PROGRESS (4 sorries, 1 axiom in Exploration.lean)

## Current State

- **File**: `proofs/Proofs/YangMills/Exploration.lean` (~28K lines)
- **Sorries**: 4 (was 15)
- **Axioms**: 1

## Session 2026-03-30 (Session 1) - Eliminate routine sorries

**Mode**: FRESH (MODERATE knowledge)
**Outcome**: progress (15S->4S, 11 sorries eliminated)

### What I Did
Fixed 11 routine sorries (positivity, arithmetic, casting):
1. `dim4_decreases` (L17427): `pow_lt_pow_left` for Q^4 monotonicity
2. `wv_mass_sq_pos` (L21975-76): `linarith` from Nf > 0, chi_t > 0 hypotheses
3. `hook_length_positive` (L22503): `mul_pos` for eps2 * (l_leg + 1) > 0
4. `semiclassical_pos` (L22560): `Nat.cast_pos` for (N : R) > 0 from N >= 2
5. `csTopologicalMass_pos` (L24128): `mul_pos` + `Nat.cast_pos` for k * g_sq > 0
6. `csRenorm_gt_bare` (L24188): `push_cast` + `linarith` for (k + N : R) > (k : R)
7. `num_links_pos` (L25308-09): `omega` + `Nat.pos_pow_of_pos` for lattice dims
8. `tc_decreases_with_mu` (L25835): `div_pos` + `div_nonneg` + `linarith` for sq_lt_sq'
9. `sc_tension_monotone_in_N` (L27492): `nlinarith` + `sq_nonneg` for N^2 monotonicity

### Remaining 4 Sorries (need statement fixes)
1. **L15091** `tension_gap_ratio`: Mathematically incorrect. `sigma/m^2 = (g^4 N^2/(8pi)) / (g^2 N/(2pi))^2 = pi/2`, not `N/(4pi)`.
2. **L22071** `quantum_breaks_scale`: Missing `g != 0` hypothesis. When `g = 0`, `beta/(2*g) = beta/0 = 0` in Lean, so conclusion is unprovable.
3. **L22788** `coupling_controlled`: Complex MATHLIB-DRIFT. Real.log calc chain broke.
4. **L24965** `bv_field_count`: With `d >= 3, N >= 2`: `(3+3)*(4-1) = 18 < 24`. Needs `N >= 3`.

### Files Modified
- `proofs/Proofs/YangMills/Exploration.lean` (11 sorries eliminated)
- `src/data/proofs/yang-mills-transfer-matrix/meta.json` (sorries: 15->4)
- `src/data/research/problems/yang-mills-transfer-matrix-oq-01.json` (knowledge)

### Next Steps
- Fix tension_gap_ratio: correct the formula or verify physics
- Add g != 0 hypothesis to quantum_breaks_scale
- Fix bv_field_count N >= 2 -> N >= 3
- Rebuild coupling_controlled with current Mathlib API
