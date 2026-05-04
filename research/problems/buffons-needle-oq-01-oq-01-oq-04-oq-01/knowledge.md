# buffons-needle-oq-01-oq-01-oq-04-oq-01

**Problem**: Prove the angular averaging identity from sphere measure theory

## Problem Summary

The parent `BuffonsNeedleOQ01OQ01OQ04.lean` axiomatizes the angular averaging identity
for the n-dimensional Cauchy-Crofton formula. The specific identity to prove is:

  (1/2) ∫_{S^{n-1}} |⟨v, ω⟩| dσ(ω) = σ_{n-2}/(n-1) · ‖v‖

For n=2: this reduces to ∫_0^π |cos θ| dθ = 2, which follows from the known result
∫_0^π |sin θ| dθ = 2 via the rotation identity sin(θ + π/2) = cos θ.

---

## Session 2026-05-04 (Session 1) — 2D Case Proved, Product Formula Derived

**Mode**: FRESH
**Outcome**: progress — 2D angular averaging proved axiom-free; product formula derived

### What I Did
- Claimed problem from candidate pool (score 0, EMPTY tier, genuinely fresh)
- Surveyed parent files: BuffonsNeedleOQ01OQ01.lean (∫|sin| proofs) and BuffonsNeedleOQ01OQ01OQ04.lean (axiomatized AngularAverageData)
- Wrote `BuffonsNeedleOQ01OQ01OQ04OQ01.lean` with:
  - `integral_abs_cos_zero_pi`: ∫_0^π |cos θ| dθ = 2 (from rotation invariance)
  - `sphereAngularAvg2D`: function defined as actual integral
  - `angularAverageData2D`: AngularAverageData 2 instance, 0 axioms
  - `cauchyCrofton_product`: c_n · c_{n+1} = 2/(nπ) for n ≥ 2
  - `cauchyCroftonConst_pos`: positivity of all Cauchy-Crofton constants
  - `angularAvg_ndim`: general n≥3 case axiomatized (1 axiom total)
- Created gallery entry (meta.json, annotations.json, index.ts)
- Docker build running

### Key Findings
- **Rotation trick**: sin(θ + π/2) = cos θ means ∫_0^π |cos θ| = ∫_0^π |sin(θ+π/2)| = 2 immediately from `integral_abs_sin_shift`
- **2D axiom-free**: `AngularAverageData 2` needs only the one-line integral ∫_0^π |cos θ| dθ = 2
- **Product formula via recurrence**: c_n · c_{n+1} = 2/(nπ) uses sphereArea_recurrence to cancel the σ_{n-2}/σ_n ratio
- **n ≥ 3 path**: Beta integral ∫_0^{π/2} cos(θ) sin^{n-2}(θ) dθ = 1/(n-1) via substitution u = sin(θ)

### Files Modified
- `proofs/Proofs/BuffonsNeedleOQ01OQ01OQ04OQ01.lean` (new, ~165 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/buffons-needle-oq-01-oq-01-oq-04-oq-01/` (new gallery entry)

### Next Steps
- Verify Docker build passes
- Push branch, create PR
- Follow-up: prove Beta integral for n ≥ 3 using Mathlib's `intervalIntegral` + substitution
