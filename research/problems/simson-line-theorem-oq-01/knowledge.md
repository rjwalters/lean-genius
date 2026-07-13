# Simson's Line Theorem (simson-line-theorem-oq-01)

## Problem Summary

For a point P on the circumcircle of triangle ABC, the feet of the perpendiculars
from P onto the three side-lines AB, BC, CA are collinear. The line they span is the
*Simson line* (Wallace line) of P.

**Status**: COMPLETE — fully verified, 0 axioms, 0 sorries.
**File**: `proofs/Proofs/SimsonLineTheorem.lean`

## Approach (complex unit-circle coordinates)

Model A, B, C, P as complex numbers and normalise the circumcircle to the unit circle
(`Complex.normSq = 1`), WLOG via an affine map of ℂ (preserves perpendicularity and
collinearity).

Key device: on the unit circle `conj z = z⁻¹`, so conjugation is a rational operation.

1. **Foot formula** `foot u v p = (u + v + p − u·v·conj p)/2` — the orthogonal projection
   of p onto the chord-line through unit-circle points u, v. Certified by:
   - `foot_perp`: `Re((p − foot)·conj(v − u)) = 0` (perpendicular to chord)
   - `foot_on_chord`: `Im((foot − u)·conj(v − u)) = 0` (lies on chord line)
   Both need only u, v on the circle (any p).

2. **Difference identity** (pure `ring`, no unit hypothesis):
   `foot b c p − foot a b p = (c − a)(1 − b·conj p)/2`
   `foot c a p − foot a b p = (c − b)(1 − a·conj p)/2`

3. **Collinearity**: three complex points are collinear iff
   `w := (z₂ − z₁)·conj(z₃ − z₁)` is real (`w = conj w`), equivalently `Im w = 0`
   (twice the signed area). `simson_key` proves `w = conj w`; `simson_collinear` gives
   `Im w = 0`. After substituting `conj z = z⁻¹`, `w − conj w` is a rational function that
   simplifies to 0 identically (`field_simp; ring`).

## Verification notes

- Foot formula vs. true perpendicular foot: confirmed numerically to 1e-13 for u,v on
  the unit circle and arbitrary p (2000 random samples).
- Collinearity identity confirmed in the ideal ⟨a·conj a−1, …⟩ via sympy Groebner reduction,
  and as a rational-function identity after conj→inverse substitution.

## Mathlib API used (v4.26.0)

- `Complex.mul_conj : z * conj z = ↑(normSq z)` (unit-circle → conj z = z⁻¹ bridge)
- `Complex.conj_im`, `Complex.conj_re`, `Complex.neg_re` (real/collinearity bridges)
- Avoided deprecated `Complex.abs`/`norm_eq_abs` and the non-constant `Complex.sq_abs`.

## Sessions

### Session 2026-06-16 (Session 1, researcher-12) — COMPLETE
**Mode**: FRESH. **Outcome**: completed.

- Surveyed the pool; routh-theorem-oq-01 turned out to be a DUPLICATE (already proven in
  `CevasTheoremOQ01OQ03.lean`, merged PR #15173) — synced its pool status to completed.
  pompeiu-theorem-oq-01 was under active 3-way contention (r9/r10/r11 uncommitted), so
  backed off it per anti-collision policy.
- Picked Simson (genuinely undone, unclaimed, clean ring-provable complex proof).
- Designed and numerically/symbolically verified the foot formula, difference identities,
  and collinearity criterion before writing Lean.
- Wrote `SimsonLineTheorem.lean`: 1 def, 6 theorems, 4 private lemmas; 0 axioms, 0 sorries.
- Registered import in `Proofs.lean`; authored gallery meta.json + annotations.json.

### Next Steps (follow-ups)
- Steiner deltoid: envelope of Simson lines as P moves on the circumcircle.
- Simson line bisects the segment from P to the orthocenter.
