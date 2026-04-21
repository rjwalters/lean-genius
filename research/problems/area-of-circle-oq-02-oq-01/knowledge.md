# Knowledge Base: area-of-circle-oq-02-oq-01

**Problem**: Prove nball_volume_scaling — the scaling law Vol(Bⁿ(r)) = rⁿ·Vol(Bⁿ(1))
**Status**: COMPLETED (0 sorries, 0 axioms)
**Lean file**: `proofs/Proofs/AreaOfCircleOQ02OQ01.lean`

---

## Session 2026-04-21 (Session 1) — Proof Complete

**Mode**: FRESH  
**Outcome**: completed

### What I Did

Proved the n-ball volume scaling law for n ≥ 1 using `EuclideanSpace.volume_ball` from Mathlib.
Created gallery entry with meta.json, index.ts, annotations.json.

### Key Findings

1. **Mathlib has the result**: `EuclideanSpace.volume_ball` (in VolumeOfBalls.lean) gives:
   ```
   volume (ball x r) = (ofReal r)^n * ofReal(√π^n / Γ(n/2+1))
   ```
   This requires `[Nonempty ι]` (so n ≥ 1).

2. **Bridge lemma**: `(√π)^n = π^(n/2)` — needed to connect Mathlib's `√π^n` form
   to our `unitBallVolume n = π^(n/2)/Γ(n/2+1)`.
   Proof: `sqrt_eq_rpow` + `← rpow_natCast` + `← rpow_mul` + `ring`.

3. **Edge case bug found**: The parent axiom `nball_volume_scaling` is FALSE at n=0, r=0:
   - LHS: `volume(ball 0 0) = 0` (empty ball)
   - RHS: `ofReal(0^0 * 1) = 1` (since `0^0 = 1` in ℝ)
   - The correct hypothesis is `n ≥ 1` or `r > 0`.

4. **ENNReal lemmas used**:
   - `ENNReal.ofReal_pow hr`: `(ofReal r)^n = ofReal(r^n)` when `r ≥ 0`
   - `ENNReal.ofReal_mul h`: `ofReal a * ofReal b = ofReal(a*b)` when `a ≥ 0`

### Files Modified

- `proofs/Proofs/AreaOfCircleOQ02OQ01.lean` — new proof file (130 lines, 5 theorems)
- `src/data/proofs/area-of-circle-oq-02-oq-01/meta.json` — gallery entry
- `src/data/proofs/area-of-circle-oq-02-oq-01/index.ts` — gallery export
- `src/data/proofs/area-of-circle-oq-02-oq-01/annotations.json` — empty
- `src/data/proofs/listings.json` — added listing entry
- `src/data/research/problems/area-of-circle-oq-02-oq-01.json` — research tracking

### Next Steps

None — problem is complete. Potential follow-up:
- Fix the parent file `AreaOfCircleOQ02.lean` to replace the axiom with a theorem
  with hypothesis `(hn : 0 < n)`, then reuse `nball_volume_scaling_theorem`.
