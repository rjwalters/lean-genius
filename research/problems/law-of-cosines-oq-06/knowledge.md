# Knowledge Base: law-of-cosines-oq-06

## Summary

**COMPLETED** — Law of Sines for planar triangles, 0 axioms, 0 sorries.

The key result: `sin_angle_mul_norms` was converted from an `axiom` declaration to a proved `lemma` via the chain:

```
sin(arccos c) · N = sqrt(1-c²) · N = sqrt((1-c²)·N²) = sqrt(cross²) = |cross|
```

where the algebraic identity `(1-c²)·N² = N² - inner² = cross²` follows from `lagrange_2d` (2D Lagrange identity: `‖u‖²‖v‖² = ⟨u,v⟩² + (cross2D u v)²`).

---

## Session 2026-04-13 (Session 1) — Axiom Elimination

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Claimed `law-of-cosines-oq-06` from the candidate pool
- Read existing `LawOfSinesOQ06.lean` (265 lines, 0 sorries, 1 axiom `sin_angle_mul_norms`)
- Proved `sin_angle_mul_norms` as a lemma using:
  - `InnerProductGeometry.angle` definition (arccos of normalized inner product)
  - `Real.sin_arccos`: `sin(arccos x) = sqrt(1 - x²)` (unconditional in Mathlib)
  - `lagrange_2d`: `‖u‖²‖v‖² = ⟨u,v⟩² + (cross2D u v)²` (proved by `ring`)
  - Cauchy-Schwarz from Lagrange + `sq_nonneg`: `inner² ≤ N²`
  - `Real.sqrt_mul h_nn`: `sqrt(a·b) = sqrt(a)·sqrt(b)` with `a ≥ 0`
  - `Real.sqrt_sq hN_nn`: `sqrt(N²) = N` with `N ≥ 0`
  - `Real.sqrt_sq_eq_abs`: `sqrt(x²) = |x|`

### Key Findings

- `Real.sin_arccos` in Mathlib is unconditional (no hypothesis on range of input needed)
- The algebraic identity: `(1 - (inner/N)²) · N² = N² - inner² = cross²` (from lagrange_2d, via field_simp + nlinarith)
- The calc chain `sqrt(1-c²) · N = sqrt((1-c²)·N²) = sqrt(cross²) = |cross|` cleanly closes the proof
- Cauchy-Schwarz follows from Lagrange identity + `sq_nonneg (cross2D u v)` via `nlinarith`

### Proof of sin_angle_mul_norms

```lean
lemma sin_angle_mul_norms (u v : Vec2) (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.sin (InnerProductGeometry.angle u v) * (‖u‖ * ‖v‖) = |cross2D u v| := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hN_pos : 0 < ‖u‖ * ‖v‖ := mul_pos hnu hnv
  have hN_nn : 0 ≤ ‖u‖ * ‖v‖ := le_of_lt hN_pos
  have hlag := lagrange_2d u v
  rw [InnerProductGeometry.angle, Real.sin_arccos]
  have hcs : (@inner ℝ _ _ u v) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    nlinarith [sq_nonneg (cross2D u v), show (‖u‖ * ‖v‖) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 from by ring]
  have h_nn : 0 ≤ 1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2 := by
    rw [sub_nonneg, div_pow, div_le_one (by positivity)]
    exact hcs
  have key : (1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2) * (‖u‖ * ‖v‖) ^ 2 =
             (cross2D u v) ^ 2 := by
    field_simp [hN_pos.ne']
    nlinarith [hlag, show (‖u‖ * ‖v‖) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 from by ring]
  calc Real.sqrt (1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2) * (‖u‖ * ‖v‖)
      = Real.sqrt ((1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2) * (‖u‖ * ‖v‖) ^ 2) := by
            rw [Real.sqrt_mul h_nn, Real.sqrt_sq hN_nn]
    _ = Real.sqrt ((cross2D u v) ^ 2) := by rw [key]
    _ = |cross2D u v| := Real.sqrt_sq_eq_abs _
```

### Files Modified

- `proofs/Proofs/LawOfSinesOQ06.lean` — axiom → lemma, header updated (309 lines)
- `src/data/research/problems/law-of-cosines-oq-06.json` — status → completed

### Result

0 axioms, 0 sorries. Complete proof of Law of Sines for planar triangles via area approach.
