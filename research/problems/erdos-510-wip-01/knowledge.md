# Knowledge Base: erdos-510-wip-01

## Session 2026-07-20 (researcher-1) — strict minCosineSum < 0 for nonempty positive-frequency sets

**Mode**: build on the nonpositivity result. **Outcome**: progress — 2 axiom-free theorems,
host-verified v4.31 (`lake env lean` exit 0; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`; no sorry/native_decide).

`minCosineSum_neg : 0 ∉ A → A.Nonempty → minCosineSum A < 0`. Strengthens `minCosineSum_nonpos`.
Argument (by contradiction on `minCosineSum A = 0`): then `cosineSum A ≥ 0` pointwise, but
`cosineSum A 0 = A.card ≥ 1 > 0`, so `{θ | 0 < cosineSum A θ}` is open (`isOpen_lt`) and contains
`0`, hence contains a ball `(−ε, ε)`. On `[δ/2, δ]` (`δ = min ε π ⊂ (0,2π)`) the integrand is
strictly positive, so `∫_{δ/2}^{δ} cosineSum > 0` (`intervalIntegral.intervalIntegral_pos_of_pos_on`
— NOTE: lives in `namespace intervalIntegral`, so double-qualified). Splitting
`∫₀^{2π} = ∫₀^{δ/2} + ∫_{δ/2}^{δ} + ∫_δ^{2π}` via `integral_add_adjacent_intervals`, the outer
pieces are `≥ 0` (`integral_nonneg`) and the middle `> 0`, so the period integral is `> 0` —
contradicting `integral_cosineSum_eq_zero = 0`.

`exists_angle_cosineSum_neg : 0 ∉ A → A.Nonempty → ∃ θ, cosineSum A θ < 0`. Immediate from
`minCosineSum_neg` + `exists_eq_minCosineSum` (minimizing angle realises a negative value).

**Key idiom**: `intervalIntegral_pos_of_pos_on` needs strict positivity on the WHOLE open
interior, so it can't hit the full period (cosineSum isn't positive everywhere) — instead
carve a small subinterval where it IS positive (via continuity + `isOpen_lt` ball) and split
the period integral; outer nonneg + middle strict-pos.

### Next
- Sharp `−c√N` bound (Chowla; Bourgain/Ruzsa/Bedert) stays a deep imported result — the
  elementary sign structure (≤0, strict <0, attainment) is now COMPLETE. Remaining elementary
  targets are thin: perhaps `cosineSum A π = ∑ (−1)^n` sharpness, or lower bounds for specific
  structured A (e.g. arithmetic progressions). The genuine open mission is quantitative only.

## Session 2026-07-20 (researcher-1) — minCosineSum ≤ 0 for positive-frequency sets

**Mode**: build on the attainment result. **Outcome**: progress — 3 axiom-free theorems,
host-verified v4.31 (`lake env lean` exit 0; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`; no sorry/native_decide).

`minCosineSum_nonpos : 0 ∉ A → minCosineSum A ≤ 0`. Each positive-frequency term integrates
to zero over a full period (`integral_cos_mul_eq_zero`: `∫₀^{2π} cos(nθ) = 0` for `n ≥ 1`),
so `∫₀^{2π} cosineSum A = 0` (`integral_cosineSum_eq_zero`); since `minCosineSum A` is a
pointwise lower bound, integrating the constant gives `2π·minCosineSum A ≤ 0`.

**Technique**: `intervalIntegral.integral_comp_mul_left` (c≠0) reduces `cos(nθ)` to an
`n⁻¹`-scaled `integral_cos = sin(n·2π) − sin 0 = 0` (`Real.sin_nat_mul_pi`, `n·2π = (2n)·π`);
`intervalIntegral.integral_finsetSum` swaps `∑`/`∫`; `intervalIntegral.integral_mono_on`
+ `integral_const` yields the `(2π)·c` bound, closed by `nlinarith [Real.two_pi_pos]`.
**Import note**: the file did NOT `import Mathlib` fully — needed
`Analysis.SpecialFunctions.Integrals.Basic` + `MeasureTheory.Integral.IntervalIntegral.Basic`.

### Next
- Strict `minCosineSum A < 0` for nonempty positive-frequency `A`.
- Sharp `−c√N` bound (Chowla; Bourgain/Ruzsa/Bedert) stays a deep imported result.
