# Knowledge Base: erdos-510-wip-01

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
