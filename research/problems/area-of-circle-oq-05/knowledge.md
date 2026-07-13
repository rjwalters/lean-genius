# area-of-circle-oq-05
## Gaussian Integral: All 4 theorems proved, 0 sorries

**Status: COMPLETE** — All sorries in `AreaOfCircleOQ05.lean` proved, 0 sorries remain.

**Parent**: [Area of Circle OQ-05: The Gaussian Integral](area-of-circle-oq-05)

---

## Summary

All four theorems in `AreaOfCircleOQ05.lean` now compile with 0 sorries:

1. `gaussian_integral_eq_sqrt_pi`: ∫ x, rexp(-(x²)) = √π
2. `scaled_gaussian`: ∀ a > 0, ∫ x, rexp(-(a·x²)) = √(π/a)
3. `standard_normal_normalization`: ∫ (1/√(2π)) · rexp(-(x²/2)) dx = 1
4. `radial_integral`: ∫₀^∞ r · rexp(-(r²)) dr = 1/2

The file also explains why π appears in the Gaussian integral: squaring gives
I² = ∫∫ e^{-(x²+y²)} dx dy = ∫₀^{2π} ∫₀^∞ r·e^{-r²} dr dθ = 2π · (1/2) = π.

---

## Session Log

### Session 2026-04-03 (Session 1) — Final
**Mode**: FRESH
**Outcome**: completed

**What Was Proved**:

1. `gaussian_integral_eq_sqrt_pi` — fixed for updated Mathlib API:
   - `integral_gaussian` now gives `∫ x, exp(-b*x²) = √(π/b)`, not `exp(-(b*x)²) = √π/|b|`
   - Used `simp_rw` to rewrite integrand `-(x²)` → `-(1:ℝ)*x²` before applying `integral_gaussian 1`
   - `div_one` simp cleans up `√(π/1) = √π`

2. `scaled_gaussian` — direct proof with new API:
   - `simp_rw` rewrites `-(a*x²)` → `-a*x²`
   - `exact integral_gaussian a` closes the goal

3. `standard_normal_normalization`:
   - Fixed `convert h using 2` bug (was going too deep, giving `⊢ 2 = π`)
   - Used `funext` approach: `have heq : f = g := funext fun x => by congr 1; ring` + `rw [heq, h]`
   - `congr 1; field_simp` proves `√(π/(1/2)) = √(2π)`
   - Fixed deprecated `integral_mul_left` → `integral_const_mul`

4. `radial_integral` — FTC for improper integrals:
   - Antiderivative: `F(r) = -(1/2)·exp(-r²)`, `F'(r) = r·exp(-r²)`
   - Lemmas: `integrableOn_Ioi_deriv_of_nonneg'`, `integral_Ioi_of_hasDerivAt_of_tendsto'`
   - Fixed `Pi.neg_apply` issue: `(hasDerivAt_pow 2 x).neg.exp` creates `Pi.neg` wrapper;
     `simp only [Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]` before `ring`
   - Fixed `𝓝` notation: replaced with `nhds` (avoids needing `open scoped Topology`)
   - Fixed `rexp_pos` → `exp_pos` (correct lemma name in `Real` namespace)
   - `norm_num [Real.exp_zero] at h` cleans up `0 - (-(1/2) * 1) = 1/2`

---

## Key Mathematical Insights

1. **API change**: `integral_gaussian (b : ℝ) : ∫ x, exp(-b*x²) = √(π/b)` (current Mathlib)
   vs old `∫ x, exp(-(b*x)²) = √π/|b|`. The `simp_rw` + `ring` pattern adapts between forms.

2. **Pi.neg_apply**: `HasDerivAt.neg` may produce `(-f) x` (Pi.neg applied to function `f`),
   which `ring` cannot reduce. Always add `simp only [Pi.neg_apply]` before `ring` when
   using `.neg.exp` chains.

3. **convert depth**: `convert h using 1` on integral equality leaves `ℝ`-equality goal
   (not function equality). `ext` fails. Use `simp_rw` + `exact h` pattern instead.

4. **FTC for improper integrals on [a,∞)**:
   - `integrableOn_Ioi_deriv_of_nonneg'`: integrability from antiderivative + limit
   - `integral_Ioi_of_hasDerivAt_of_tendsto'`: FTC giving `∫ f' = limit - F(a)`
   - Both in `Mathlib.MeasureTheory.Integral.IntegralEqImproper`
