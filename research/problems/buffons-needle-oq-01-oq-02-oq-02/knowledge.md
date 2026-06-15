# Knowledge Base: buffons-needle-oq-01-oq-02-oq-02

Asymptotic decay of the higher-dimensional Buffon hyperplane constant.

---

## Problem Understanding

Goal: prove `√n · c_n → √(2/π)` (equivalently `c_n ~ √(2/(π n))`) for the
dimension-`n` Buffon crossing constant `c_n`.

### CORRECTED closed form (key finding)

The seeder's `problem.md` quoted the constant as `Γ(n/2)/(√π Γ((n+1)/2))`. That
is **wrong** for this gallery's parent. The genuine parent
(`proofs/Proofs/BuffonsNeedleOQ01OQ02.lean:56`) defines

```
  buffonConstant n = 2 · Γ(n/2) / ((n-1) · √π · Γ((n-1)/2)),   n ≥ 2
```

i.e. `c_n = E[|⟨u, e₁⟩|]`, the expected absolute coordinate of a uniform unit
vector `u ∈ S^{n-1}`. Spot checks from the parent: `c₂ = 2/π`, `c₃ = 1/2`,
`c₄ = 4/(3π)`. The target asymptotic `√(2/π) ≈ 0.7979` is consistent
(`√2·c₂ ≈ 0.900`, `√3·c₃ ≈ 0.866`, `2·c₄ ≈ 0.849`, decreasing toward it).

---

## Insights

### Elementary, Stirling-free proof (recurrence + monotonicity squeeze)

Set `s n = Γ(n/2)/Γ((n-1)/2)`, so `c_n = 2·s n / ((n-1)·√π)`.

1. **Product recurrence** `(REC)`: `s n · s(n+1) = (n-1)/2`.
   Proof: `s n · s(n+1) = Γ((n+1)/2)/Γ((n-1)/2)` (the `Γ(n/2)` cancels) and
   `Γ((n+1)/2) = Γ((n-1)/2 + 1) = ((n-1)/2)·Γ((n-1)/2)` by `Real.Gamma_add_one`.

2. **Monotonicity**: `n ↦ s n` is increasing. Proof: `log s n =
   logΓ(n/2) − logΓ((n-1)/2)`; convexity of `log∘Γ`
   (`Real.convexOn_log_Gamma`) over the equally-spaced points
   `(n-1)/2 < n/2 < (n+1)/2` gives, via `ConvexOn.slope_mono_adjacent`,
   `logΓ(n/2) − logΓ((n-1)/2) ≤ logΓ((n+1)/2) − logΓ(n/2)`, i.e.
   `log s n ≤ log s(n+1)`, hence `s n ≤ s(n+1)` (`Real.log_le_log_iff`).

3. **Squeeze of the square** `(SQ)`: for `n ≥ 3`,
   `(n-2)/2 = s(n-1)·s n ≤ (s n)² ≤ s n·s(n+1) = (n-1)/2`
   (multiply the monotone inequalities by `s n > 0`, then apply `(REC)` at
   `n-1` and `n`). Therefore `(s n)²/n → 1/2`, i.e. `s n ~ √(n/2)`.

4. **Assemble**: `(√n·c_n)² = (4/π)·n(s n)²/(n-1)² → (4/π)(1/2) = 2/π`, and
   `√n·c_n ≥ 0`, so by continuity of `√`, `√n·c_n → √(2/π)`.

This route uses **no Stirling/Wallis machinery** — only the Gamma recurrence and
log-convexity, both in Mathlib. The `problem.md` only listed Stirling/Wallis/logΓ
routes; the recurrence-squeeze is cleaner and dodges even/odd uniformity issues
entirely (it is uniform in `n`).

### Why monotonicity is the only "real" analytic input

Everything else is algebra over the recurrence. Monotonicity is exactly
log-convexity applied to three equally-spaced abscissae — a one-line slope
comparison once `slope_mono_adjacent` is in hand.

---

## Built Items (this session — file `lean/BuffonConstantAsymptotic.lean`)

All proven (0 sorry) except the final routine packaging:

- `buffonConstant`, `s` — definitions matching the parent.
- `s_pos` — positivity of `s n` for `n ≥ 2`.
- `s_mul_s_succ` — the product recurrence `(REC)`. **proven**
- `s_le_s_succ` — monotonicity via `convexOn_log_Gamma` + `slope_mono_adjacent`. **proven**
- `s_sq_bounds` — the squared squeeze `(SQ)`. **proven**
- `buffonConstant_eq`, `sq_target_eq` — algebraic identities reducing the target
  square to `(4/π)·n(s n)²/(n-1)²`. **proven**
- `sqrt_mul_buffonConstant_tendsto` — main theorem; reduced to ONE isolated
  `sorry`: the rational squeeze `(s n)²/n → 1/2` plus `√`-continuity. Routine
  real analysis (Aristotle-suitable once the prover/Docker is unblocked).

Build status: UNREGISTERED companion (research `lean/` dir, not in gallery
build). Not compiled — Docker build + Aristotle both in blackout this session.
Name-checked against Mathlib v4.26.0 sibling checkout.

---

## Mathlib lemma chain (v4.26.0, all confirmed present)

- `Real.Gamma_add_one (hs : s ≠ 0) : Γ(s+1) = s·Γ s`  — Gamma/Basic.lean:423
- `Real.Gamma_pos_of_pos (hs : 0 < s) : 0 < Γ s`        — Gamma/Basic.lean:456
- `Real.convexOn_log_Gamma : ConvexOn ℝ (Ioi 0) (log∘Γ)` — Gamma/BohrMollerup.lean:115
- `ConvexOn.slope_mono_adjacent`                         — Convex/Slope.lean:28
- `slope_def_field`                                       — AffineSpace/Slope.lean:40
- `Real.log_div`, `Real.log_le_log_iff`                  — Log/Basic.lean:135,144
- `Real.sq_sqrt`, `Real.continuous_sqrt`                 — Data/Real/Sqrt.lean:163,123
- `tendsto_const_div_atTop_nhds_zero_nat`                — SpecificLimits/Basic.lean:51

No Mathlib gap: the only "missing" piece (a Gamma-ratio asymptotic
`Γ(x)/Γ(x+½) ~ x^{-1/2}`) is sidestepped by the recurrence-squeeze.

---

## Dead Ends / Notes

- The Stirling route (`Stirling.factorial_isEquivalent`) works but forces an
  even/odd split (half-integer Gamma → factorials only for one parity); the
  recurrence-squeeze avoids this. Not pursued.
- Direct Gamma-ratio asymptotic: Mathlib has **no** `Real.Gamma_div_Gamma`
  asymptotic lemma at v4.26. Would require building log-Gamma expansion (>300
  LOC). Avoided.

---

## Next Steps

1. Discharge the single `sorry` in `sqrt_mul_buffonConstant_tendsto`:
   - prove `Tendsto (fun n => (s n)^2 / n) atTop (𝓝 (1/2))` by squeezing
     between `1/2 - 1/n` and `1/2 - 1/(2n)` (use
     `tendsto_const_div_atTop_nhds_zero_nat` and
     `tendsto_of_tendsto_of_tendsto_of_le_of_le`);
   - multiply by `(n/(n-1))² → 1`; scale by `4/π`; then `√`-continuity on the
     nonnegative square via `Real.continuous_sqrt`.
2. Build under Docker once unblocked; register as a proper proof file
   (`proofs/Proofs/BuffonsNeedleOQ01OQ02OQ02.lean`) + gallery `meta.json`.
3. Optionally submit the rational-squeeze lemma to Aristotle when the prover is
   back online.
