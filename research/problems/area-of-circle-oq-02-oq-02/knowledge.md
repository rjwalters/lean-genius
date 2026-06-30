# Knowledge Base: area-of-circle-oq-02-oq-02

**Problem**: Prove Vₙ → 0 as n → ∞ — the unit n-ball volume vanishes in high dimensions
**Status**: COMPLETED (0 sorries, 0 axioms)
**Lean file**: `proofs/Proofs/AreaOfCircleOQ02OQ02.lean`

---

## Session 2026-06-20 (Session 1) — Proof Complete

**Mode**: FRESH (self-contained)
**Outcome**: completed

### What I Did

Proved `unitBallVolume_tendsto_zero : Tendsto unitBallVolume atTop (𝓝 0)` where
`unitBallVolume n = π^(n/2)/Γ(n/2+1)`, plus the measure-theoretic corollary
`volume_unitBall_toReal_tendsto_zero`. Created the gallery entry (meta.json).

### Proof Architecture (Gamma-free at the limit step)

1. **Even closed form**: `V₂ₘ = πᵐ/m!` exactly, because `Γ(m+1) = m!`
   (`Real.Gamma_nat_eq_factorial`) and `π^((2m)/2) = πᵐ` (`Real.rpow_natCast`).
   Tends to 0 by `FloorSemiring.tendsto_pow_div_factorial_atTop` (cⁿ/n! → 0).

2. **Odd bound**: `V₂ₘ₊₁ ≤ 2·πᵐ/m!`, by induction on m from the recurrence
   `Vₙ = Vₙ₋₂·2π/n`. Step factor `2π/(2m+3) ≤ π/(m+1)`. The succ step clears
   denominators with `div_le_div_iff₀` then closes with `nlinarith` fed
   `mul_le_mul_of_nonneg_left ih (0 ≤ 2π(k+1))` and `π^k·π > 0`. Squeeze to 0.

3. **Combine**: even and odd subsequences exhaust ℕ, so `Metric.tendsto_atTop` +
   `Nat.even_or_odd'` + an ε–N argument (`N = 2·Mₑ + 2·Mₒ + 1`, `omega` for the
   index bounds) gives the full limit. No dedicated even/odd combinator lemma needed.

4. **Measure headline**: `EuclideanSpace.volume_ball` + bridge `(√π)ⁿ = π^(n/2)`
   gives `volume(ball 0 1) = ofReal(Vₙ)` for n ≥ 1; `Tendsto.congr'` over
   `eventually_gt_atTop 0` transports the limit to `.toReal`.

### Gotchas (Mathlib v4.26.0)

- **Parent file `AreaOfCircleOQ02.lean` is BIT-ROTTED on main** — `unitBallVolume_recurrence`
  (line ~120) and `area_scaling_2d` (lines ~163/167, `hr.le` invalid since `hr : 0 ≤ r`)
  do not compile. This is why this file is fully self-contained instead of importing the
  parent. Flag for a mechanic. (Auditors miss it: cheap-check, not lake build.)
- `field_simp` output on the recurrence is **non-deterministic** (left `n·n⁻¹` one run,
  a different fraction the next). Replaced with deterministic
  `div_mul_eq_mul_div, div_div, div_eq_div_iff (mul_ne_zero ..) (mul_ne_zero ..); ring`.
- Recurrence: rewrite Nat `↑(n-2)` to `↑n - 2` (`Nat.cast_sub hn; norm_num`) BEFORE the
  exponent/Gamma rewrites so `ring` can verify `n = 2·((n-2)/2+1)`.
- `pi_nonneg.le` does NOT typecheck (`pi_nonneg : 0 ≤ π` already) — use `Real.pi_pos.le`.
- `le_div_iff₀` / `div_le_div_iff₀` are the current (non-deprecated) names.

### Files Added
- `proofs/Proofs/AreaOfCircleOQ02OQ02.lean` (229 lines, 12 thm / 2 lemma / 1 def)
- `src/data/proofs/area-of-circle-oq-02-oq-02/meta.json`

### Verification
`#print axioms unitBallVolume_tendsto_zero` → `[propext, Classical.choice, Quot.sound]`
(no `Lean.ofReduceBool`, no `sorryAx`). Docker build green (7743 jobs).

### Open Follow-ups
- Quantitative decay rate (Stirling): `Vₙ ~ (2πe/n)^(n/2)/√(nπ)`.
- One-statement non-monotonicity: increasing for n ≤ 5, decreasing for n ≥ 5.
- Ratio `Vₙ/2ⁿ` (ball vs bounding cube) → 0 super-exponentially.
