/-
# The Exact Stirling Asymptotic of the Even Unit-Ball Volumes

## Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-01-oq-01-oq-02

**Question** (as posed): Prove the exact asymptotics
`ω_n ~ √(2π/n) · (2πe/n)^(n/2)` from Stirling's formula in Mathlib.

**What we prove (and a correction).** The ancestor file proved only that the
unit `n`-ball volumes `ω_n = π^(n/2) / Γ(n/2+1)` tend to `0`. Here we pin the
*exact decay rate* of the even subsequence using Mathlib's Stirling formula
`Stirling.factorial_isEquivalent_stirling`:

  `ω_{2k} ~[atTop] (π e / k)^k / √(2π k)`.

Writing `n = 2k` (so `k = n/2`) this reads

  `ω_n ~ (2π e / n)^(n/2) / √(π n)`,

i.e. the universal leading constant is `1/√(π n)`, **not** `√(2π/n)` as the
question literally states. From `Γ(n/2+1) ~ √(π n)·(n/(2e))^(n/2)` (Stirling),

  `ω_n = π^(n/2)/Γ(n/2+1) ~ π^(n/2) / (√(π n)·(n/(2e))^(n/2))
        = (2π e / n)^(n/2) / √(π n)`,

and `1/√(π n) ≠ √(2π/n)` (they differ by the factor `√2·π`). So the proved
constant `1/√(π n)` is the correct one; we record the discrepancy honestly.

**Self-contained.** The committed ancestor `AreaOfCircleOQ01OQ02OQ01OQ01.lean`
does not currently compile under Mathlib `v4.26.0` (an orphaned doc-comment plus
a `Real.Gamma` rewrite that drifted). To keep this file independently
machine-checkable we re-derive the minimal infrastructure it needs — the
definition `ω`, the dimension-recurrence `ω_{n+2} = (2π/(n+2))·ω_n`, and the even
closed form `ω_{2k} = π^k/k!` — directly, then prove the new asymptotic. The
recurrence proof here is the drift-corrected version.

## Mathlib ingredients
- `Stirling.factorial_isEquivalent_stirling` — `n! ~ √(2π n)·(n/e)^n`.
- `Real.Gamma_add_one`, `Real.Gamma_one`, `Real.Gamma_pos_of_pos` — Γ recurrence.
- `Asymptotics.IsEquivalent.{mul,inv,congr_right}`, `isEquivalent_iff_tendsto_one`.
-/

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic

open Real Filter Asymptotics Nat
open scoped Topology

namespace BallVolumeAsymptotic

/-- The volume of the unit `n`-ball, `ω_n = π^(n/2) / Γ(n/2 + 1)`. -/
noncomputable def ω (n : ℕ) : ℝ := π ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)

/-- `ω_0 = 1` (the "volume" of a point). -/
theorem omega_zero : ω 0 = 1 := by
  simp [ω, Real.Gamma_one]

/-- Positivity of the half-integer Gamma values appearing in `ω`. -/
theorem gamma_half_pos (n : ℕ) : 0 < Real.Gamma ((n : ℝ) / 2 + 1) :=
  Real.Gamma_pos_of_pos (by positivity)

/-- **Dimension recurrence** `ω_{n+2} = (2π / (n+2)) · ω_n`.

This is the drift-corrected proof: after `↑(n+2)/2 = ↑n/2 + 1`, the `Γ` argument
becomes `(↑n/2 + 1) + 1` *definitionally*, so a single `Gamma_add_one` discharges
it (no second cast rewrite, which is where the ancestor file broke). -/
theorem omega_recurrence (n : ℕ) : ω (n + 2) = 2 * π / (↑n + 2) * ω n := by
  unfold ω
  have hcast1 : (↑(n + 2) : ℝ) / 2 = ↑n / 2 + 1 := by push_cast; ring
  have hpos : (0 : ℝ) < ↑n / 2 + 1 := by positivity
  have hΓ : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := gamma_half_pos n
  rw [hcast1, rpow_add pi_pos, rpow_one, Gamma_add_one hpos.ne']
  have hn2 : (↑n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- **Even closed form** `ω_{2k} = π^k / k!`.

Pure induction on the recurrence (no `Γ` manipulation), exactly as the classical
even-subsequence identity. -/
theorem omega_even_formula : ∀ k : ℕ, ω (2 * k) = π ^ k / (k ! : ℝ)
  | 0 => by simp [omega_zero]
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, omega_recurrence (2 * k),
        omega_even_formula k, Nat.factorial_succ]
    have h1 : (2 * (↑k : ℝ) + 2) ≠ 0 := by positivity
    have h2 : (↑(k !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_pos k).ne'
    have h3 : (↑k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **Exact even asymptotic.** The even unit-ball volumes satisfy

  `ω_{2k} ~[atTop] (π·e / k)^k / √(2π k)`.

This is the exact Stirling decay rate sharpening `ω_n → 0`: it identifies both
the super-exponential shape `(πe/k)^k` and the precise polynomial prefactor
`1/√(2πk)`. -/
theorem omega_even_isEquivalent :
    (fun k : ℕ => ω (2 * k)) ~[atTop]
      (fun k : ℕ => (π * Real.exp 1 / (k : ℝ)) ^ k / Real.sqrt (2 * π * k)) := by
  have hstir := Stirling.factorial_isEquivalent_stirling
  -- `ω(2k) = π^k * (k!)⁻¹` pointwise.
  have homega : (fun k : ℕ => ω (2 * k)) =ᶠ[atTop]
      (fun k : ℕ => (π : ℝ) ^ k * ((k ! : ℝ))⁻¹) := by
    filter_upwards with k
    rw [omega_even_formula k, div_eq_mul_inv]
  -- Transport Stirling through `π^k · (·)⁻¹`.
  have hmul : (fun k : ℕ => (π : ℝ) ^ k * ((k ! : ℝ))⁻¹) ~[atTop]
      (fun k : ℕ => (π : ℝ) ^ k *
        (Real.sqrt (2 * k * π) * ((k : ℝ) / Real.exp 1) ^ k)⁻¹) :=
    (IsEquivalent.refl).mul hstir.inv
  -- The transported right-hand side equals the clean closed form (for `k ≥ 1`).
  have hclean : (fun k : ℕ => (π : ℝ) ^ k *
        (Real.sqrt (2 * k * π) * ((k : ℝ) / Real.exp 1) ^ k)⁻¹) =ᶠ[atTop]
      (fun k : ℕ => (π * Real.exp 1 / (k : ℝ)) ^ k / Real.sqrt (2 * π * k)) := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hsqrt : Real.sqrt (2 * (k : ℝ) * π) = Real.sqrt (2 * π * k) := by
      rw [mul_right_comm]
    have hpow : π ^ k * (Real.exp 1 / (k : ℝ)) ^ k = (π * Real.exp 1 / (k : ℝ)) ^ k := by
      rw [← mul_pow, ← mul_div_assoc]
    rw [hsqrt, mul_inv, ← inv_pow, inv_div,
        show (π : ℝ) ^ k * ((Real.sqrt (2 * π * k))⁻¹ * (Real.exp 1 / (k : ℝ)) ^ k)
          = (π ^ k * (Real.exp 1 / (k : ℝ)) ^ k) * (Real.sqrt (2 * π * k))⁻¹ from by ring,
        hpow, div_eq_mul_inv ((π * Real.exp 1 / (k : ℝ)) ^ k)]
  exact homega.isEquivalent.trans (hmul.congr_right hclean)

/-- The exact even asymptotic restated as a limit of the normalised ratio:

  `ω_{2k} / ((π·e/k)^k / √(2π k)) → 1`. -/
theorem omega_even_ratio_tendsto_one :
    Tendsto (fun k : ℕ => ω (2 * k) /
        ((π * Real.exp 1 / (k : ℝ)) ^ k / Real.sqrt (2 * π * k)))
      atTop (nhds 1) := by
  have hne : ∀ᶠ k : ℕ in atTop,
      (π * Real.exp 1 / (k : ℝ)) ^ k / Real.sqrt (2 * π * k) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : (0 : ℝ) < π * Real.exp 1 / k :=
      div_pos (mul_pos pi_pos (Real.exp_pos 1)) hk0
    have h2 : (0 : ℝ) < Real.sqrt (2 * π * k) := Real.sqrt_pos.mpr (by positivity)
    exact (div_pos (pow_pos h1 k) h2).ne'
  exact (isEquivalent_iff_tendsto_one hne).mp omega_even_isEquivalent

end BallVolumeAsymptotic
