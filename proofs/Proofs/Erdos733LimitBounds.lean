/-
# Erdős Problem #733 — the limit constant, correctly bounded

**Parent.** `Erdos733Problem.lean` (registered). `f(n) = countLineCompatible n`
is the number of line-compatible sequences; Szemerédi–Trotter gives
`f(n) = exp(Θ(√n))`, encoded there as the axioms `lower_bound`
(`f(n) ≥ exp(c√n)`, `n ≥ 4`) and `upper_bound` (`f(n) ≤ exp(C√n)`, `n ≥ 2`).
Erdős's open question is whether `λ = limₙ log f(n)/√n` exists and what it is.

## Why this file exists — a defect in `Erdos733Problem.limit_bounds`

The registered `limit_bounds` (still behind a `sorry`) reads, in essence,

> `∀ λ, (∃ ε>0, ∀ n≥4, |log f(n)/√n − λ| < ε) → ∃ c C, c>0 ∧ C>0 ∧ c ≤ λ ∧ λ ≤ C`.

Its hypothesis is **too weak**: `ε` is existentially quantified with no
smallness requirement, so it merely says `g(n) := log f(n)/√n` is *bounded*
near `λ`. Taking `λ = 0` makes the hypothesis satisfiable (the sequence `g` is
bounded, by the two axioms) while the conclusion `∃ c>0, c ≤ 0` is impossible.
So the statement is **false as written** — it cannot be discharged, and its
`sorry` is an unprovable obligation rather than a routine gap.

## The correct statement (proved here, no `sorry`)

The intended fact is: *if the limit exists, it lies in `[c, C]`.* That is true
and elementary — squeeze the convergent sequence between the two axiomatic
bounds. The hypothesis must be genuine convergence (`Filter.Tendsto … (𝓝 λ)`),
not the weak `ε`-boundedness above.

`limit_in_bounds` below proves exactly this. The key estimate is that for
`n ≥ 4` the lower axiom already forces `f(n) > 0`, so on `n ≥ 4` both
`c ≤ g(n)` and `g(n) ≤ C` hold (take `log` of the bounds, then divide by the
positive `√n`); `ge_of_tendsto` / `le_of_tendsto` then transfer the inequalities
to the limit.

**Recommended registered-file patch (next build session).** Replace the
hypothesis of `Erdos733Problem.limit_bounds` with `Filter.Tendsto (fun n =>
log f(n)/√n) atTop (𝓝 λ)` and reuse this proof; or simply add the corollary
`limitConstant → λ ∈ [c, C]`. The open part (does the limit exist? what is its
value?) is untouched — see the open ORIENT PRs #24269 / #24295 for the
constant-chasing frontier.

**Build status.** Authored under a Docker/Aristotle blackout; this file is
**not yet registered in `Proofs.lean`**. Every Mathlib lemma is name-checked
against the pinned v4.26 toolchain.
-/

import Mathlib
import Proofs.Erdos733Problem

namespace Erdos733

open Filter Real

/-- **Corrected limit-bounds.** *If* the normalized log-count
`g(n) = log f(n)/√n` converges to `λ`, then `λ` lies strictly inside the
positive bracket `[c, C]` supplied by the two Szemerédi–Trotter axioms.

This is the true content the registered `limit_bounds` was meant to capture; its
`ε`-boundedness hypothesis was too weak (satisfiable at `λ = 0`, where the
conclusion fails). Convergence is the right hypothesis. -/
theorem limit_in_bounds (lam : ℝ)
    (h : Filter.Tendsto
          (fun n : ℕ => Real.log (countLineCompatible n) / Real.sqrt n)
          Filter.atTop (nhds lam)) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ c ≤ lam ∧ lam ≤ C := by
  obtain ⟨c, hc, hlow⟩ := lower_bound
  obtain ⟨C, hC, hupp⟩ := upper_bound
  refine ⟨c, C, hc, hC, ?_, ?_⟩
  · -- `c ≤ λ`: eventually `c ≤ g(n)`, then pass to the limit.
    refine ge_of_tendsto h ?_
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hn0 : 0 < n := by omega
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
    have hclog : c * Real.sqrt (n : ℝ) ≤ Real.log (countLineCompatible n : ℝ) := by
      have hle := Real.log_le_log (Real.exp_pos _) (hlow n hn)
      rwa [Real.log_exp] at hle
    exact (le_div_iff₀ hsqrt).mpr hclog
  · -- `λ ≤ C`: eventually `g(n) ≤ C`, then pass to the limit.
    refine le_of_tendsto h ?_
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hn0 : 0 < n := by omega
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
    have hfpos : (0 : ℝ) < (countLineCompatible n : ℝ) :=
      lt_of_lt_of_le (Real.exp_pos _) (hlow n hn)
    have hClog : Real.log (countLineCompatible n : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
      have hle := Real.log_le_log hfpos (hupp n (by omega))
      rwa [Real.log_exp] at hle
    exact (div_le_iff₀ hsqrt).mpr hClog

/-- Phrased directly against `Erdos733.limitConstant`: if the limit constant
exists, it is positive (and bounded above). This is the honest corollary —
existence itself remains the open Erdős question. -/
theorem limitConstant_mem_bounds (h : limitConstant) :
    ∃ lam c C : ℝ, c > 0 ∧ C > 0 ∧ c ≤ lam ∧ lam ≤ C ∧
      Filter.Tendsto (fun n : ℕ => Real.log (countLineCompatible n) / Real.sqrt n)
        Filter.atTop (nhds lam) := by
  obtain ⟨lam, hlam⟩ := h
  obtain ⟨c, C, hc, hC, hcl, hlC⟩ := limit_in_bounds lam hlam
  exact ⟨lam, c, C, hc, hC, hcl, hlC, hlam⟩

#check @limit_in_bounds
#check @limitConstant_mem_bounds

end Erdos733
