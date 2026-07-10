/-
Erdős Problem #1014 OQ-03: The consecutive off-diagonal Ramsey increment
Δ_l(k) = R(k, l+1) − R(k, l)

The parent problem (Erdős #1014) proves the *ratio* convergence
`R(k,l+1)/R(k,l) → 1`. OQ-03 asks whether the *increment* `Δ_l(k)` admits a clean
asymptotic formula `Δ_l(k) ~ g_k(l)`. The full asymptotic is OPEN and is **not**
asserted here.

## A cautionary observation about the naive derivation

A tempting "Approach A" derives the increment asymptotic from a power law
`R(k,l) ~ c_k · l^{k-1}/(log l)^{k-2}` by expanding
`Δ_l(k) = R(k,l)·((l+1)/l)^{k-1}(1+o(1)) − R(k,l)`. This is **not valid from
asymptotic equivalence alone**: the consecutive difference of a sequence is *not*
determined by its asymptotic equivalence class. For example `u_l = l²` and
`v_l = l² + l·sin l` satisfy `u ~ v` yet have wildly different increments
(`u_{l+1}−u_l = 2l+1` versus an `Θ(l)`-oscillating difference for `v`). So the
expansion secretly assumes the *ratio* asymptotic `R(k,l+1)/R(k,l) → ((l+1)/l)^{k-1}`,
which does not follow from `R(k,l) ~ g(l)`. A rigorous increment statement must
hypothesize the ratio (or a regularity/monotonicity) condition directly.

## What is proved here (unconditional, self-contained)

The **increment–ratio bridge**: for any positive sequence `R`, the normalized
increment equals the consecutive ratio minus one,

    (R(l+1) − R(l)) / R(l) = R(l+1)/R(l) − 1,

so the increment is `o(R(l))` **iff** the consecutive ratio tends to `1`. Applied to
`R(k,·)` this converts Erdős #1014's proven ratio-convergence
`R(k,l+1)/R(k,l) → 1` into the rigorous increment consequence
`Δ_l(k) = o(R(k,l))` — the correct, hypothesis-honest bridge from #1014 to increment
behavior, sidestepping the invalid power-law expansion above.

Verified, 0 axioms, 0 sorries, no `native_decide`.

References:
- Erdős [Er71], Problem 1014
- Erdős–Szekeres (1935), AKS (1980), Kim (1995): `R(3,l) = Θ(l²/log l)`
-/

import Mathlib

namespace Erdos1014OQ03

open Filter Topology

/-- **The increment–ratio identity.** For a sequence `R` with `R l ≠ 0`, the
normalized consecutive increment equals the consecutive ratio minus one:

`(R(l+1) − R(l)) / R(l) = R(l+1)/R(l) − 1`.

Purely algebraic; the engine of the increment–ratio bridge below. -/
theorem increment_div_eq_ratio_sub_one (R : ℕ → ℝ) (l : ℕ) (h : R l ≠ 0) :
    (R (l + 1) - R l) / R l = R (l + 1) / R l - 1 := by
  rw [sub_div, div_self h]

/-- **Increment–ratio bridge.** For an eventually-nonzero sequence `R`, the
normalized increment `(R(l+1) − R(l))/R(l)` tends to `0` **iff** the consecutive
ratio `R(l+1)/R(l)` tends to `1`.

Applied to `R(k, ·)` for fixed `k`, the right-hand side is exactly Erdős #1014's
ratio-convergence statement `R(k,l+1)/R(k,l) → 1`; the left-hand side says the
Ramsey increment is `o(R(k,l))`, i.e. `Δ_l(k) = R(k,l+1) − R(k,l) = o(R(k,l))`.
Thus #1014 rigorously yields `Δ_l(k) = o(R(k,l))` with no extra hypotheses — the
honest increment consequence, avoiding the (invalid-from-`~`-alone) power-law
expansion. -/
theorem increment_div_tendsto_zero_iff_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, R l ≠ 0) :
    Tendsto (fun l => (R (l + 1) - R l) / R l) atTop (𝓝 0) ↔
      Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1) := by
  have heq : (fun l => (R (l + 1) - R l) / R l)
      =ᶠ[atTop] (fun l => R (l + 1) / R l - 1) := by
    filter_upwards [hpos] with l hl using increment_div_eq_ratio_sub_one R l hl
  rw [tendsto_congr' heq]
  constructor
  · intro h
    have h1 := h.add_const 1
    simpa using h1
  · intro h
    have h1 := h.sub_const 1
    simpa using h1

/-- **Corollary (the increment is `o(R)`).** If the consecutive ratio tends to `1`
then the normalized increment tends to `0`. This is the forward direction, packaged
for direct use: fed Erdős #1014's `R(k,l+1)/R(k,l) → 1`, it delivers
`(R(k,l+1) − R(k,l))/R(k,l) → 0`. -/
theorem increment_div_tendsto_zero_of_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, R l ≠ 0)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => (R (l + 1) - R l) / R l) atTop (𝓝 0) :=
  (increment_div_tendsto_zero_iff_ratio_tendsto_one R hpos).mpr hratio

end Erdos1014OQ03
