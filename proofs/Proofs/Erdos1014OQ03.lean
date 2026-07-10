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

/-- **General-limit increment–ratio bridge.** For an eventually-nonzero sequence
`R` and any real `c`, the normalized increment `(R(l+1) − R(l))/R(l)` tends to `c`
**iff** the consecutive ratio `R(l+1)/R(l)` tends to `c + 1`.

The special case `c = 0` is `increment_div_tendsto_zero_iff_ratio_tendsto_one`. For
a geometrically-growing sequence whose ratio tends to a limit `L` (e.g. the
*diagonal* Ramsey number `R(k,k)`, whose growth ratio `R(k+1,k+1)/R(k,k)` tends to
`4`), this reads off the normalized-increment limit `L − 1` directly, exhibiting the
`o(R)` conclusion for #1014's off-diagonal `R(k,l)` (where `L = 1`) as the borderline
case of a general statement. -/
theorem increment_div_tendsto_iff_ratio_tendsto (R : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ᶠ l in atTop, R l ≠ 0) :
    Tendsto (fun l => (R (l + 1) - R l) / R l) atTop (𝓝 c) ↔
      Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 (c + 1)) := by
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

/-- **Increment-asymptotic reformulation.** Fix a comparison sequence `g`, with both
`R` and `g` eventually nonzero. Then the increment `R(l+1) − R(l)` is asymptotically
equivalent to `g` (normalized quotient `→ 1`) **iff** the *ratio-minus-one*
`R(l+1)/R(l) − 1` is asymptotically equivalent to `g/R`:

`(R(l+1) − R(l)) / g(l) → 1  ↔  (R(l+1)/R(l) − 1) / (g(l)/R(l)) → 1`.

This is the rigorous, hypothesis-honest form of the naive power-law expansion warned
against in the module docstring: an increment asymptotic `Δ_l(k) ~ g_k(l)` is
*exactly* a statement about the consecutive ratio, namely
`R(k,l+1)/R(k,l) − 1 ~ g_k(l)/R(k,l)`. The two normalized quantities are in fact
eventually equal, so neither direction of the equivalence adds a hypothesis beyond
eventual nonvanishing — a faithful reformulation, not a derivation that smuggles in
regularity. -/
theorem increment_asymptotic_iff_ratioSubOne_asymptotic (R g : ℕ → ℝ)
    (hR : ∀ᶠ l in atTop, R l ≠ 0) (hg : ∀ᶠ l in atTop, g l ≠ 0) :
    Tendsto (fun l => (R (l + 1) - R l) / g l) atTop (𝓝 1) ↔
      Tendsto (fun l => (R (l + 1) / R l - 1) / (g l / R l)) atTop (𝓝 1) := by
  have heq : (fun l => (R (l + 1) / R l - 1) / (g l / R l))
      =ᶠ[atTop] (fun l => (R (l + 1) - R l) / g l) := by
    filter_upwards [hR, hg] with l hR' hg'
    field_simp
    ring
  rw [tendsto_congr' heq]

/-- **Logarithmic increment–ratio bridge.** For an eventually-positive sequence
`R`, the *additive* increment of `log R` tends to `0` **iff** the consecutive ratio
tends to `1`:

`Real.log (R(l+1)) − Real.log (R l) → 0  ↔  R(l+1)/R(l) → 1`.

This is the logarithmic companion of `increment_div_tendsto_zero_iff_ratio_tendsto_one`:
since `log R(l+1) − log R(l) = log(R(l+1)/R(l))`, the log-increment is exactly the
log of the ratio, and `log` is a homeomorphism near `1` (with `log 1 = 0`). Applied to
`R(k, ·)`, Erdős #1014's ratio-convergence `R(k,l+1)/R(k,l) → 1` is thus equivalent to
the additive statement `log R(k,l+1) − log R(k,l) → 0`. -/
theorem log_increment_tendsto_zero_iff_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l) :
    Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 0) ↔
      Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1) := by
  have hpos1 : ∀ᶠ l in atTop, 0 < R (l + 1) := (tendsto_add_atTop_nat 1).eventually hpos
  -- the additive log-increment is the log of the ratio
  have heq : (fun l => Real.log (R (l + 1)) - Real.log (R l))
      =ᶠ[atTop] (fun l => Real.log (R (l + 1) / R l)) := by
    filter_upwards [hpos, hpos1] with l hl hl1
    rw [Real.log_div (ne_of_gt hl1) (ne_of_gt hl)]
  rw [tendsto_congr' heq]
  constructor
  · -- `log(ratio) → 0` ⟹ `ratio = exp(log ratio) → exp 0 = 1`
    intro h
    have hratio_pos : ∀ᶠ l in atTop, 0 < R (l + 1) / R l := by
      filter_upwards [hpos, hpos1] with l hl hl1 using div_pos hl1 hl
    have hexp : (fun l => R (l + 1) / R l)
        =ᶠ[atTop] (fun l => Real.exp (Real.log (R (l + 1) / R l))) := by
      filter_upwards [hratio_pos] with l hl using (Real.exp_log hl).symm
    rw [tendsto_congr' hexp]
    have := (Real.continuous_exp.tendsto 0).comp h
    simpa using this
  · -- `ratio → 1` ⟹ `log(ratio) → log 1 = 0` by continuity of `log` at `1`
    intro h
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h
    simpa using this

/-- **Corollary (log-increment vanishes).** If the consecutive ratio tends to `1`
then the additive log-increment `log R(l+1) − log R(l)` tends to `0`. The forward
direction packaged for direct use; fed Erdős #1014's `R(k,l+1)/R(k,l) → 1` it yields
`log R(k,l+1) − log R(k,l) → 0`. -/
theorem log_increment_tendsto_zero_of_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 0) :=
  (log_increment_tendsto_zero_iff_ratio_tendsto_one R hpos).mpr hratio

/-- **General-limit logarithmic increment–ratio bridge.** For an eventually-positive
sequence `R` and any positive limit `L`, the additive log-increment
`log R(l+1) − log R(l)` tends to `log L` **iff** the consecutive ratio `R(l+1)/R(l)`
tends to `L`:

`Real.log (R(l+1)) − Real.log (R l) → Real.log L  ↔  R(l+1)/R(l) → L`   (for `L > 0`).

The logarithmic companion of the general-limit multiplicative bridge
`increment_div_tendsto_iff_ratio_tendsto`, and the `L`-parametrized form of
`log_increment_tendsto_zero_iff_ratio_tendsto_one` (the case `L = 1`, where
`log 1 = 0`). Since `log R(l+1) − log R(l) = log(R(l+1)/R(l))`, the additive
log-increment is exactly `log` of the ratio; `exp`/`log` continuity transports the
limit both ways. For the *diagonal* Ramsey number `R(k,k)`, whose growth ratio
`R(k+1,k+1)/R(k,k)` tends to a limit `L ∈ [2, 4]`, this reads the additive
log-increment limit directly as `log L`. -/
theorem log_increment_tendsto_log_iff_ratio_tendsto (R : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hpos : ∀ᶠ l in atTop, 0 < R l) :
    Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 (Real.log L)) ↔
      Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 L) := by
  have hpos1 : ∀ᶠ l in atTop, 0 < R (l + 1) := (tendsto_add_atTop_nat 1).eventually hpos
  have heq : (fun l => Real.log (R (l + 1)) - Real.log (R l))
      =ᶠ[atTop] (fun l => Real.log (R (l + 1) / R l)) := by
    filter_upwards [hpos, hpos1] with l hl hl1
    rw [Real.log_div (ne_of_gt hl1) (ne_of_gt hl)]
  rw [tendsto_congr' heq]
  constructor
  · -- `log(ratio) → log L` ⟹ `ratio = exp(log ratio) → exp(log L) = L`
    intro h
    have hratio_pos : ∀ᶠ l in atTop, 0 < R (l + 1) / R l := by
      filter_upwards [hpos, hpos1] with l hl hl1 using div_pos hl1 hl
    have hexp : (fun l => R (l + 1) / R l)
        =ᶠ[atTop] (fun l => Real.exp (Real.log (R (l + 1) / R l))) := by
      filter_upwards [hratio_pos] with l hl using (Real.exp_log hl).symm
    rw [tendsto_congr' hexp]
    have := (Real.continuous_exp.tendsto (Real.log L)).comp h
    rw [Real.exp_log hL] at this
    simpa using this
  · -- `ratio → L` ⟹ `log(ratio) → log L` by continuity of `log` at `L ≠ 0`
    intro h
    have := (Real.continuousAt_log (ne_of_gt hL)).tendsto.comp h
    simpa using this

/-- **Additive–multiplicative increment equivalence.** For an eventually-positive
sequence `R`, the *normalized (multiplicative) increment* `(R(l+1) − R(l))/R(l)`
tends to `0` **iff** the *additive log-increment* `log R(l+1) − log R(l)` tends to
`0`.

Both quantities are, by the two bridges above, equivalent to the consecutive ratio
`R(l+1)/R(l)` tending to `1`, so they are equivalent to each other. This packages the
multiplicative bridge `increment_div_tendsto_zero_iff_ratio_tendsto_one` and the
logarithmic bridge `log_increment_tendsto_zero_iff_ratio_tendsto_one` into a single
statement that the two natural senses of "the increment is small" — additive on the
log scale, multiplicative relative to `R` — coincide for positive sequences. Applied
to `R(k, ·)`, Erdős #1014's ratio-convergence makes the two increment-smallness
notions interchangeable, so `Δ_l(k) = o(R(k,l))` and `log R(k,l+1) − log R(k,l) → 0`
carry exactly the same information. -/
theorem increment_div_tendsto_zero_iff_log_increment_tendsto_zero (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l) :
    Tendsto (fun l => (R (l + 1) - R l) / R l) atTop (𝓝 0) ↔
      Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 0) := by
  rw [increment_div_tendsto_zero_iff_ratio_tendsto_one R (hpos.mono fun _ hl => ne_of_gt hl),
    log_increment_tendsto_zero_iff_ratio_tendsto_one R hpos]


end Erdos1014OQ03
