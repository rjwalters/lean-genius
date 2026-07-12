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
  rw [tendsto_congr' heq]

/-- **Sharp increment bridge (`l`-scaled, limit form).** The `β`-parametrized companion
to `increment_asymptotic_iff_ratioSubOne_asymptotic`, valid for *every* `β` including
`β = 0`. Scaling both the normalized increment and the ratio-excess by `l`, the two have
the same limit:

`((R(l+1) − R(l))/R(l))·l → β  ↔  (R(l+1)/R(l) − 1)·l → β`.

The right-hand side is the honest *sharp* ratio hypothesis; the left-hand side is exactly
the power-law increment `Δ_l ~ β·R(l)/l`. This is the rigorous content of the naive
"Approach A" expansion warned against in the module docstring: under the sharp ratio
hypothesis (and only then) the increment inherits the leading power-law term. For the
conjectured `R(k,l) ~ c_k·l^{k-1}/(log l)^{k-2}` the target is `β = k − 1`, but that sharp
ratio asymptotic is the open regular-variation input, not proved here. Unlike the
general-`g` reformulation above (which needs `g` eventually nonzero and so cannot express
`β = 0`), this limit form covers the boundary `β = 0` — the exact threshold between
`Δ_l = o(R/l)` and genuine power growth. The two scaled quantities are eventually equal,
so neither direction adds a hypothesis beyond eventual nonvanishing. -/
theorem increment_div_mul_tendsto_iff_ratioSubOne_mul_tendsto (R : ℕ → ℝ) (β : ℝ)
    (hpos : ∀ᶠ l in atTop, R l ≠ 0) :
    Tendsto (fun l => ((R (l + 1) - R l) / R l) * (l : ℝ)) atTop (𝓝 β) ↔
      Tendsto (fun l => (R (l + 1) / R l - 1) * (l : ℝ)) atTop (𝓝 β) := by
  have heq : (fun l => ((R (l + 1) - R l) / R l) * (l : ℝ))
      =ᶠ[atTop] (fun l => (R (l + 1) / R l - 1) * (l : ℝ)) := by
    filter_upwards [hpos] with l hl
    rw [increment_div_eq_ratio_sub_one R l hl]
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

/-- **The gap increment telescopes into unit increments.** The `m`-step increment is the exact
(unconditional) sum of the `m` consecutive unit increments:

`R(l+m) − R(l) = ∑_{i<m} (R(l+i+1) − R(l+i))`.

This is the additive backbone of the gap-convergence theorems below (`increment_gap_div_tendsto_zero`
etc.): each summand is a shifted unit increment, so a bound on unit increments controls the whole
window exactly, not merely asymptotically. -/
theorem increment_gap_eq_sum (R : ℕ → ℝ) (l m : ℕ) :
    R (l + m) - R l = ∑ i ∈ Finset.range m, (R (l + i + 1) - R (l + i)) := by
  have h := Finset.sum_range_sub (fun i => R (l + i)) m
  simpa using h.symm

/-- **The log-gap increment telescopes into unit log-increments.** Applying `increment_gap_eq_sum`
to `log ∘ R`: the `m`-step log-increment is the exact sum of the `m` consecutive unit
log-increments,

`log R(l+m) − log R(l) = ∑_{i<m} (log R(l+i+1) − log R(l+i))`.

The multiplicative telescoping `R(l+m)/R(l) = ∏_{i<m} R(l+i+1)/R(l+i)` referenced by
`ratio_gap_tendsto_one`, read additively through the logarithm — the exact identity underlying
`log_increment_gap_tendsto_zero`. -/
theorem log_increment_gap_eq_sum (R : ℕ → ℝ) (l m : ℕ) :
    Real.log (R (l + m)) - Real.log (R l)
      = ∑ i ∈ Finset.range m, (Real.log (R (l + i + 1)) - Real.log (R (l + i))) := by
  have h := Finset.sum_range_sub (fun i => Real.log (R (l + i))) m
  simpa using h.symm

/-- **The gap-ratio telescopes into a product of unit ratios.** The multiplicative
companion of `increment_gap_eq_sum` (additive) and `log_increment_gap_eq_sum`
(log-additive): whenever `R` is nonzero across the window `[l, l+m]`, the `m`-step
ratio is the exact product of the `m` consecutive unit ratios,

`R(l+m) / R l = ∏_{i<m} R(l+i+1) / R(l+i)`.

This is the multiplicative telescoping `R(l+m)/R(l) = ∏ R(l+i+1)/R(l+i)` invoked (but
not previously stated) in the docstrings of `ratio_gap_tendsto_one` and
`ratio_gap_tendsto_pow`; it is their exact algebraic backbone, made explicit here.
Proof: induction on `m`, splitting off one factor with `div_mul_div_cancel₀` (exactly
as in `ratio_gap_tendsto_one`'s inductive step). -/
theorem ratio_gap_eq_prod (R : ℕ → ℝ) (l m : ℕ) (hne : ∀ i ≤ m, R (l + i) ≠ 0) :
    R (l + m) / R l = ∏ i ∈ Finset.range m, (R (l + i + 1) / R (l + i)) := by
  revert hne
  induction m with
  | zero =>
      intro hne
      simp only [Finset.range_zero, Finset.prod_empty, Nat.add_zero]
      exact div_self (by simpa using hne 0 le_rfl)
  | succ m ih =>
      intro hne
      show R (l + m + 1) / R l = ∏ i ∈ Finset.range (m + 1), (R (l + i + 1) / R (l + i))
      rw [Finset.prod_range_succ,
          ← ih (fun i hi => hne i (Nat.le_succ_of_le hi)),
          mul_comm, div_mul_div_cancel₀ (hne m (Nat.le_succ m))]

/-- **The product of consecutive ratios tends to `1`.** Under Erdős #1014's ratio
convergence `R(l+1)/R(l) → 1`, for every fixed gap `m` the product form of the
gap-ratio converges,

`∏_{i<m} R(l+i+1) / R(l+i) → 1`.

The product-form reading of `ratio_gap_tendsto_one` (to which it is equal on the
nonvanishing window by `ratio_gap_eq_prod`): each of the `m` factors is a shifted copy
of the unit ratio, so each tends to `1`, and the finite product of null-factors tends to
`∏ 1 = 1` (`tendsto_finset_prod`). Notably this needs **no** positivity hypothesis — it
holds for the product of shifted ratios directly. -/
theorem prod_consecutive_ratios_tendsto_one (R : ℕ → ℝ) (m : ℕ)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => ∏ i ∈ Finset.range m, (R (l + i + 1) / R (l + i))) atTop (𝓝 1) := by
  have h : Tendsto (fun l => ∏ i ∈ Finset.range m, (R (l + i + 1) / R (l + i))) atTop
      (𝓝 (∏ _i ∈ Finset.range m, (1 : ℝ))) := by
    refine tendsto_finset_prod _ (fun i _ => ?_)
    have hi := hratio.comp (tendsto_add_atTop_nat i)
    simpa using hi
  simpa using h

/-- **Bounded-gap ratio convergence.** If the consecutive ratio `R(l+1)/R(l)` tends to
`1` (Erdős #1014) and `R` is eventually positive, then for *every fixed gap* `m` the
gap-ratio `R(l+m)/R(l)` also tends to `1`.

Telescoping `R(l+m)/R(l) = ∏_{i<m} R(l+i+1)/R(l+i)` into `m` consecutive ratios — each
`→ 1` (the `i`-th being the unit-gap ratio shifted by `i`) — the product of finitely many
null-ratios is `1`; formally by induction on `m`, splitting off one factor with
`div_mul_div_cancel₀`. Applied to `R(k, ·)`, #1014's unit-gap convergence self-strengthens
to `R(k,l+m)/R(k,l) → 1` for every fixed `m`: Ramsey growth is smooth over any bounded
window of the second index, not merely between neighbours. -/
theorem ratio_gap_tendsto_one (R : ℕ → ℝ) (m : ℕ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => R (l + m) / R l) atTop (𝓝 1) := by
  induction m with
  | zero =>
      have heq : (fun l => R (l + 0) / R l) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
        filter_upwards [hpos] with l hl
        simp [div_self (ne_of_gt hl)]
      rw [tendsto_congr' heq]
      exact tendsto_const_nhds
  | succ m ih =>
      have hpos_m : ∀ᶠ l in atTop, 0 < R (l + m) :=
        (tendsto_add_atTop_nat m).eventually hpos
      have hmul : Tendsto
          (fun l => R (l + m + 1) / R (l + m) * (R (l + m) / R l)) atTop (𝓝 1) := by
        have hshift := hratio.comp (tendsto_add_atTop_nat m)
        simpa using hshift.mul ih
      refine hmul.congr' ?_
      filter_upwards [hpos_m] with l hlm
      show R (l + m + 1) / R (l + m) * (R (l + m) / R l) = R (l + m + 1) / R l
      exact div_mul_div_cancel₀ (ne_of_gt hlm)

/-- **Corollary (bounded-gap increment is `o(R)`).** Under #1014's ratio convergence,
the increment `R(l+m) − R(l)` over any fixed gap `m` is `o(R(l))`:
`(R(l+m) − R(l))/R(l) → 0`. Immediate from `ratio_gap_tendsto_one`, since
`(R(l+m) − R(l))/R(l) = R(l+m)/R(l) − 1`; the `m = 1` case is
`increment_div_tendsto_zero_of_ratio_tendsto_one`. -/
theorem increment_gap_div_tendsto_zero (R : ℕ → ℝ) (m : ℕ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => (R (l + m) - R l) / R l) atTop (𝓝 0) := by
  have hgap := ratio_gap_tendsto_one R m hpos hratio
  have heq : (fun l => (R (l + m) - R l) / R l)
      =ᶠ[atTop] (fun l => R (l + m) / R l - 1) := by
    filter_upwards [hpos] with l hl
    rw [sub_div, div_self (ne_of_gt hl)]
  rw [tendsto_congr' heq]
  have := hgap.sub_const 1
  simpa using this

/-- **General-limit additive–multiplicative increment equivalence.** For an
eventually-positive sequence `R` and any `c` with `c + 1 > 0`, the *normalized
(multiplicative) increment* `(R(l+1) − R(l))/R(l)` tends to `c` **iff** the *additive
log-increment* `log R(l+1) − log R(l)` tends to `log (c + 1)`.

The `c = 0` case is `increment_div_tendsto_zero_iff_log_increment_tendsto_zero`
(where `log (0 + 1) = 0`). Both quantities are, by the two general-limit bridges,
equivalent to the consecutive ratio tending to `c + 1`
(`increment_div_tendsto_iff_ratio_tendsto` and
`log_increment_tendsto_log_iff_ratio_tendsto` at `L = c + 1`), hence equivalent to each
other. This is the `c`-parametrized form of the additive–multiplicative equivalence:
for a geometrically-growing sequence whose normalized increment tends to `c` (ratio
`→ c + 1`), the additive log-increment tends to `log (c + 1)`. -/
theorem increment_div_tendsto_iff_log_increment_tendsto (R : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c + 1) (hpos : ∀ᶠ l in atTop, 0 < R l) :
    Tendsto (fun l => (R (l + 1) - R l) / R l) atTop (𝓝 c) ↔
      Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop
        (𝓝 (Real.log (c + 1))) := by
  rw [increment_div_tendsto_iff_ratio_tendsto R c (hpos.mono fun _ hl => ne_of_gt hl),
    log_increment_tendsto_log_iff_ratio_tendsto R (c + 1) hc hpos]

/-- **Logarithmic bounded-gap increment vanishes.** Under Erdős #1014's ratio
convergence `R(l+1)/R(l) → 1` (with `R` eventually positive), the *additive
log-increment over any fixed gap* `m` tends to `0`:
`log R(l+m) − log R(l) → 0`.

The logarithmic companion of `increment_gap_div_tendsto_zero` (the multiplicative
bounded-gap increment), and the `m`-fold form of
`log_increment_tendsto_zero_of_ratio_tendsto_one` (the unit gap `m = 1`). Since
`log R(l+m) − log R(l) = log (R(l+m)/R(l))` and the gap-ratio `R(l+m)/R(l) → 1`
(`ratio_gap_tendsto_one`), continuity of `log` at `1` (with `log 1 = 0`) gives the
claim. So under #1014, Ramsey growth is additively smooth on the log scale over every
bounded window of the second index. -/
theorem log_increment_gap_tendsto_zero (R : ℕ → ℝ) (m : ℕ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => Real.log (R (l + m)) - Real.log (R l)) atTop (𝓝 0) := by
  have hgap := ratio_gap_tendsto_one R m hpos hratio
  have hpos_m : ∀ᶠ l in atTop, 0 < R (l + m) := (tendsto_add_atTop_nat m).eventually hpos
  have heq : (fun l => Real.log (R (l + m)) - Real.log (R l))
      =ᶠ[atTop] (fun l => Real.log (R (l + m) / R l)) := by
    filter_upwards [hpos, hpos_m] with l hl hlm
    rw [Real.log_div (ne_of_gt hlm) (ne_of_gt hl)]
  rw [tendsto_congr' heq]
  have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hgap
  simpa using this

/-- **General-limit bounded-gap ratio.** If the consecutive ratio `R(l+1)/R(l)` tends
to a limit `L` (with `R` eventually positive), then for *every fixed gap* `m` the
gap-ratio `R(l+m)/R(l)` tends to `L^m`:

`R(l+m)/R(l) → L^m`.

The general-`L` companion of `ratio_gap_tendsto_one` (its `L = 1` special case, where
`1^m = 1`). Telescoping `R(l+m)/R(l) = ∏_{i<m} R(l+i+1)/R(l+i)` into `m` consecutive
ratios — each `→ L` — the product of `m` copies of `L` is `L^m`; formally by induction on
`m`, splitting off one factor with `div_mul_div_cancel₀`. For the *diagonal* Ramsey number
`R(k,k)`, whose growth ratio `R(k+1,k+1)/R(k,k)` is conjectured to tend to a limit
`L ∈ [2, 4]`, this reads off the growth `R(k+m,k+m)/R(k,k) → L^m` over any fixed window of
the diagonal index — the exponential-in-the-window statement whose off-diagonal
`L = 1` degeneration is #1014's smoothness `ratio_gap_tendsto_one`. -/
theorem ratio_gap_tendsto_pow (R : ℕ → ℝ) (L : ℝ) (m : ℕ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 L)) :
    Tendsto (fun l => R (l + m) / R l) atTop (𝓝 (L ^ m)) := by
  induction m with
  | zero =>
      have heq : (fun l => R (l + 0) / R l) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
        filter_upwards [hpos] with l hl
        simp [div_self (ne_of_gt hl)]
      rw [tendsto_congr' heq, pow_zero]
      exact tendsto_const_nhds
  | succ m ih =>
      have hpos_m : ∀ᶠ l in atTop, 0 < R (l + m) :=
        (tendsto_add_atTop_nat m).eventually hpos
      have hshift : Tendsto (fun l => R (l + m + 1) / R (l + m)) atTop (𝓝 L) := by
        simpa using hratio.comp (tendsto_add_atTop_nat m)
      have hmul : Tendsto
          (fun l => R (l + m + 1) / R (l + m) * (R (l + m) / R l)) atTop (𝓝 (L * L ^ m)) :=
        hshift.mul ih
      rw [pow_succ']
      refine hmul.congr' ?_
      filter_upwards [hpos_m] with l hlm
      show R (l + m + 1) / R (l + m) * (R (l + m) / R l) = R (l + m + 1) / R l
      exact div_mul_div_cancel₀ (ne_of_gt hlm)

/-- **General-limit bounded-gap increment.** If the consecutive ratio `R(l+1)/R(l)` tends
to `L` (with `R` eventually positive), then the normalized increment over any fixed gap `m`
tends to `L^m − 1`:

`(R(l+m) − R(l))/R(l) → L^m − 1`.

Immediate from `ratio_gap_tendsto_pow`, since `(R(l+m) − R(l))/R(l) = R(l+m)/R(l) − 1`. The
`L = 1` case recovers `increment_gap_div_tendsto_zero` (`1^m − 1 = 0`, the `o(R)` conclusion),
so this exhibits Erdős #1014's off-diagonal increment-smallness as the boundary `L = 1` of a
general geometric-growth statement. -/
theorem increment_gap_div_tendsto (R : ℕ → ℝ) (L : ℝ) (m : ℕ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 L)) :
    Tendsto (fun l => (R (l + m) - R l) / R l) atTop (𝓝 (L ^ m - 1)) := by
  have hgap := ratio_gap_tendsto_pow R L m hpos hratio
  have heq : (fun l => (R (l + m) - R l) / R l)
      =ᶠ[atTop] (fun l => R (l + m) / R l - 1) := by
    filter_upwards [hpos] with l hl
    rw [sub_div, div_self (ne_of_gt hl)]
  rw [tendsto_congr' heq]
  exact hgap.sub_const 1

/-- **General-limit logarithmic bounded-gap increment.** If the consecutive ratio
`R(l+1)/R(l)` tends to a *positive* limit `L` (with `R` eventually positive), then the
additive log-increment over any fixed gap `m` tends to `m · log L`:

`log R(l+m) − log R(l) → m · Real.log L`   (for `L > 0`).

The logarithmic companion of `increment_gap_div_tendsto`, and the general-`L` form of
`log_increment_gap_tendsto_zero` (the case `L = 1`, where `m · log 1 = 0`). Since
`log R(l+m) − log R(l) = log (R(l+m)/R(l))` and the gap-ratio `R(l+m)/R(l) → L^m`
(`ratio_gap_tendsto_pow`), continuity of `log` at `L^m ≠ 0` with `Real.log_pow` gives the
additive limit `log (L^m) = m · log L`. For the *diagonal* Ramsey number with ratio-limit
`L`, this reads the additive log-growth over a window of size `m` as exactly `m · log L`,
i.e. linear in the window — the additive shadow of the multiplicative `L^m`. -/
theorem log_increment_gap_tendsto (R : ℕ → ℝ) (L : ℝ) (m : ℕ) (hL : 0 < L)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 L)) :
    Tendsto (fun l => Real.log (R (l + m)) - Real.log (R l)) atTop
      (𝓝 (m * Real.log L)) := by
  have hgap := ratio_gap_tendsto_pow R L m hpos hratio
  have hpos_m : ∀ᶠ l in atTop, 0 < R (l + m) := (tendsto_add_atTop_nat m).eventually hpos
  have heq : (fun l => Real.log (R (l + m)) - Real.log (R l))
      =ᶠ[atTop] (fun l => Real.log (R (l + m) / R l)) := by
    filter_upwards [hpos, hpos_m] with l hl hlm
    rw [Real.log_div (ne_of_gt hlm) (ne_of_gt hl)]
  rw [tendsto_congr' heq]
  have hcont : Tendsto (fun l => Real.log (R (l + m) / R l)) atTop (𝓝 (Real.log (L ^ m))) :=
    (Real.continuousAt_log (pow_ne_zero m (ne_of_gt hL))).tendsto.comp hgap
  rw [Real.log_pow] at hcont
  exact hcont

/-! ## Reciprocal-sequence duality

The increment–ratio bridge is stable under reciprocation.  The consecutive ratio
of the reciprocal sequence `l ↦ (R l)⁻¹` is the reciprocal of that of `R`, and
reciprocation fixes the limit `1`, so the borderline `o(R)` behavior transfers
verbatim to the reciprocal (density-like) sequence `1/R`.  Applied to `R(k, ·)`,
Erdős #1014's ratio-convergence `R(k,l+1)/R(k,l) → 1` yields not only
`Δ_l(k) = o(R(k,l))` but also the dual statement that the reciprocal density
`1/R(k,l)` has vanishing normalized increment. -/

/-- The consecutive ratio of the reciprocal sequence `l ↦ (R l)⁻¹` is the
reciprocal of the consecutive ratio of `R`.  Holds unconditionally (both sides
are `0` when a denominator vanishes). -/
theorem inv_ratio_eq (R : ℕ → ℝ) (l : ℕ) :
    (R (l + 1))⁻¹ / (R l)⁻¹ = (R (l + 1) / R l)⁻¹ := by
  rcases eq_or_ne (R l) 0 with h | h
  · simp [h]
  · rcases eq_or_ne (R (l + 1)) 0 with h2 | h2
    · simp [h2]
    · field_simp

/-- **Reciprocal ratio convergence.** The consecutive ratio of `R` tends to `1`
**iff** the consecutive ratio of the reciprocal sequence `l ↦ (R l)⁻¹` does —
reciprocation is a self-inverse map continuous at, and fixing, the limit `1`. -/
theorem reciprocal_ratio_tendsto_one_iff (R : ℕ → ℝ) :
    Tendsto (fun l => (R (l + 1))⁻¹ / (R l)⁻¹) atTop (𝓝 1) ↔
      Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1) := by
  have heq : (fun l => (R (l + 1))⁻¹ / (R l)⁻¹)
      =ᶠ[atTop] (fun l => (R (l + 1) / R l)⁻¹) :=
    Eventually.of_forall (inv_ratio_eq R)
  rw [tendsto_congr' heq]
  constructor
  · intro h; simpa using h.inv₀
  · intro h; simpa using h.inv₀

/-- **Reciprocal-increment duality.** For an eventually-nonzero sequence `R`, the
normalized increment of the reciprocal sequence `l ↦ (R l)⁻¹` tends to `0` **iff**
the consecutive ratio of `R` tends to `1`.

The reciprocal companion of `increment_div_tendsto_zero_iff_ratio_tendsto_one`:
applied to `R(k, ·)`, Erdős #1014's `R(k,l+1)/R(k,l) → 1` transfers to the
reciprocal (density-like) sequence `1/R(k,l)`, whose increment is likewise
`o(1/R(k,l))`. -/
theorem reciprocal_increment_div_tendsto_zero_iff (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, R l ≠ 0) :
    Tendsto (fun l => ((R (l + 1))⁻¹ - (R l)⁻¹) / (R l)⁻¹) atTop (𝓝 0) ↔
      Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1) := by
  have hinv : ∀ᶠ l in atTop, (R l)⁻¹ ≠ 0 := by
    filter_upwards [hpos] with l hl using inv_ne_zero hl
  rw [increment_div_tendsto_zero_iff_ratio_tendsto_one (fun l => (R l)⁻¹) hinv]
  exact reciprocal_ratio_tendsto_one_iff R

/-! ## Subexponential growth (the root-test consequence)

The increment–ratio bridge above controls *local* (one-step) behavior of `R`. A
consecutive ratio tending to `1` also has a *global* consequence for the growth
*rate*: it forces the geometric root `R(l)^{1/l}` to tend to `1`, i.e. `R` grows
subexponentially, `R(l) = e^{o(l)}`.

The mechanism is the ratio-test ⇒ root-test passage, made quantitative through the
logarithm. Writing `c_l = log R(l+1) − log R(l)` for the additive log-increment
(shown above to vanish exactly when the ratio tends to `1`), the telescoping identity
`log R(n) − log R(0) = ∑_{i<n} c_i` (`log_increment_gap_eq_sum` with `l = 0`) turns the
normalized log `(log R(n))/n` into the **Cesàro average** of the `c_i`. Cesàro
averaging preserves limits (`Filter.Tendsto.cesaro`), so `c_l → 0` gives
`(log R(n))/n → 0`, and exponentiating gives `R(n)^{1/n} → 1`.

Applied to `R(k, ·)`, Erdős #1014's ratio-convergence `R(k,l+1)/R(k,l) → 1` yields
`R(k,l)^{1/l} → 1`: the off-diagonal Ramsey numbers are subexponential in `l` for
fixed `k`. This is consistent with the known polynomial rate `R(3,l) = Θ(l²/log l)`
(every polynomially-bounded positive sequence is subexponential) but is derived here
from the ratio hypothesis alone, with no rate input. -/

/-- **Normalized log tends to zero (Cesàro form).** If the consecutive ratio of an
eventually-positive `R` tends to `1`, then `(log R(l))/l → 0`.

Proof: the log-increment `log R(l+1) − log R(l)` tends to `0`
(`log_increment_tendsto_zero_of_ratio_tendsto_one`); its Cesàro average
`n⁻¹ ∑_{i<n} (log R(i+1) − log R(i))` therefore also tends to `0`
(`Filter.Tendsto.cesaro`); and that sum telescopes to `log R(n) − log R(0)`
(`Finset.sum_range_sub`), whose `log R(0)/n` tail is negligible. -/
theorem log_div_nat_tendsto_zero_of_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => Real.log (R l) / (l : ℝ)) atTop (𝓝 0) := by
  -- the log-increment sequence vanishes …
  have hc0 : Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 0) :=
    log_increment_tendsto_zero_of_ratio_tendsto_one R hpos hratio
  -- … so its Cesàro average vanishes …
  have hces := hc0.cesaro
  -- … and the Cesàro sum telescopes to `log R(n) − log R(0)`.
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, (Real.log (R (i + 1)) - Real.log (R i)))
        = Real.log (R n) - Real.log (R 0) :=
    fun n => Finset.sum_range_sub (fun i => Real.log (R i)) n
  simp only [hsum] at hces
  -- the `log R(0)/n` tail tends to `0`
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hconst : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (R 0)) atTop (𝓝 0) := by
    simpa using hinv.mul_const (Real.log (R 0))
  -- add it back to recover `n⁻¹ · log R(n) → 0`, then rewrite `n⁻¹ · x = x / n`.
  have hgoal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (R n)) atTop (𝓝 0) := by
    have hsum2 := hces.add hconst
    simp only [add_zero] at hsum2
    refine hsum2.congr fun n => ?_
    ring
  refine hgoal.congr fun n => ?_
  rw [div_eq_inv_mul]

/-- **Subexponential growth (root test).** If the consecutive ratio of an
eventually-positive `R` tends to `1`, then the geometric root `R(l)^{1/l}` tends to
`1`; equivalently `R(l) = e^{o(l)}`.

The global growth-rate companion of the local increment–ratio bridge: fed Erdős
#1014's `R(k,l+1)/R(k,l) → 1` it gives `R(k,l)^{1/l} → 1`, so for fixed `k` the
off-diagonal Ramsey numbers grow subexponentially in `l`. Proof: exponentiate
`log_div_nat_tendsto_zero_of_ratio_tendsto_one`, using `x^{1/l} = exp((1/l)·log x)`
for `x > 0` and continuity of `exp` at `0`. -/
theorem rpow_inv_nat_tendsto_one_of_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => (R l) ^ ((l : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun l : ℕ => (l : ℝ)⁻¹ * Real.log (R l)) atTop (𝓝 0) := by
    have h := log_div_nat_tendsto_zero_of_ratio_tendsto_one R hpos hratio
    refine h.congr fun n => ?_
    rw [div_eq_inv_mul]
  have hexp : Tendsto (fun l : ℕ => Real.exp ((l : ℝ)⁻¹ * Real.log (R l))) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp hlog
    simpa using this
  refine hexp.congr' ?_
  filter_upwards [hpos] with l hl
  rw [Real.rpow_def_of_pos hl, mul_comm (Real.log (R l)) ((l : ℝ)⁻¹)]

end Erdos1014OQ03
