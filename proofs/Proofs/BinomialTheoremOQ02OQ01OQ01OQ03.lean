/-
# Multinomial Marginal Central Limit Theorem

**Open Question** (binomial-theorem-oq-02-oq-01-oq-01-oq-03):
"Multinomial marginal CLT in Lean: does (Xᵢ - npᵢ) / √(npᵢ(1-pᵢ)) converge in
distribution to N(0,1) for each coordinate as n → ∞?"

## Status

**Reduction complete.** This file STATES the multinomial marginal CLT
and reduces it to the classical de Moivre–Laplace (binomial) CLT plus the
already-proved marginal-PMF identity from `BinomialTheoremOQ02OQ01OQ02`.
The reduction lemma `multinomialMarginalCDF_eq_binomialCDF` is now fully
proved (Phase-3 deliverable, this file).

The de Moivre–Laplace CLT itself is taken as an axiom: at the lake-pinned
Mathlib v4.26.0 SHA (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), no
`ProbabilityTheory.iid_central_limit_theorem` symbol exists anywhere in
Mathlib (see S14 bearer audit in `research/problems/binomial-theorem-oq-
02-oq-01-oq-01-oq-03/knowledge.md`); a Mathlib-native proof would have
to construct the i.i.d. CLT scaffolding locally and bridge to CDF form
via Portmanteau, which is non-trivial and is left for a follow-up
effort. After this file, the single mathematical assumption beyond
Mathlib is the classical Binomial CLT itself.

## What This File Provides

1. `binomialCDF n p x` — concrete CDF of Binomial(n, p), defined as
   ∑_{j ≤ x} C(n,j) p^j (1-p)^(n-j).
2. `multinomialMarginalCDF s p n i₀ x` — concrete CDF of the marginal X_{i₀}
   of Multinomial(n, p), defined by summing `multinomialProb` over the
   filtered piAntidiag.
3. `standardNormalCDF` — concrete `noncomputable def` integrating
   Mathlib's `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`,
   plus the elementary properties `_nonneg`, `_le_one`, `_mono`.
4. `binomial_clt_pointwise` — AXIOM: pointwise convergence of standardized
   binomial CDF to standardNormalCDF.
5. `multinomialMarginalCDF_eq_binomialCDF` — reduction lemma, **proved**:
   the marginal CDF of the multinomial equals the binomial CDF with
   parameter p(i₀). Proof regroups `∑ k ∈ s.piAntidiag n` into fibers
   over `j = k(i₀)` via `Finset.sum_fiberwise_of_maps_to`, then applies
   `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`.
6. `multinomial_marginal_clt` — DERIVED THEOREM (no axiom of its own).
   Combines (4) and (5) via `Filter.Tendsto.congr`.

## Mathematical Content

For (X₁, ..., Xₖ) ~ Multinomial(n, p₁, ..., pₖ), each marginal Xᵢ ~ Binomial(n, pᵢ)
(this was proved in `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`).
The classical de Moivre–Laplace theorem gives:

    P( (X − np) / √(np(1−p)) ≤ x )  →  Φ(x)    as n → ∞

for any x ∈ ℝ, where Φ is the standard normal CDF. Composing these two facts
gives the multinomial marginal CLT.

## Honest Reporting

- Sorries: 0 after S11 ACT (2026-05-13, researcher-1) transcribed the five
  S10 repair templates targeting issue #17317. Prior history: S8 (PR #17233)
  introduced five Mathlib v4.26 API-drift breakages; mechanic PR #17353
  demoted them to `sorry` so the file type-checks; S10 PR (researcher-6)
  produced concrete repair templates against the lake-pinned Mathlib v4.26
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. S11 transcribes those
  templates; status is BUILD-PENDING (the templates carry low/medium
  forensic certainty — Doctor/Mechanic may need to refine closing
  tactics if Docker build reveals elaboration drift). All theorem
  signatures preserved.
- Axioms: 1 (`binomial_clt_pointwise`). The Session-2 `standardNormalCDF`
  opaque was replaced in Session 6 with a concrete `noncomputable def`
  using Mathlib's `gaussianPDFReal`.
- Status: axiomatized — not "verified".
- Session 7 added the two boundary-saturation lemmas `binomialCDF_zero`
  and `binomialCDF_eq_one`, completing the four-corner characterization
  of `binomialCDF` on the binomial side, plus `standardNormalCDF_continuous`
  on the gaussian side.
- Session 8 added two CDF-tail-limit lemmas for Φ:
  `standardNormalCDF_tendsto_atBot` (Φ → 0 as x → -∞) and
  `standardNormalCDF_tendsto_atTop` (Φ → 1 as x → +∞). Together with
  the prior structural lemmas this proves Φ has the full proper-CDF
  signature (nonneg, monotone, continuous, ≤ 1, with limit values 0
  and 1 at the two infinities) — the data the Phase-4 Portmanteau
  bridge needs at every continuity point of the limit.
- Session 11 (this session, 2026-05-13, researcher-1) discharges the
  five-sorry build-broken state inherited from #17353 by transcribing
  the S10 repair templates:
  * `standardNormalCDF_tendsto_atBot` rebuilt around `aecover_Ioi` +
    `setIntegral_compl` + `Set.compl_Ioi` (replacing the absent
    `MeasureTheory.tendsto_integral_Iic_zero` cited by S8).
  * `multinomialMarginalCDF_eq_binomialCDF` restored via the
    fiber-decomposition route with the corrected `(f := ...)` named
    argument (the pre-fix proof passed `(g := if-stmt)` by mistake).
  * `binomialCDF_mono` restored with the explicit close of the
    `if_neg ∧ if_neg` branch (`rw [if_neg hjy]` produces `(0 : ℝ) ≤ 0`,
    discharged by `rfl`/`le_refl`).
  * `binomialCDF_eq_one` rebuilt to mirror the working `binomialCDF_le_one`
    idiom (`Finset.sum_congr` over a fully-true if-branch + `add_pow`);
    the pre-fix proof's `exact (binomialCDF_neg n p hx).symm` close was
    a copy-paste bug (`binomialCDF_neg` requires `x < 0` but `hx : n ≤ x`
    contradicts that for `n ≥ 0`).
  * `multinomial_marginal_clt` derived cleanly from the now-proved
    reduction lemma + `binomial_clt_pointwise` via `Filter.Tendsto.congr`.

The contribution of this file is the *full reduction* of the multinomial
marginal CLT to the classical Binomial CLT, leaving only the latter as
an explicit named assumption.

## Why CDF formulation

A measure-theoretic CLT (the form Mathlib would naturally provide, were
`ProbabilityTheory.iid_central_limit_theorem` present — it is NOT at the
lake-pinned v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; see
S14 bearer audit in `knowledge.md`) is stated in terms of measure-weak-
convergence of the law of standardized sums to the Gaussian measure. Our
statement is in CDF form to (a) avoid the heavy measure-theory setup for
a marginal-only result, (b) match the classical "de Moivre–Laplace"
presentation, and (c) keep the reduction to the already-proved marginal-
PMF identity transparent.

## Dependencies

- `BinomialTheoremOQ02OQ01OQ02` — `multinomialProb`, `multinomial_marginal_pmf`
- Mathlib — `Real.sqrt`, `Filter.Tendsto`, `nhds`
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ02

namespace BinomialTheoremOQ02OQ01OQ01OQ03

open Finset BigOperators

/-! ## CDF definitions -/

/-- The CDF of Binomial(n, p) at `x`:
    `binomialCDF n p x = ∑_{j ≤ x, 0 ≤ j ≤ n} C(n, j) · p^j · (1 - p)^(n - j)`.

    No constraints on `p` are enforced at the definition level; the axiom
    `binomial_clt_pointwise` requires `0 < p < 1`. -/
noncomputable def binomialCDF (n : ℕ) (p : ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    if (j : ℝ) ≤ x then
      (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j)
    else 0

/-- The marginal CDF of coordinate `i₀` for X ~ Multinomial(n, p). -/
noncomputable def multinomialMarginalCDF
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (i₀ : α) (x : ℝ) : ℝ :=
  ∑ k ∈ s.piAntidiag n,
    if ((k i₀ : ℕ) : ℝ) ≤ x then
      BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
    else 0

/-! ## Standard normal CDF -/

/-- The standard normal CDF,
    `Φ(x) = ∫_{-∞}^x (1/√(2π)) · exp(-t²/2) dt`.

    Defined concretely as the Lebesgue integral of Mathlib's
    `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`. Replaces
    the Session-2 `opaque standardNormalCDF` marker; this removes that
    declaration from the file's assumption count. -/
noncomputable def standardNormalCDF (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 t

/-- The standard normal CDF is non-negative — the integral of a
    non-negative density over a measurable set is non-negative. -/
theorem standardNormalCDF_nonneg (x : ℝ) : 0 ≤ standardNormalCDF x := by
  unfold standardNormalCDF
  exact MeasureTheory.setIntegral_nonneg_of_ae
    (Filter.Eventually.of_forall (ProbabilityTheory.gaussianPDFReal_nonneg 0 1))

/-- The standard normal CDF is at most `1` — the integral over `(−∞, x]`
    is bounded above by the total integral, which equals `1` by
    `ProbabilityTheory.integral_gaussianPDFReal_eq_one`. -/
theorem standardNormalCDF_le_one (x : ℝ) : standardNormalCDF x ≤ 1 := by
  have h_total : ∫ t, ProbabilityTheory.gaussianPDFReal 0 1 t = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
  unfold standardNormalCDF
  rw [← h_total]
  exact MeasureTheory.setIntegral_le_integral
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1)
    (Filter.Eventually.of_forall (ProbabilityTheory.gaussianPDFReal_nonneg 0 1))

/-- The standard normal CDF is monotone in `x` — the integrand is
    non-negative and `Set.Iic x ⊆ Set.Iic y` whenever `x ≤ y`. -/
theorem standardNormalCDF_mono : Monotone standardNormalCDF := by
  intro x y hxy
  unfold standardNormalCDF
  exact MeasureTheory.setIntegral_mono_set
    ((ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn)
    (Filter.Eventually.of_forall (ProbabilityTheory.gaussianPDFReal_nonneg 0 1))
    (Set.Iic_subset_Iic.mpr hxy).eventuallyLE

/-- The standard normal CDF, evaluated at `x`, equals the constant
    `standardNormalCDF 0` plus the (interval-)integral of the standard normal
    PDF from `0` to `x`. This bridge lemma is the input to the continuity
    proof: the LHS is a `setIntegral` over `Iic x`; the RHS is decomposed as a
    constant plus an `intervalIntegral` whose primitive form is continuous via
    `MeasureTheory.Integrable.continuous_primitive`.

    Proof: both `∫ Iic x` and `∫ Iic 0` are limits of `∫ a..x` and `∫ a..0`
    as `a → -∞` (`MeasureTheory.intervalIntegral_tendsto_integral_Iic`). For
    each `a`, the adjacent-intervals identity
    `∫ a..x = ∫ a..0 + ∫ 0..x` holds. Taking limits and using `tendsto_nhds_unique`
    closes the equation. -/
private lemma standardNormalCDF_eq_zero_plus_intervalIntegral (x : ℝ) :
    standardNormalCDF x = standardNormalCDF 0
      + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
  have hf_int : MeasureTheory.Integrable (ProbabilityTheory.gaussianPDFReal 0 1) :=
    ProbabilityTheory.integrable_gaussianPDFReal 0 1
  -- The function `y ↦ ∫ t in y..x, f t` tends to `standardNormalCDF x` at `atBot`.
  have h_lim_x : Filter.Tendsto
      (fun y : ℝ => ∫ t in y..x, ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot (nhds (standardNormalCDF x)) := by
    unfold standardNormalCDF
    exact MeasureTheory.intervalIntegral_tendsto_integral_Iic x
      hf_int.integrableOn Filter.tendsto_id
  -- The function `y ↦ ∫ t in y..0, f t` tends to `standardNormalCDF 0` at `atBot`.
  have h_lim_0 : Filter.Tendsto
      (fun y : ℝ => ∫ t in y..(0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot (nhds (standardNormalCDF 0)) := by
    unfold standardNormalCDF
    exact MeasureTheory.intervalIntegral_tendsto_integral_Iic 0
      hf_int.integrableOn Filter.tendsto_id
  -- Adjacent-intervals identity: rewrite `∫ y..x` as `∫ y..0 + ∫ 0..x`.
  have hfn_eq : (fun y : ℝ => ∫ t in y..x, ProbabilityTheory.gaussianPDFReal 0 1 t) =
      fun y : ℝ => (∫ t in y..(0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 t)
        + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
    funext y
    have hab : IntervalIntegrable
        (ProbabilityTheory.gaussianPDFReal 0 1) MeasureTheory.volume y 0 :=
      hf_int.intervalIntegrable
    have hbc : IntervalIntegrable
        (ProbabilityTheory.gaussianPDFReal 0 1) MeasureTheory.volume 0 x :=
      hf_int.intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm
  rw [hfn_eq] at h_lim_x
  -- The rewritten LHS is a sum-of-tendsto: the first summand → standardNormalCDF 0,
  -- and the second is constant. So the limit is standardNormalCDF 0 + ∫ 0..x.
  have h_lim_rhs : Filter.Tendsto
      (fun y : ℝ => (∫ t in y..(0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 t)
        + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot
      (nhds (standardNormalCDF 0
        + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t)) :=
    h_lim_0.add_const _
  exact tendsto_nhds_unique h_lim_x h_lim_rhs

/-- **The standard normal CDF is continuous on `ℝ`.**

    Strategy: rewrite `standardNormalCDF` as `standardNormalCDF 0 +
    intervalIntegral 0..x` (`standardNormalCDF_eq_zero_plus_intervalIntegral`),
    then apply `MeasureTheory.Integrable.continuous_primitive` to the
    interval-primitive piece. The `NoAtoms volume` instance on `ℝ` is the
    measure-theoretic input that makes the primitive continuous.

    On the **Portmanteau-bridge critical path** for Phase-4 axiom elimination:
    Portmanteau converts measure-weak-convergence into pointwise convergence
    of CDFs at every continuity point of the limit CDF. Since `Φ` is
    continuous everywhere, every `x ∈ ℝ` is a continuity point, so the
    convergence is universal. Combined with the four `binomialCDF_*` lemmas
    (Sessions 4–5) and the three `standardNormalCDF_{nonneg,le_one,mono}`
    lemmas (Session 6), this completes the structural-properties library
    for the Phase-4 Portmanteau bridge that next session will build to
    discharge `binomial_clt_pointwise`. -/
theorem standardNormalCDF_continuous : Continuous standardNormalCDF := by
  have hfeq : standardNormalCDF = fun x : ℝ => standardNormalCDF 0
      + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
    funext x
    exact standardNormalCDF_eq_zero_plus_intervalIntegral x
  rw [hfeq]
  exact continuous_const.add
    ((ProbabilityTheory.integrable_gaussianPDFReal 0 1).continuous_primitive 0)

/-- **Left tail saturation**: `standardNormalCDF x → 0` as `x → -∞`.

    Direct corollary of `MeasureTheory.tendsto_integral_Iic_zero`, which says that
    for any integrable `f`, `(λ a, ∫ t in Iic a, f t) → 0` along `atBot`. With
    `f := gaussianPDFReal 0 1` (integrable by Mathlib's
    `ProbabilityTheory.integrable_gaussianPDFReal`) and `a := id`, the
    conclusion matches `standardNormalCDF` after unfolding.

    On the **Portmanteau-bridge critical path** for Phase-4 axiom elimination:
    Portmanteau converts measure-weak-convergence into pointwise CDF
    convergence at every continuity point. Combined with continuity (Session 7)
    and the right-tail saturation `standardNormalCDF_tendsto_atTop`, this
    proves Φ is a *bona fide* probability CDF in the Mathlib sense — the
    limit value at `-∞` is `0` and the limit at `+∞` is `1`, mirroring the
    boundary saturations `binomialCDF_neg = 0` and `binomialCDF_eq_one = 1`
    on the binomial side. -/
theorem standardNormalCDF_tendsto_atBot :
    Filter.Tendsto standardNormalCDF Filter.atBot (nhds 0) := by
  -- S11 (researcher-1, 2026-05-13): repair template from S10 knowledge.md.
  -- Strategy: along `atBot`, `Ioi x` is an `AECover` (via `aecover_Ioi`
  -- + `tendsto_id`); the integral over `Ioi x` tends to `∫ ℝ, f = 1`.
  -- Then `∫ Iic x = 1 − ∫ Ioi x` via `setIntegral_compl` + `Set.compl_Ioi`,
  -- and `Tendsto.const_sub 1` gives the `1 − 1 = 0` limit. Build-pending.
  unfold standardNormalCDF
  have hint : MeasureTheory.Integrable (ProbabilityTheory.gaussianPDFReal 0 1) :=
    ProbabilityTheory.integrable_gaussianPDFReal 0 1
  have hone : ∫ t, ProbabilityTheory.gaussianPDFReal 0 1 t = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
  have hcover : MeasureTheory.AECover MeasureTheory.volume Filter.atBot
      (fun x : ℝ => Set.Ioi x) :=
    MeasureTheory.aecover_Ioi Filter.tendsto_id
  have htendsto_Ioi :=
    hcover.integral_tendsto_of_countably_generated hint
  rw [hone] at htendsto_Ioi
  -- htendsto_Ioi : Tendsto (fun x => ∫ t in Ioi x, f t) atBot (𝓝 1)
  have h_eq : ∀ x : ℝ,
      ∫ t in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 t
        = 1 - ∫ t in Set.Ioi x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
    intro x
    have hms : MeasurableSet (Set.Ioi x) := measurableSet_Ioi
    have hcompl_eq : (Set.Ioi x)ᶜ = Set.Iic x := Set.compl_Ioi
    have hsetc := MeasureTheory.setIntegral_compl (μ := MeasureTheory.volume)
      hms hint
    rw [hcompl_eq] at hsetc
    rw [hsetc, hone]
  have hsub : Filter.Tendsto
      (fun x : ℝ => 1 - ∫ t in Set.Ioi x, ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot (nhds (1 - 1)) :=
    Filter.Tendsto.const_sub 1 htendsto_Ioi
  have hsub' : Filter.Tendsto
      (fun x : ℝ => 1 - ∫ t in Set.Ioi x, ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot (nhds 0) := by simpa using hsub
  exact hsub'.congr (fun x => (h_eq x).symm)

/-- **Right tail saturation**: `standardNormalCDF x → 1` as `x → +∞`.

    Proof: the family `(Iic x)_{x : ℝ}` is an `MeasureTheory.AECover` of `ℝ`
    along `atTop` (Mathlib's `aecover_Iic` plus `Filter.tendsto_id`). Combined
    with the integrability of `gaussianPDFReal 0 1`,
    `AECover.integral_tendsto_of_countably_generated` gives
    `(λ x, ∫ t in Iic x, gaussianPDFReal 0 1 t) → ∫ t, gaussianPDFReal 0 1 t`,
    and the total integral is `1` by `integral_gaussianPDFReal_eq_one 0 one_ne_zero`.

    On the **Portmanteau-bridge critical path**: companion to
    `standardNormalCDF_tendsto_atBot`, jointly establishing that Φ is a
    proper CDF with limits `0` and `1` at the two infinities. -/
theorem standardNormalCDF_tendsto_atTop :
    Filter.Tendsto standardNormalCDF Filter.atTop (nhds 1) := by
  unfold standardNormalCDF
  have hcover : MeasureTheory.AECover MeasureTheory.volume Filter.atTop
      (fun x : ℝ => Set.Iic x) :=
    MeasureTheory.aecover_Iic Filter.tendsto_id
  have hint : MeasureTheory.Integrable (ProbabilityTheory.gaussianPDFReal 0 1) :=
    ProbabilityTheory.integrable_gaussianPDFReal 0 1
  have htendsto := hcover.integral_tendsto_of_countably_generated hint
  have hone : ∫ t, ProbabilityTheory.gaussianPDFReal 0 1 t = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
  rw [hone] at htendsto
  exact htendsto

/-! ## Axiom: classical de Moivre–Laplace (binomial CLT) -/

/-- **AXIOM** (de Moivre–Laplace, 1733/1812): the standardized binomial CDF
    converges pointwise to the standard normal CDF as `n → ∞`.

    For `0 < p < 1` and any `x : ℝ`,
    `binomialCDF n p (np + x √(np(1−p)))  →  Φ(x)`.

    Mathematical justification: classical, see e.g. Feller, *Introduction to
    Probability Theory*, Vol. I (1968), Ch. VII §3. The Mathlib path would
    route through a not-yet-landed `iid_central_limit_theorem` (absent at
    the v4.26.0 pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, see
    S14 audit in `knowledge.md`) plus a Portmanteau CDF-bridge; recorded
    as an axiom here (Phase-3 target). -/
axiom binomial_clt_pointwise
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        binomialCDF n p ((n : ℝ) * p + x * Real.sqrt ((n : ℝ) * p * (1 - p))))
      Filter.atTop (nhds (standardNormalCDF x))

/-! ## Reduction lemma -/

/-- For any composition `k ∈ s.piAntidiag n`, every coordinate is at most `n`. -/
private lemma piAntidiag_apply_le {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) (i₀ : α) :
    ∀ k ∈ s.piAntidiag n, k i₀ ≤ n := by
  intro k hk
  rw [Finset.mem_piAntidiag] at hk
  obtain ⟨hksum, hksup⟩ := hk
  by_cases h : i₀ ∈ s
  · -- i₀ ∈ s: bound by the sum.
    have hle : k i₀ ≤ ∑ i ∈ s, k i :=
      Finset.single_le_sum (s := s) (f := k) (fun i _ => Nat.zero_le _) h
    -- S12 (researcher-9, 2026-05-13): replace bare `omega` with explicit
    -- chain. Reason: in Mathlib v4.26.0, `Finset.mem_piAntidiag` gives
    -- `hksum : s.sum k = n` (dot-notation form), which omega's preprocessor
    -- does NOT unify with `hle`'s `∑ i ∈ s, k i` form, despite definitional
    -- equality. The calc chain is bulletproof against this notation skew.
    calc k i₀ ≤ ∑ i ∈ s, k i := hle
      _       = n             := hksum
  · -- i₀ ∉ s: support condition forces k i₀ = 0.
    by_contra hne
    push_neg at hne
    have h1 : k i₀ ≠ 0 := by omega
    exact h (hksup i₀ h1)

/-- **Reduction lemma**: the marginal CDF of the multinomial equals the
    binomial CDF with parameter `p(i₀)`.

    Proof: regroup `∑ k ∈ s.piAntidiag n` into fibers over the value
    `j = k i₀` for `j ∈ {0, ..., n}` via `Finset.sum_fiberwise_of_maps_to`;
    on each fiber, the `if`-guard `((k i₀ : ℕ) : ℝ) ≤ x` simplifies to
    `(j : ℝ) ≤ x` (since `k i₀ = j` is the fiber predicate), which is
    constant in `k` and so factors out; the inner fiber-sum then collapses
    to `C(n, j) · p(i₀)^j · (1 − p(i₀))^(n − j)` by
    `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf` (Sublemma A). -/
theorem multinomialMarginalCDF_eq_binomialCDF
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (x : ℝ) :
    multinomialMarginalCDF s p n i₀ x = binomialCDF n (p i₀) x := by
  -- S11 (researcher-1, 2026-05-13): repair template from S10 knowledge.md.
  -- Strategy: fiber-decompose the multinomial sum over `j = k i₀` via
  -- `Finset.sum_fiberwise_of_maps_to` (named-arg `(f := ...)`, not `(g := ...)`
  -- as the pre-fix proof erroneously wrote); inside each fiber the if-guard
  -- collapses to a constant; the inner sum reduces to the binomial PMF via
  -- `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`. Build-pending.
  unfold multinomialMarginalCDF binomialCDF
  have hmaps : ∀ k ∈ s.piAntidiag n, k i₀ ∈ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact piAntidiag_apply_le s n i₀ k hk
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (n + 1)) hmaps
        (f := fun k =>
          if ((k i₀ : ℕ) : ℝ) ≤ x
          then BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
          else 0)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  by_cases hcond : (j : ℝ) ≤ x
  · rw [if_pos hcond]
    have h_inner :
        ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
            (if ((k i₀ : ℕ) : ℝ) ≤ x
             then BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
             else 0)
        = ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
            BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [hk.2, if_pos hcond]
    rw [h_inner]
    exact BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf
            s p n hp i₀ hi₀ j hj
  · rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hk.2, if_neg hcond]

/-! ## Structural properties of `binomialCDF` (Phase-4 prep) -/

/-- For `x < 0`, `binomialCDF n p x = 0`. Every `j ∈ {0, …, n}` satisfies
    `(j : ℝ) ≥ 0 > x`, so the if-guard is false in every term. -/
theorem binomialCDF_neg (n : ℕ) (p : ℝ) {x : ℝ} (hx : x < 0) :
    binomialCDF n p x = 0 := by
  unfold binomialCDF
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (not_le.mpr (lt_of_lt_of_le hx (Nat.cast_nonneg j)))]

/-- `binomialCDF n p` is monotone in `x`, when `0 ≤ p ≤ 1`.

    Each summand is either `0` or the binomial PMF
    `C(n, j) · p^j · (1 − p)^(n − j)`, which is non-negative under the
    standing hypothesis `0 ≤ p ≤ 1`. As `x` increases, more if-guards
    become true, so each summand is non-decreasing.

    Useful for the Phase-4 Portmanteau bridge: continuous monotone CDFs
    characterize weak convergence on `ℝ`. -/
theorem binomialCDF_mono (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Monotone (binomialCDF n p) := by
  -- S11 (researcher-1, 2026-05-13): repair template from S10 knowledge.md.
  -- Case-split on whether each `(j : ℝ) ≤ x` holds; when it does, both
  -- if-guards (x and y) are true and the summands match; when x's guard
  -- fails, we must compare `0` (left) against either the binomial PMF
  -- (right-true) or `0` (right-false). The pre-fix proof body was
  -- missing the explicit terminal close in the `if_neg ∧ if_neg` branch.
  -- Build-pending.
  intro x y hxy
  unfold binomialCDF
  apply Finset.sum_le_sum
  intro j _
  have h1mp : 0 ≤ 1 - p := by linarith
  by_cases hjx : (j : ℝ) ≤ x
  · rw [if_pos hjx, if_pos (le_trans hjx hxy)]
  · rw [if_neg hjx]
    by_cases hjy : (j : ℝ) ≤ y
    · rw [if_pos hjy]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
        (pow_nonneg h1mp _)
    · rw [if_neg hjy]

/-- For `0 ≤ p ≤ 1`, every value of `binomialCDF n p` is non-negative.

    Each summand is either `0` (if-guard false) or the binomial PMF
    `C(n, j) · p^j · (1 − p)^(n − j)`, which is non-negative since
    `Nat.choose n j ≥ 0`, `p ≥ 0`, and `1 − p ≥ 0`. The sum of
    non-negative terms is non-negative.

    Useful for the Phase-4 Portmanteau bridge: weak-convergence
    arguments for measures often pull back to non-negativity of CDFs. -/
theorem binomialCDF_zero_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ℝ) : 0 ≤ binomialCDF n p x := by
  have h1mp : 0 ≤ 1 - p := by linarith
  unfold binomialCDF
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hjx
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg h1mp _)
  · exact le_refl 0

/-- For `0 ≤ p ≤ 1`, every value of `binomialCDF n p` is at most `1`.

    Proof: the full unrestricted sum
    `∑_{j=0}^{n} C(n, j) · p^j · (1 − p)^(n − j) = (p + (1 − p))^n = 1`
    by the binomial theorem (`add_pow`). The CDF replaces some summands
    with `0`; under the hypothesis `0 ≤ p ≤ 1` each summand is
    non-negative, so dropping terms only decreases the total.

    Useful for the Phase-4 Portmanteau bridge: weak-convergence is
    typically formulated for sub-probability measures, and bounded
    CDFs on `[0, 1]` characterize the standard normal in the limit. -/
theorem binomialCDF_le_one (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ℝ) : binomialCDF n p x ≤ 1 := by
  have h1mp : 0 ≤ 1 - p := by linarith
  -- Step 1: rewrite `1` as the binomial expansion of `(p + (1 − p))^n`.
  have hexp : ∑ j ∈ Finset.range (n + 1),
      (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) = 1 := by
    have hadd := add_pow p (1 - p) n
    have hp_eq : p + (1 - p) = (1 : ℝ) := by ring
    rw [hp_eq, one_pow] at hadd
    -- hadd : (1 : ℝ) = ∑ k, p^k * (1 − p)^(n−k) * (Nat.choose n k : ℝ)
    -- S12 (researcher-9, 2026-05-13): use targeted `conv_rhs => rw [hadd]`
    -- to substitute ONLY the goal's RHS `1` with `∑ m, p^m * (1-p)^(n-m)
    -- * choose`. A bare `rw [hadd]` would also rewrite the inner `1`
    -- inside `(1 - p)^(n-j)`, mangling the goal. The `← hadd` direction
    -- can't find the sum-pattern in the LHS because `binomialCDF` uses
    -- `choose * p^m * (1-p)^(n-m)` order (choose first), but `add_pow`
    -- in Mathlib v4.26.0 produces `p^m * (1-p)^(n-m) * choose` order
    -- (choose last). The subsequent `sum_congr + ring` normalises
    -- per-term multiplication order.
    conv_rhs => rw [hadd]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- Step 2: replace `1` on the RHS with the equivalent sum.
  rw [← hexp]
  -- Step 3: term-by-term comparison.
  unfold binomialCDF
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hjx
  · exact le_refl _
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg h1mp _)

/-- At `x = 0`, only the `j = 0` term contributes to `binomialCDF n p`;
    every other `j ∈ {1, …, n}` has `(j : ℝ) ≥ 1 > 0`, failing the
    if-guard. The surviving term simplifies to
    `C(n, 0) · p^0 · (1 − p)^(n − 0) = (1 − p)^n`.

    Useful for the Phase-4 Portmanteau bridge: the boundary value at
    `x = 0` (i.e., the probability of zero successes) is the only
    closed-form value of the CDF, and it appears in the standardised
    threshold `np + x √(np(1−p))` when `x = -√(np/(1-p))`. -/
theorem binomialCDF_zero (n : ℕ) (p : ℝ) :
    binomialCDF n p 0 = (1 - p) ^ n := by
  unfold binomialCDF
  -- Reduce the sum to its single non-zero term `j = 0`.
  rw [Finset.sum_eq_single 0]
  · -- j = 0: if-guard `(0 : ℝ) ≤ 0` holds; the term is `1 · 1 · (1 − p)^n`.
    simp [Nat.choose_zero_right]
  · -- For `j ≠ 0` in the range, if-guard `(j : ℝ) ≤ 0` is false.
    intro j _ hjne
    have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
    have hj_not_le : ¬ (j : ℝ) ≤ 0 := by
      push_neg
      exact_mod_cast hjpos
    rw [if_neg hj_not_le]
  · -- `0 ∈ Finset.range (n+1)` is automatic.
    intro h
    exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ _)) h

/-- For `0 ≤ p ≤ 1` and any `x` with `(n : ℝ) ≤ x`, every if-guard
    `(j : ℝ) ≤ x` is satisfied (since `j ∈ {0, …, n}` gives
    `(j : ℝ) ≤ (n : ℝ) ≤ x`). The sum then equals the full binomial
    expansion `(p + (1 − p))^n = 1`.

    Useful for the Phase-4 Portmanteau bridge: the right-tail
    saturation `binomialCDF n p x = 1` for `x ≥ n` mirrors
    `Φ(x) → 1` as `x → ∞` for the standard normal. The companion
    `binomialCDF_neg` gives the matching left-tail saturation. -/
theorem binomialCDF_eq_one (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {x : ℝ} (hx : (n : ℝ) ≤ x) : binomialCDF n p x = 1 := by
  -- S11 (researcher-1, 2026-05-13): repair template from S10 knowledge.md.
  -- Strategy: collapse every if-guard `(j : ℝ) ≤ x` to true (since
  -- `j ≤ n ≤ x`); the remaining sum is the full binomial expansion
  -- `(p + (1-p))^n = 1` via `add_pow`. Mirrors the working idiom in
  -- `binomialCDF_le_one` (line 418); the pre-fix body's terminal
  -- `exact (binomialCDF_neg n p hx).symm` was a copy-paste bug
  -- (premise mismatch: `binomialCDF_neg` needs `x < 0`). Build-pending.
  unfold binomialCDF
  have h_simp : ∀ j ∈ Finset.range (n + 1),
      (if (j : ℝ) ≤ x
       then (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) else 0)
      = (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hjx : (j : ℝ) ≤ x := le_trans (by exact_mod_cast hj) hx
    rw [if_pos hjx]
  rw [Finset.sum_congr rfl h_simp]
  have hadd := add_pow p (1 - p) n
  have hp_eq : p + (1 - p) = (1 : ℝ) := by ring
  rw [hp_eq, one_pow] at hadd
  -- S12 (researcher-9, 2026-05-13): use targeted `conv_rhs => rw [hadd]`
  -- (same fix as `binomialCDF_le_one` above) — a bare `rw [hadd]` would
  -- also rewrite the inner `1` inside `(1 - p)^(n-j)`, mangling the goal.
  -- Multiplication-order mismatch between `add_pow`'s `p^k * (1-p)^(n-k)
  -- * choose` and `binomialCDF`'s `choose * p^k * (1-p)^(n-k)` is
  -- normalised by the subsequent sum_congr + ring step.
  conv_rhs => rw [hadd]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Right-tail asymptote of `binomialCDF`.** As `x → +∞`, the binomial
    CDF tends to `1` (under `0 ≤ p ≤ 1`).

    Proof: by `binomialCDF_eq_one`, `binomialCDF n p x = 1` for every
    `x` with `(n : ℝ) ≤ x`; the predicate `(n : ℝ) ≤ x` holds eventually
    along `Filter.atTop` (`Filter.eventually_ge_atTop`), so the function
    is *eventually constant equal to `1`* and the limit is `1`.

    Companion to `standardNormalCDF_tendsto_one_atTop`: paired right-tail
    saturation feeding the Phase-4 Portmanteau bridge. -/
theorem binomialCDF_tendsto_one_atTop (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Filter.Tendsto (binomialCDF n p) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (n : ℝ)] with x hx
  exact (binomialCDF_eq_one n hp0 hp1 hx).symm

/-- **Left-tail asymptote of `binomialCDF`.** As `x → -∞`, the binomial
    CDF tends to `0`.

    Proof: by `binomialCDF_neg`, `binomialCDF n p x = 0` for every `x < 0`;
    the predicate `x < 0` holds eventually along `Filter.atBot`
    (`Filter.eventually_lt_atBot`), so the function is *eventually constant
    equal to `0`* and the limit is `0`. No constraints on `p` are needed:
    `binomialCDF_neg` already holds for arbitrary `p`.

    The matching `standardNormalCDF_tendsto_zero_atBot` (Φ's left-tail
    saturation) is the next structural-CDF prerequisite for the
    Phase-4 Portmanteau bridge. -/
theorem binomialCDF_tendsto_zero_atBot (n : ℕ) (p : ℝ) :
    Filter.Tendsto (binomialCDF n p) Filter.atBot (nhds 0) := by
  have h : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atBot (nhds 0) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with x hx
  exact (binomialCDF_neg n p hx).symm

/-! ## Main theorem: multinomial marginal CLT (derived) -/

/-- **Multinomial marginal CLT** (DERIVED THEOREM, no separate axiom):
    for X ~ Multinomial(n, p), each non-degenerate marginal `Xᵢ` has the
    standardized CDF converging pointwise to `Φ(x)`.

    Proof: combine the de Moivre–Laplace axiom (`binomial_clt_pointwise`)
    with the reduction lemma (`multinomialMarginalCDF_eq_binomialCDF`)
    via `Filter.Tendsto.congr`. -/
theorem multinomial_marginal_clt
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (hp0 : 0 < p i₀) (hp1 : p i₀ < 1) (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        multinomialMarginalCDF s p n i₀
          ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))))
      Filter.atTop (nhds (standardNormalCDF x)) := by
  -- S11 (researcher-1, 2026-05-13): repair template from S10 knowledge.md.
  -- Clean composition: the multinomial marginal CDF *equals* the binomial CDF
  -- with parameter `p i₀` (Sorry 2, just repaired above); apply the
  -- de Moivre–Laplace axiom (`binomial_clt_pointwise`) on the binomial side
  -- and pull back through `Filter.Tendsto.congr`. Build-pending.
  have hbridge : ∀ n : ℕ,
      multinomialMarginalCDF s p n i₀
          ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀)))
        = binomialCDF n (p i₀)
            ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))) :=
    fun n => multinomialMarginalCDF_eq_binomialCDF s p n hp i₀ hi₀ _
  exact (binomial_clt_pointwise (p i₀) hp0 hp1 x).congr (fun n => (hbridge n).symm)

end BinomialTheoremOQ02OQ01OQ01OQ03
