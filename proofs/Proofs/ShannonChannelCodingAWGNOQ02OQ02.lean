/-
  Multi-symbol AWGN output power:  E[(∑ᵢ Wᵢ)²] = ∑ᵢ E[Wᵢ²]

  Open question (shannon-channel-coding-awgn-oq-02-oq-02):
  "Variance of a Sum of Pairwise-Independent Contributions (Multi-Symbol AWGN
   Output Power)."

  The parent file `ShannonChannelCodingAWGNOQ02.lean` discharges the *two-term*
  output-power relation `E[(X + Z)²] = E[X²] + E[Z²]` for a single-symbol additive
  channel `Y = X + Z`, using `ProbabilityTheory.IndepFun.variance_add`.

  A block of `n` transmitted symbols produces an aggregate output that is a *finite
  sum* of contributions `∑_{i ∈ s} Wᵢ` (per-symbol signal + noise terms). When the
  contributions are **pairwise independent** and **zero-mean**, the aggregate output
  power is the sum of the individual powers:

        E[(∑_{i ∈ s} Wᵢ)²] = ∑_{i ∈ s} E[Wᵢ²].

  The mathematical content is the *variance-of-a-sum* fact for pairwise-independent
  families — `ProbabilityTheory.IndepFun.variance_sum`, where the vanishing pairwise
  covariances collapse the double sum to the diagonal — specialised to zero mean via
  `E[W²] = Var[W]` (`ProbabilityTheory.variance_eq_sub`).  Note that *pairwise*
  independence (not full/mutual independence) already suffices, exactly as for the
  classical Bienaymé identity.

  This generalises the parent's two-term result (`s = {X, Z}`) to arbitrary finite
  blocks.  Everything is assembled from Mathlib's probability layer; the file is
  axiom-free and sorry-free.
-/

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace ShannonAWGNMultiSymbolPower

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a zero-mean square-integrable random variable the **second moment equals the
variance**: `E[W²] = Var[W]`.  This is the bridge that turns the "power" of a
zero-mean signal into its variance.  (Same statement as in the parent file, recorded
here so the multi-symbol results are self-contained.) -/
theorem second_moment_eq_variance [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hW : MemLp W 2 μ) (hW0 : μ[W] = 0) :
    μ[W ^ 2] = Var[W; μ] := by
  rw [variance_eq_sub hW, hW0]
  ring

/-- **Multi-symbol output variance (Bienaymé identity).**  The variance of a finite
sum of *pairwise-independent* square-integrable contributions is the sum of the
variances:

        Var[∑_{i ∈ s} Wᵢ] = ∑_{i ∈ s} Var[Wᵢ].

This is `IndepFun.variance_sum`, recorded in the channel notation.  Pairwise
independence suffices — the off-diagonal covariances vanish. -/
theorem awgn_multisymbol_variance {ι : Type*} {W : ι → Ω → ℝ} {s : Finset ι}
    (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (hindep : Set.Pairwise ↑s fun i j => W i ⟂ᵢ[μ] W j) :
    Var[∑ i ∈ s, W i; μ] = ∑ i ∈ s, Var[W i; μ] :=
  IndepFun.variance_sum hW hindep

/-- The aggregate of a family of zero-mean contributions is again zero-mean:
`E[∑_{i ∈ s} Wᵢ] = 0`. -/
theorem sum_mean_zero [IsFiniteMeasure μ] {ι : Type*} {W : ι → Ω → ℝ} {s : Finset ι}
    (hW : ∀ i ∈ s, MemLp (W i) 2 μ) (hmean : ∀ i ∈ s, μ[W i] = 0) :
    μ[∑ i ∈ s, W i] = 0 := by
  have hint : ∀ i ∈ s, Integrable (W i) μ := fun i hi => (hW i hi).integrable one_le_two
  simp only [Finset.sum_apply]
  rw [integral_finset_sum s hint]
  exact Finset.sum_eq_zero hmean

/-- **Multi-symbol AWGN output power.**  If the aggregate channel output is the finite
sum `∑_{i ∈ s} Wᵢ` of *pairwise-independent*, zero-mean, square-integrable
contributions, then the output second moment (power) is the sum of the individual
second moments:

        E[(∑_{i ∈ s} Wᵢ)²] = ∑_{i ∈ s} E[Wᵢ²].

This is the variance-of-a-sum fact reduced to second moments via the zero-mean
hypotheses, generalising the parent's two-term identity `E[(X + Z)²] = E[X²] + E[Z²]`
to an arbitrary finite block of symbols. -/
theorem awgn_multisymbol_power [IsProbabilityMeasure μ] {ι : Type*} {W : ι → Ω → ℝ}
    {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (hindep : Set.Pairwise ↑s fun i j => W i ⟂ᵢ[μ] W j)
    (hmean : ∀ i ∈ s, μ[W i] = 0) :
    μ[(∑ i ∈ s, W i) ^ 2] = ∑ i ∈ s, μ[(W i) ^ 2] := by
  have hSum : MemLp (∑ i ∈ s, W i) 2 μ := memLp_finset_sum' s hW
  have hSum0 : μ[∑ i ∈ s, W i] = 0 := sum_mean_zero hW hmean
  rw [second_moment_eq_variance hSum hSum0, awgn_multisymbol_variance hW hindep]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact (second_moment_eq_variance (hW i hi) (hmean i hi)).symm

/-- **Multi-symbol AWGN output power, named powers.**  Writing `Pᵢ = E[Wᵢ²]` for the
power of the `i`-th contribution, the aggregate output power is the sum of the
per-contribution powers:

        E[(∑_{i ∈ s} Wᵢ)²] = ∑_{i ∈ s} Pᵢ.

For a signal-plus-noise block (`Wᵢ` ranging over both the per-symbol signal and noise
terms) this is the total-power budget `P_total = ∑ signal powers + ∑ noise powers`,
the `n`-symbol analogue of the parent's `E[Y²] = P + N`. -/
theorem awgn_multisymbol_output_power [IsProbabilityMeasure μ] {ι : Type*}
    {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (hindep : Set.Pairwise ↑s fun i j => W i ⟂ᵢ[μ] W j)
    (hmean : ∀ i ∈ s, μ[W i] = 0) {P : ι → ℝ}
    (hP : ∀ i ∈ s, μ[(W i) ^ 2] = P i) :
    μ[(∑ i ∈ s, W i) ^ 2] = ∑ i ∈ s, P i := by
  rw [awgn_multisymbol_power hW hindep hmean]
  exact Finset.sum_congr rfl hP

/-!
### Sharp form: pairwise *uncorrelatedness* already suffices

The results above assume **pairwise independence** of the contributions, following
`ProbabilityTheory.IndepFun.variance_sum`.  But the Bienaymé identity only ever uses
that the *pairwise covariances vanish* — the off-diagonal terms of the double sum
`Var[∑ Wᵢ] = ∑ᵢ ∑ⱼ cov[Wᵢ, Wⱼ]` (`ProbabilityTheory.variance_sum'`) drop out.  Pairwise
independence is a strictly stronger hypothesis than pairwise uncorrelatedness (there
exist uncorrelated but dependent random variables), so the identity holds under the
weaker, and in fact *exactly sufficient*, second-order hypothesis `cov[Wᵢ, Wⱼ] = 0` for
`i ≠ j`.  For the AWGN power budget this is the sharp statement: **uncorrelated** signal
and noise contributions — not necessarily independent — still add in power.
-/

/-- **Sharp Bienaymé identity.**  The variance of a finite sum of *pairwise
uncorrelated* square-integrable random variables is the sum of the variances.  Only the
vanishing of the pairwise covariances is required; this is strictly weaker than the
pairwise-independence hypothesis of `ProbabilityTheory.IndepFun.variance_sum`, and it is
the exact second-order condition that makes the off-diagonal covariances of
`variance_sum'` disappear. -/
theorem variance_sum_of_pairwise_uncorrelated [IsFiniteMeasure μ] {ι : Type*}
    {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (huncor : Set.Pairwise ↑s fun i j => cov[W i, W j; μ] = 0) :
    Var[∑ i ∈ s, W i; μ] = ∑ i ∈ s, Var[W i; μ] := by
  rw [variance_sum' hW]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => huncor hi hj hji.symm]
  exact covariance_self (hW i hi).aemeasurable

/-- Pairwise independence is a special case of pairwise uncorrelatedness, so the
independence-based `awgn_multisymbol_variance` factors through the sharp identity:
`IndepFun.covariance_eq_zero` turns each pairwise-independence witness into a vanishing
covariance. -/
theorem variance_sum_of_pairwise_indep [IsFiniteMeasure μ] {ι : Type*} {W : ι → Ω → ℝ}
    {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (hindep : Set.Pairwise ↑s fun i j => W i ⟂ᵢ[μ] W j) :
    Var[∑ i ∈ s, W i; μ] = ∑ i ∈ s, Var[W i; μ] :=
  variance_sum_of_pairwise_uncorrelated hW fun i hi j hj hij =>
    (hindep hi hj hij).covariance_eq_zero (hW i hi) (hW j hj)

/-- **Multi-symbol AWGN output power under mere uncorrelatedness (sharp).**  If the
aggregate channel output is the finite sum `∑_{i ∈ s} Wᵢ` of *pairwise-uncorrelated*,
zero-mean, square-integrable contributions, then the output second moment (power) is the
sum of the individual second moments:

        E[(∑_{i ∈ s} Wᵢ)²] = ∑_{i ∈ s} E[Wᵢ²].

This strengthens `awgn_multisymbol_power` by replacing pairwise independence with the
weaker (and exactly sufficient) hypothesis of vanishing pairwise covariances. -/
theorem awgn_multisymbol_power_of_uncorrelated [IsProbabilityMeasure μ] {ι : Type*}
    {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (huncor : Set.Pairwise ↑s fun i j => cov[W i, W j; μ] = 0)
    (hmean : ∀ i ∈ s, μ[W i] = 0) :
    μ[(∑ i ∈ s, W i) ^ 2] = ∑ i ∈ s, μ[(W i) ^ 2] := by
  have hSum : MemLp (∑ i ∈ s, W i) 2 μ := memLp_finset_sum' s hW
  have hSum0 : μ[∑ i ∈ s, W i] = 0 := sum_mean_zero hW hmean
  rw [second_moment_eq_variance hSum hSum0,
    variance_sum_of_pairwise_uncorrelated hW huncor]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact (second_moment_eq_variance (hW i hi) (hmean i hi)).symm

/-!
### Sharp necessity: what is the *exact* condition for power to add?

The results above show that vanishing pairwise covariances are **sufficient** for the
variance (equivalently, zero-mean power) to add.  Are they also **necessary**?  The
Bienaymé expansion `Var[∑ Wᵢ] = ∑ᵢ ∑ⱼ cov[Wᵢ, Wⱼ]` (`variance_sum'`) answers this
exactly: peeling off the diagonal `cov[Wᵢ, Wᵢ] = Var[Wᵢ]` leaves

    Var[∑_{i ∈ s} Wᵢ] = ∑_{i ∈ s} Var[Wᵢ]  +  ∑_{i ∈ s} ∑_{j ∈ s, j ≠ i} cov[Wᵢ, Wⱼ],

so additivity of variance holds **iff the total off-diagonal covariance vanishes** — a
condition strictly weaker than pairwise uncorrelatedness (the individual covariances may
cancel in aggregate without each being zero).  Thus, for a block of `n ≥ 3` contributions,
pairwise uncorrelatedness is sufficient but *not* necessary for the powers to add; only
the aggregate off-diagonal cancellation is.  For the two-symbol case the off-diagonal sum
is `2·cov[W₀, W₁]`, so there additivity holds **iff** the single covariance is zero —
uncorrelatedness is then exactly necessary and sufficient.
-/

/-- **Exact condition for variance additivity (sharp necessity).**  For any finite family
of square-integrable random variables, the variance of the sum equals the sum of the
variances *if and only if* the total off-diagonal covariance vanishes:

    Var[∑_{i ∈ s} Wᵢ] = ∑_{i ∈ s} Var[Wᵢ]  ↔  ∑_{i ∈ s} ∑_{j ∈ s.erase i} cov[Wᵢ, Wⱼ] = 0.

This is the sharp converse to `variance_sum_of_pairwise_uncorrelated`: pairwise
uncorrelatedness (`cov[Wᵢ, Wⱼ] = 0` for all `i ≠ j`) forces the double sum to be zero and
so is *sufficient*, but the identity holds under the strictly weaker hypothesis that the
off-diagonal covariances merely *cancel in aggregate*. -/
theorem variance_sum_eq_iff_offDiag_covariance_zero [IsFiniteMeasure μ] {ι : Type*}
    [DecidableEq ι] {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ) :
    Var[∑ i ∈ s, W i; μ] = ∑ i ∈ s, Var[W i; μ] ↔
      ∑ i ∈ s, ∑ j ∈ s.erase i, cov[W i, W j; μ] = 0 := by
  have hsplit : ∀ i ∈ s, ∑ j ∈ s, cov[W i, W j; μ]
      = Var[W i; μ] + ∑ j ∈ s.erase i, cov[W i, W j; μ] := by
    intro i hi
    rw [← Finset.add_sum_erase s (fun j => cov[W i, W j; μ]) hi,
      covariance_self (hW i hi).aemeasurable]
  have key : ∑ i ∈ s, ∑ j ∈ s, cov[W i, W j; μ]
      = (∑ i ∈ s, Var[W i; μ]) + ∑ i ∈ s, ∑ j ∈ s.erase i, cov[W i, W j; μ] := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplit
  rw [variance_sum' hW, key]
  constructor <;> intro h <;> linarith

/-- **Two-symbol sharp boundary.**  For a *pair* of square-integrable contributions the
output powers add if and only if the two are uncorrelated:

    Var[W₀ + W₁] = Var[W₀] + Var[W₁]  ↔  cov[W₀, W₁] = 0.

Here uncorrelatedness is genuinely *necessary* (not merely sufficient), because the single
off-diagonal covariance cannot cancel against anything.  This is the exact second-order
condition behind the two-term AWGN identity `E[(X + Z)²] = E[X²] + E[Z²]` of the parent
file. -/
theorem variance_add_eq_iff_covariance_zero [IsFiniteMeasure μ] {W₀ W₁ : Ω → ℝ}
    (h₀ : MemLp W₀ 2 μ) (h₁ : MemLp W₁ 2 μ) :
    Var[W₀ + W₁; μ] = Var[W₀; μ] + Var[W₁; μ] ↔ cov[W₀, W₁; μ] = 0 := by
  rw [variance_add h₀ h₁]
  constructor <;> intro h <;> linarith

/-!
### Sharp necessity in *power* (second-moment) language

Everything above the two `variance_..._iff_...` results is stated for the *variance*
`Var[∑ Wᵢ]`, but the file is named for the AWGN output **power** `E[(∑ Wᵢ)²]`.  For
*zero-mean* contributions the two coincide (`second_moment_eq_variance`), so the sharp
necessity results transport verbatim into second-moment language.  These are the capstone
statements: the exact condition for the AWGN output **powers** to add.
-/

/-- **Exact condition for AWGN output power to add (sharp necessity, power form).**  For a
finite family of *zero-mean* square-integrable contributions, the aggregate output power
equals the sum of the individual powers *if and only if* the total off-diagonal covariance
vanishes:

    E[(∑_{i ∈ s} Wᵢ)²] = ∑_{i ∈ s} E[Wᵢ²]  ↔  ∑_{i ∈ s} ∑_{j ∈ s.erase i} cov[Wᵢ, Wⱼ] = 0.

This is `variance_sum_eq_iff_offDiag_covariance_zero` transported into second-moment
language via the zero-mean bridge, giving the sharp converse of
`awgn_multisymbol_power_of_uncorrelated`: pairwise uncorrelatedness is *sufficient* for the
powers to add, but the exact condition is the strictly weaker aggregate off-diagonal
cancellation. -/
theorem awgn_multisymbol_power_eq_iff_offDiag_covariance_zero [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {W : ι → Ω → ℝ} {s : Finset ι}
    (hW : ∀ i ∈ s, MemLp (W i) 2 μ) (hmean : ∀ i ∈ s, μ[W i] = 0) :
    μ[(∑ i ∈ s, W i) ^ 2] = ∑ i ∈ s, μ[(W i) ^ 2] ↔
      ∑ i ∈ s, ∑ j ∈ s.erase i, cov[W i, W j; μ] = 0 := by
  have hSum : MemLp (∑ i ∈ s, W i) 2 μ := memLp_finset_sum' s hW
  have hSum0 : μ[∑ i ∈ s, W i] = 0 := sum_mean_zero hW hmean
  rw [second_moment_eq_variance hSum hSum0,
    show (∑ i ∈ s, μ[(W i) ^ 2]) = ∑ i ∈ s, Var[W i; μ] from
      Finset.sum_congr rfl fun i hi => second_moment_eq_variance (hW i hi) (hmean i hi)]
  exact variance_sum_eq_iff_offDiag_covariance_zero hW

/-- **Two-symbol AWGN output power, sharp boundary (power form).**  For a *pair* of
zero-mean square-integrable contributions the output powers add if and only if the two are
uncorrelated:

    E[(W₀ + W₁)²] = E[W₀²] + E[W₁²]  ↔  cov[W₀, W₁] = 0.

This is the exact sharp boundary behind the parent file's two-term AWGN identity
`E[(X + Z)²] = E[X²] + E[Z²]`: for the two-symbol case the single off-diagonal covariance
cannot cancel against anything, so uncorrelatedness is genuinely *necessary* — not merely
sufficient — for the powers to add. -/
theorem awgn_two_symbol_power_eq_iff_covariance_zero [IsProbabilityMeasure μ]
    {W₀ W₁ : Ω → ℝ} (h₀ : MemLp W₀ 2 μ) (h₁ : MemLp W₁ 2 μ)
    (hm₀ : μ[W₀] = 0) (hm₁ : μ[W₁] = 0) :
    μ[(W₀ + W₁) ^ 2] = μ[W₀ ^ 2] + μ[W₁ ^ 2] ↔ cov[W₀, W₁; μ] = 0 := by
  have hsum : MemLp (W₀ + W₁) 2 μ := h₀.add h₁
  have hsum0 : μ[W₀ + W₁] = 0 := by
    simp only [Pi.add_apply]
    rw [integral_add (h₀.integrable one_le_two) (h₁.integrable one_le_two), hm₀, hm₁,
      add_zero]
  rw [second_moment_eq_variance hsum hsum0, second_moment_eq_variance h₀ hm₀,
    second_moment_eq_variance h₁ hm₁]
  exact variance_add_eq_iff_covariance_zero h₀ h₁

/-!
### Quantitative defect and sign-definite monotonicity

The `iff` results above pin the *exact boundary* — the output powers add precisely when the
off-diagonal covariances cancel in aggregate.  The results below record the *signed* content
behind that boundary.  The exact defect `Var[∑] − ∑Var` equals the total off-diagonal
covariance, so when those covariances are **sign-definite** the AWGN output power is
monotone: positive correlation *inflates* it (super-additive), negative correlation
*deflates* it (sub-additive).  The two `iff` theorems are the "defect `= 0`" boundary
between these two regimes.
-/

/-- **Exact variance defect.**  The gap between the variance of a sum and the sum of the
variances is exactly the total off-diagonal covariance:

    Var[∑_{i ∈ s} Wᵢ] − ∑_{i ∈ s} Var[Wᵢ] = ∑_{i ∈ s} ∑_{j ∈ s.erase i} cov[Wᵢ, Wⱼ].

This is the signed strengthening of `variance_sum_eq_iff_offDiag_covariance_zero`, which is
the special case "defect `= 0`". -/
theorem variance_sum_sub_eq_offDiag_covariance [IsFiniteMeasure μ] {ι : Type*}
    [DecidableEq ι] {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ) :
    Var[∑ i ∈ s, W i; μ] - ∑ i ∈ s, Var[W i; μ]
      = ∑ i ∈ s, ∑ j ∈ s.erase i, cov[W i, W j; μ] := by
  have hsplit : ∀ i ∈ s, ∑ j ∈ s, cov[W i, W j; μ]
      = Var[W i; μ] + ∑ j ∈ s.erase i, cov[W i, W j; μ] := by
    intro i hi
    rw [← Finset.add_sum_erase s (fun j => cov[W i, W j; μ]) hi,
      covariance_self (hW i hi).aemeasurable]
  have key : ∑ i ∈ s, ∑ j ∈ s, cov[W i, W j; μ]
      = (∑ i ∈ s, Var[W i; μ]) + ∑ i ∈ s, ∑ j ∈ s.erase i, cov[W i, W j; μ] := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplit
  rw [variance_sum' hW, key]; ring

/-- **Positive correlation inflates output power (super-additivity).**  If every off-diagonal
pair is *non-negatively* correlated, the variance of the sum is at least the sum of the
variances:

    ∑_{i ∈ s} Var[Wᵢ] ≤ Var[∑_{i ∈ s} Wᵢ]. -/
theorem variance_sum_ge_of_nonneg_covariance [IsFiniteMeasure μ] {ι : Type*}
    [DecidableEq ι] {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (hcov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 0 ≤ cov[W i, W j; μ]) :
    ∑ i ∈ s, Var[W i; μ] ≤ Var[∑ i ∈ s, W i; μ] := by
  have hdef := variance_sum_sub_eq_offDiag_covariance hW
  have hnn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, cov[W i, W j; μ] := by
    refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    rw [Finset.mem_erase] at hj
    exact hcov i hi j hj.2 (Ne.symm hj.1)
  linarith [hdef, hnn]

/-- **Negative correlation deflates output power (sub-additivity).**  If every off-diagonal
pair is *non-positively* correlated, the variance of the sum is at most the sum of the
variances:

    Var[∑_{i ∈ s} Wᵢ] ≤ ∑_{i ∈ s} Var[Wᵢ]. -/
theorem variance_sum_le_of_nonpos_covariance [IsFiniteMeasure μ] {ι : Type*}
    [DecidableEq ι] {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (hcov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov[W i, W j; μ] ≤ 0) :
    Var[∑ i ∈ s, W i; μ] ≤ ∑ i ∈ s, Var[W i; μ] := by
  have hdef := variance_sum_sub_eq_offDiag_covariance hW
  have hnp : ∑ i ∈ s, ∑ j ∈ s.erase i, cov[W i, W j; μ] ≤ 0 := by
    refine Finset.sum_nonpos fun i hi => Finset.sum_nonpos fun j hj => ?_
    rw [Finset.mem_erase] at hj
    exact hcov i hi j hj.2 (Ne.symm hj.1)
  linarith [hdef, hnp]

/-- **Positive correlation inflates AWGN output power (power form).**  For a finite family of
*zero-mean* square-integrable contributions with non-negative pairwise covariances, the
aggregate output power is at least the sum of the individual powers:

    ∑_{i ∈ s} E[Wᵢ²] ≤ E[(∑_{i ∈ s} Wᵢ)²].

This is `variance_sum_ge_of_nonneg_covariance` transported into second-moment language via
the zero-mean bridge — the super-additive companion of the sharp boundary
`awgn_multisymbol_power_eq_iff_offDiag_covariance_zero`. -/
theorem awgn_multisymbol_power_ge_of_nonneg_covariance [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {W : ι → Ω → ℝ} {s : Finset ι}
    (hW : ∀ i ∈ s, MemLp (W i) 2 μ) (hmean : ∀ i ∈ s, μ[W i] = 0)
    (hcov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 0 ≤ cov[W i, W j; μ]) :
    ∑ i ∈ s, μ[(W i) ^ 2] ≤ μ[(∑ i ∈ s, W i) ^ 2] := by
  have hSum : MemLp (∑ i ∈ s, W i) 2 μ := memLp_finset_sum' s hW
  have hSum0 : μ[∑ i ∈ s, W i] = 0 := sum_mean_zero hW hmean
  rw [second_moment_eq_variance hSum hSum0,
    show (∑ i ∈ s, μ[(W i) ^ 2]) = ∑ i ∈ s, Var[W i; μ] from
      Finset.sum_congr rfl fun i hi => second_moment_eq_variance (hW i hi) (hmean i hi)]
  exact variance_sum_ge_of_nonneg_covariance hW hcov

end ShannonAWGNMultiSymbolPower
