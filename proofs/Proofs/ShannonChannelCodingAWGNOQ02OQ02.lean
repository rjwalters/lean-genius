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

end ShannonAWGNMultiSymbolPower
