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

/-- **Canonical variance-of-a-sum decomposition (diagonal + twice the strict lower
triangle).**  For any finite, linearly ordered family of square-integrable contributions,

    Var[∑_{i ∈ s} Wᵢ] = ∑_{i ∈ s} Var[Wᵢ]  +  2 · ∑_{i ∈ s} ∑_{j ∈ s, j < i} cov[Wᵢ, Wⱼ].

This is the exact, *quantitative* form of the aggregate-power identity: the excess of the
true output power over the uncorrelated ("Bienaymé") baseline `∑ᵢ Var[Wᵢ]` is precisely
*twice the sum of the pairwise covariances over unordered pairs*.  The factor of two comes
from covariance symmetry (`covariance_comm`): each unordered pair `{i, j}` contributes both
`cov[Wᵢ, Wⱼ]` and `cov[Wⱼ, Wᵢ]` to the full double sum of `variance_sum'`, and these are
equal.  Specialising to `s = {0, 1}` recovers the two-symbol law `Var[W₀ + W₁] =
Var[W₀] + Var[W₁] + 2·cov[W₀, W₁]`, and setting all off-diagonal covariances to zero
recovers `variance_sum_of_pairwise_uncorrelated`.  This sharpens the qualitative
`variance_sum_eq_iff_offDiag_covariance_zero` by giving the closed-form defect rather than
just its vanishing criterion, and it halves the number of covariance terms that must be
controlled (one per unordered pair, not per ordered pair). -/
theorem variance_sum_eq_diag_add_two_mul_lowerTriangle [IsFiniteMeasure μ] {ι : Type*}
    [LinearOrder ι] {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ) :
    Var[∑ i ∈ s, W i; μ]
      = ∑ i ∈ s, Var[W i; μ]
        + 2 * ∑ i ∈ s, ∑ j ∈ s with j < i, cov[W i, W j; μ] := by
  -- The strict *upper* triangle equals the strict *lower* triangle, by covariance symmetry.
  have hUL : ∑ i ∈ s, ∑ j ∈ s with i < j, cov[W i, W j; μ]
      = ∑ i ∈ s, ∑ j ∈ s with j < i, cov[W i, W j; μ] := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_comm]
  -- Split each inner sum by trichotomy: diagonal `j = i` gives the variance, the two
  -- off-diagonal parts give the lower and upper triangles.
  have hsplit : ∀ i ∈ s, ∑ j ∈ s, cov[W i, W j; μ]
      = Var[W i; μ]
        + (∑ j ∈ s with j < i, cov[W i, W j; μ]
           + ∑ j ∈ s with i < j, cov[W i, W j; μ]) := by
    intro i hi
    have hpt : ∀ j, cov[W i, W j; μ]
        = (if j < i then cov[W i, W j; μ] else 0)
          + (if j = i then cov[W i, W j; μ] else 0)
          + (if i < j then cov[W i, W j; μ] else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp [h, h.ne, lt_asymm h]
      · simp [h]
      · simp [h, h.ne', lt_asymm h]
    calc ∑ j ∈ s, cov[W i, W j; μ]
        = ∑ j ∈ s, ((if j < i then cov[W i, W j; μ] else 0)
            + (if j = i then cov[W i, W j; μ] else 0)
            + (if i < j then cov[W i, W j; μ] else 0)) :=
          Finset.sum_congr rfl fun j _ => hpt j
      _ = (∑ j ∈ s, if j < i then cov[W i, W j; μ] else 0)
            + (∑ j ∈ s, if j = i then cov[W i, W j; μ] else 0)
            + (∑ j ∈ s, if i < j then cov[W i, W j; μ] else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = Var[W i; μ]
            + (∑ j ∈ s with j < i, cov[W i, W j; μ]
               + ∑ j ∈ s with i < j, cov[W i, W j; μ]) := by
          rw [Finset.sum_ite_eq' s i (fun j => cov[W i, W j; μ]), if_pos hi,
            covariance_self (hW i hi).aemeasurable, ← Finset.sum_filter, ← Finset.sum_filter]
          ring
  rw [variance_sum' hW, Finset.sum_congr rfl hsplit,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hUL]
  ring

/-!
### Sharp *inequality* boundary: the correlated case (subadditivity of standard deviation)

The results above pin down exactly *when* the powers add (`Var[∑Wᵢ] = ∑Var[Wᵢ]` ⟺ total
off-diagonal covariance vanishes).  When the contributions are **correlated** the equality
fails, but a sharp two-sided *inequality* survives.  The engine is the Cauchy–Schwarz
inequality for covariance,

    cov[X, Y]² ≤ Var[X] · Var[Y],

which — perhaps surprisingly — is **not** in Mathlib's probability layer (only the double-sum
`variance_sum'` and independence-based `IndepFun.variance_sum` are).  We supply it here via the
classical discriminant argument: the quadratic `t ↦ Var[X + t·Y] ≥ 0` is nonnegative for all
`t`, so its discriminant `(2·cov)² − 4·Var[Y]·Var[X]` is `≤ 0`.

From it follows the **triangle inequality for standard deviation** `σ[∑Wᵢ] ≤ ∑σ[Wᵢ]`
(`σ = √Var`), the sharp *inequality* companion to the equality boundary above: correlated
contributions can only *lose* power relative to the additive prediction bounded by the sum of
the individual standard deviations — this is exactly the L² triangle (Minkowski) inequality on
the centered contributions, and it holds with **no** independence or uncorrelatedness
hypothesis at all.
-/

/-- **Cauchy–Schwarz inequality for covariance.**  For square-integrable `X, Y`,

        cov[X, Y]² ≤ Var[X] · Var[Y].

Proof by the classical discriminant argument: for every real `t` the variance of `X + t·Y` is
nonnegative, giving a nonnegative quadratic `Var[Y]·t² + 2·cov[X,Y]·t + Var[X] ≥ 0` in `t`,
whose discriminant is therefore `≤ 0`.  This foundational bound is absent from Mathlib's
probability layer (which carries only `variance_sum'` and `IndepFun.variance_sum`), and is the
engine behind the standard-deviation triangle inequality below. -/
theorem covariance_sq_le_variance_mul_variance [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  have hquad : ∀ t : ℝ,
      0 ≤ Var[Y; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[X; μ] := by
    intro t
    have h := variance_nonneg (X + t • Y) μ
    rw [variance_add hX (hY.const_smul t), covariance_smul_right, variance_smul] at h
    nlinarith [h]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **Cauchy–Schwarz for covariance, root form.**  `|cov[X, Y]| ≤ √(Var[X] · Var[Y])`. -/
theorem abs_covariance_le_sqrt [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |cov[X, Y; μ]| ≤ Real.sqrt (Var[X; μ] * Var[Y; μ]) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (covariance_sq_le_variance_mul_variance hX hY)

/-- **Triangle inequality for standard deviation (two terms).**  For square-integrable `X, Y`,

        √Var[X + Y] ≤ √Var[X] + √Var[Y].

This is the sharp *inequality* boundary complementing `variance_add_eq_iff_covariance_zero`:
equality of `Var[X+Y]` with `Var[X]+Var[Y]` requires `cov[X,Y]=0`, but the standard deviation of
the sum is always at most the sum of the standard deviations — the L² triangle inequality on the
centered variables, needing no independence hypothesis. -/
theorem stddev_add_le [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Real.sqrt (Var[X + Y; μ]) ≤ Real.sqrt (Var[X; μ]) + Real.sqrt (Var[Y; μ]) := by
  have hcov : cov[X, Y; μ] ≤ Real.sqrt (Var[X; μ]) * Real.sqrt (Var[Y; μ]) :=
    calc cov[X, Y; μ] ≤ |cov[X, Y; μ]| := le_abs_self _
      _ ≤ Real.sqrt (Var[X; μ] * Var[Y; μ]) := abs_covariance_le_sqrt hX hY
      _ = Real.sqrt (Var[X; μ]) * Real.sqrt (Var[Y; μ]) :=
          Real.sqrt_mul (variance_nonneg _ _) _
  have hbound : Var[X + Y; μ] ≤ (Real.sqrt (Var[X; μ]) + Real.sqrt (Var[Y; μ])) ^ 2 := by
    rw [variance_add hX hY]
    have hsx : Real.sqrt (Var[X; μ]) ^ 2 = Var[X; μ] := Real.sq_sqrt (variance_nonneg _ _)
    have hsy : Real.sqrt (Var[Y; μ]) ^ 2 = Var[Y; μ] := Real.sq_sqrt (variance_nonneg _ _)
    nlinarith [hcov, hsx, hsy]
  calc Real.sqrt (Var[X + Y; μ])
      ≤ Real.sqrt ((Real.sqrt (Var[X; μ]) + Real.sqrt (Var[Y; μ])) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (Var[X; μ]) + Real.sqrt (Var[Y; μ]) :=
        Real.sqrt_sq (by positivity)

/-- **Triangle inequality for standard deviation (finite sum, capstone).**  For any finite
family of square-integrable contributions,

        σ[∑_{i ∈ s} Wᵢ] ≤ ∑_{i ∈ s} σ[Wᵢ]        (σ = √Var).

This is the sharp *inequality* companion to
`variance_sum_eq_iff_offDiag_covariance_zero`: the aggregate output standard deviation never
exceeds the sum of the per-contribution standard deviations, whatever the correlations, with
equality forced only in the fully-aligned (perfectly correlated) case.  For the AWGN power
budget it bounds the aggregate output amplitude `√E[(∑Wᵢ)²]` of zero-mean contributions by the
sum of the individual RMS amplitudes — a distribution-free ceiling requiring neither
independence nor uncorrelatedness. -/
theorem stddev_sum_le [IsFiniteMeasure μ] {ι : Type*} {W : ι → Ω → ℝ}
    (hW : ∀ i, MemLp (W i) 2 μ) (s : Finset ι) :
    Real.sqrt (Var[∑ i ∈ s, W i; μ]) ≤ ∑ i ∈ s, Real.sqrt (Var[W i; μ]) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc Real.sqrt (Var[W a + ∑ i ∈ t, W i; μ])
          ≤ Real.sqrt (Var[W a; μ]) + Real.sqrt (Var[∑ i ∈ t, W i; μ]) :=
            stddev_add_le (hW a) (memLp_finset_sum' t (fun i _ => hW i))
        _ ≤ Real.sqrt (Var[W a; μ]) + ∑ i ∈ t, Real.sqrt (Var[W i; μ]) := by gcongr

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

/-!
### Sharp *equality* boundary: when Cauchy–Schwarz is tight (a.e. affine dependence)

The covariance Cauchy–Schwarz inequality `cov[X, Y]² ≤ Var[X]·Var[Y]` proved above raises the
sharp question of its **equality case**.  The answer is the classical one: equality holds *iff*
`X` and `Y` are **almost-everywhere affinely dependent**.  The engine is the exact identity

    Var[Var[Y]·X − cov[X,Y]·Y] = Var[Y]·(Var[X]·Var[Y] − cov[X,Y]²),

so, when `Var[Y] ≠ 0`, the (unnormalised) regression residual `Var[Y]·X − cov[X,Y]·Y` has *zero
variance* — hence is a.e. constant — exactly when Cauchy–Schwarz is tight.  Dividing through by
`Var[Y]` exhibits `X` as an a.e. affine function of `Y` with the **regression slope**
`cov[X,Y]/Var[Y]`.  This is the sharp equality companion to the inequality boundary `stddev_add_le`,
and completes the second-order picture: vanishing off-diagonal covariance makes the powers *add*
(`awgn_multisymbol_power_of_uncorrelated`), while perfect (affine) dependence makes Cauchy–Schwarz
*tight*.
-/

/-- **Variance zero ⟺ a.e. constant.**  For a square-integrable random variable the variance
vanishes exactly when the variable is almost everywhere equal to its mean.  This is the real-valued
companion of Mathlib's `ProbabilityTheory.evariance_eq_zero_iff`, obtained by discharging the
`⊤` branch of `ENNReal.toReal_eq_zero_iff` via `MemLp.evariance_ne_top`. -/
theorem variance_eq_zero_iff [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[X; μ] = 0 ↔ X =ᵐ[μ] fun _ => μ[X] := by
  have hdef : Var[X; μ] = (evariance X μ).toReal := rfl
  rw [hdef, ENNReal.toReal_eq_zero_iff, or_iff_left hX.evariance_ne_top,
    evariance_eq_zero_iff hX.aemeasurable]

/-- **Regression-residual variance identity.**  The variance of the unnormalised regression residual
`Var[Y]·X − cov[X,Y]·Y` factors exactly through the Cauchy–Schwarz defect:

    Var[Var[Y]·X − cov[X,Y]·Y] = Var[Y]·(Var[X]·Var[Y] − cov[X,Y]²).

This is a pure second-moment identity (no independence hypothesis).  Because the left-hand side is a
variance it is `≥ 0`, which re-derives `covariance_sq_le_variance_mul_variance` whenever `Var[Y] > 0`;
its sharper role is to pin down the *equality* case below. -/
theorem variance_regression_residual [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[Var[Y; μ] • X - cov[X, Y; μ] • Y; μ]
      = Var[Y; μ] * (Var[X; μ] * Var[Y; μ] - cov[X, Y; μ] ^ 2) := by
  rw [variance_sub (hX.const_smul _) (hY.const_smul _), variance_smul, variance_smul,
    covariance_smul_left, covariance_smul_right]
  ring

/-- **Sharp equality boundary of covariance Cauchy–Schwarz.**  For square-integrable `X, Y` with `Y`
non-degenerate (`Var[Y] ≠ 0`), the Cauchy–Schwarz inequality `covariance_sq_le_variance_mul_variance`
is *tight* — `cov[X,Y]² = Var[X]·Var[Y]` — if and only if the regression residual
`Var[Y]·X − cov[X,Y]·Y` is almost everywhere constant.  This is the exact equality companion to that
inequality, obtained from the residual-variance identity `variance_regression_residual` together with
`variance_eq_zero_iff`. -/
theorem covariance_sq_eq_variance_mul_variance_iff [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hYnd : Var[Y; μ] ≠ 0) :
    cov[X, Y; μ] ^ 2 = Var[X; μ] * Var[Y; μ] ↔
      (Var[Y; μ] • X - cov[X, Y; μ] • Y) =ᵐ[μ]
        fun _ => μ[Var[Y; μ] • X - cov[X, Y; μ] • Y] := by
  rw [← variance_eq_zero_iff ((hX.const_smul _).sub (hY.const_smul _)),
    variance_regression_residual hX hY]
  constructor
  · intro h; rw [h]; ring
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hYnd
    · linarith

/-- **Equality in Cauchy–Schwarz ⟹ a.e. affine dependence (regression line).**  If `Y` is
non-degenerate (`Var[Y] ≠ 0`) and Cauchy–Schwarz is tight, then `X` is almost everywhere an affine
function of `Y`, with slope the regression coefficient `cov[X,Y]/Var[Y]`:

    X =ᵐ (cov[X,Y]/Var[Y])·Y + b.

This is the textbook "equality in Cauchy–Schwarz ⟺ linear dependence", specialised to the covariance
inner product on centered square-integrable variables — the sharp structural consequence of the
equality boundary `covariance_sq_eq_variance_mul_variance_iff`. -/
theorem exists_affine_of_covariance_sq_eq [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hYnd : Var[Y; μ] ≠ 0)
    (h : cov[X, Y; μ] ^ 2 = Var[X; μ] * Var[Y; μ]) :
    ∃ b : ℝ, X =ᵐ[μ] fun ω => (cov[X, Y; μ] / Var[Y; μ]) * Y ω + b := by
  refine ⟨μ[Var[Y; μ] • X - cov[X, Y; μ] • Y] / Var[Y; μ], ?_⟩
  have hae := (covariance_sq_eq_variance_mul_variance_iff hX hY hYnd).mp h
  filter_upwards [hae] with ω hω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hω ⊢
  field_simp
  linear_combination hω

/-- **Covariance is preserved under a.e. equality of the left argument.**  If `X =ᵐ X'` then their
covariances against any common `Y` agree.  This is the covariance companion of
`ProbabilityTheory.variance_congr` (which Mathlib provides but has no covariance analogue); it is
proved directly from the defining integral via `integral_congr_ae`, and is exactly what lets the
affine-dependence *converse* below accept an arbitrary a.e. representative of `X`. -/
theorem covariance_congr_left {X X' Y : Ω → ℝ} (h : X =ᵐ[μ] X') :
    cov[X, Y; μ] = cov[X', Y; μ] := by
  have hmean : μ[X] = μ[X'] := integral_congr_ae h
  simp only [covariance]
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω, hmean]

/-- **Affine dependence ⟹ Cauchy–Schwarz is tight — converse of `exists_affine_of_covariance_sq_eq`.**
If `X` is almost everywhere an affine function of `Y`, `X =ᵐ a·Y + b`, then the covariance
Cauchy–Schwarz inequality is an *equality*: `cov[X,Y]² = Var[X]·Var[Y]`.  Unlike the forward
direction this needs **no** non-degeneracy hypothesis on `Y` — it is a direct bilinear computation
(`cov[X,Y] = a·Var[Y]` and `Var[X] = a²·Var[Y]`) transported along the a.e. identity via
`covariance_congr_left` and `variance_congr`. -/
theorem covariance_sq_eq_of_affine [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) (a b : ℝ) (h : X =ᵐ[μ] fun ω => a * Y ω + b) :
    cov[X, Y; μ] ^ 2 = Var[X; μ] * Var[Y; μ] := by
  have hYint : Integrable (fun ω => a * Y ω) μ := (hY.integrable one_le_two).const_mul a
  have hcov : cov[X, Y; μ] = a * Var[Y; μ] := by
    rw [covariance_congr_left h, covariance_add_const_left hYint b,
      covariance_const_mul_left, covariance_self hY.aemeasurable]
  have hvar : Var[X; μ] = a ^ 2 * Var[Y; μ] := by
    have hsmul : (fun ω => a * Y ω) = a • Y := by
      funext ω; rw [Pi.smul_apply, smul_eq_mul]
    rw [variance_congr h, variance_add_const (hY.aestronglyMeasurable.const_mul a) b, hsmul,
      variance_smul]
  rw [hcov, hvar]; ring

/-- **Sharp equality boundary of covariance Cauchy–Schwarz — full iff form.**  For square-integrable
`X, Y` with `Y` non-degenerate (`Var[Y] ≠ 0`), `cov[X,Y]² = Var[X]·Var[Y]` holds *exactly* when `X`
is almost everywhere an affine function of `Y`.  Combines the forward direction
`exists_affine_of_covariance_sq_eq` (tightness ⟹ regression line) with the converse
`covariance_sq_eq_of_affine` (affine ⟹ tightness), giving the complete structural characterisation
of the equality case: **Cauchy–Schwarz is tight iff `X` and `Y` are a.e. affinely dependent.** -/
theorem covariance_sq_eq_variance_mul_variance_iff_affine [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hYnd : Var[Y; μ] ≠ 0) :
    cov[X, Y; μ] ^ 2 = Var[X; μ] * Var[Y; μ] ↔
      ∃ a b : ℝ, X =ᵐ[μ] fun ω => a * Y ω + b := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_affine_of_covariance_sq_eq hX hY hYnd h
    exact ⟨cov[X, Y; μ] / Var[Y; μ], b, hb⟩
  · rintro ⟨a, b, hab⟩
    exact covariance_sq_eq_of_affine hY a b hab

/-!
### Normalised capstone: the Pearson correlation coefficient ρ = cov/(σ_X·σ_Y)

The equality boundary above is most cleanly expressed through the **correlation coefficient**

    ρ[X, Y] = cov[X, Y] / (σ_X · σ_Y),        σ_X = √Var[X],  σ_Y = √Var[Y],

the dimensionless normalisation of the covariance.  The covariance Cauchy–Schwarz inequality
becomes the sharp statement `|ρ| ≤ 1` (needing *no* non-degeneracy hypothesis — the
division-by-zero convention absorbs the degenerate case), and the equality boundary
`covariance_sq_eq_variance_mul_variance_iff_affine` becomes its normalised capstone:
`|ρ| = 1` holds **exactly** when `X` and `Y` are a.e. affinely dependent.  This is the standard
correlation-coefficient packaging of the second-order theory built above.
-/

/-- **Pearson correlation coefficient.**  The covariance normalised by the product of the
standard deviations, `ρ[X, Y] = cov[X, Y] / (√Var[X] · √Var[Y])`.  With the Lean
division-by-zero convention `ρ = 0` whenever either variable is degenerate. -/
noncomputable def correlation (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  cov[X, Y; μ] / (Real.sqrt (Var[X; μ]) * Real.sqrt (Var[Y; μ]))

/-- **Correlation squared is the Cauchy–Schwarz ratio.**  `ρ² = cov² / (Var[X]·Var[Y])`, obtained
by squaring the defining quotient and collapsing `(√Var)² = Var`.  This is the algebraic bridge
between the normalised coefficient and the covariance Cauchy–Schwarz inequality. -/
theorem correlation_sq (X Y : Ω → ℝ) (μ : Measure Ω) :
    correlation X Y μ ^ 2 = cov[X, Y; μ] ^ 2 / (Var[X; μ] * Var[Y; μ]) := by
  rw [correlation, div_pow, mul_pow, Real.sq_sqrt (variance_nonneg _ _),
    Real.sq_sqrt (variance_nonneg _ _)]

/-- **|ρ| ≤ 1 — covariance Cauchy–Schwarz, normalised.**  The correlation coefficient always lies
in `[-1, 1]`, needing *no* non-degeneracy hypothesis: when either variable is degenerate the
quotient is `0` by the division-by-zero convention, and otherwise `ρ² ≤ 1` follows from
`covariance_sq_le_variance_mul_variance`. -/
theorem abs_correlation_le_one [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |correlation X Y μ| ≤ 1 := by
  have h2 : correlation X Y μ ^ 2 ≤ 1 := by
    rw [correlation_sq]
    rcases eq_or_lt_of_le (mul_nonneg (variance_nonneg X μ) (variance_nonneg Y μ)) with hz | hpos
    · rw [← hz, div_zero]; norm_num
    · rw [div_le_one hpos]; exact covariance_sq_le_variance_mul_variance hX hY
  rw [abs_le]
  constructor <;>
    nlinarith [h2, sq_nonneg (correlation X Y μ - 1), sq_nonneg (correlation X Y μ + 1)]

/-- **ρ² = 1 ⟺ a.e. affine dependence (normalised equality boundary).**  For non-degenerate
`X, Y` (`Var[X] ≠ 0`, `Var[Y] ≠ 0`) the correlation coefficient is extremal — `ρ² = 1` — *exactly*
when `X` is almost everywhere an affine function of `Y`.  This is
`covariance_sq_eq_variance_mul_variance_iff_affine` normalised through `correlation_sq`; both
non-degeneracy hypotheses are genuinely needed, since a degenerate variable makes `ρ = 0 ≠ ±1`
while the affine relation `X =ᵐ 0·Y + μ[X]` still holds. -/
theorem correlation_sq_eq_one_iff_affine [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXnd : Var[X; μ] ≠ 0) (hYnd : Var[Y; μ] ≠ 0) :
    correlation X Y μ ^ 2 = 1 ↔ ∃ a b : ℝ, X =ᵐ[μ] fun ω => a * Y ω + b := by
  rw [correlation_sq, div_eq_one_iff_eq (mul_ne_zero hXnd hYnd)]
  exact covariance_sq_eq_variance_mul_variance_iff_affine hX hY hYnd

/-- **|ρ| = 1 ⟺ a.e. affine dependence — the normalised capstone.**  For non-degenerate `X, Y`
the correlation coefficient attains its extreme value `|ρ| = 1` *exactly* when `X` and `Y` are
almost everywhere affinely dependent (perfect ±correlation).  This is the dimensionless
restatement of the sharp Cauchy–Schwarz equality boundary
`covariance_sq_eq_variance_mul_variance_iff_affine`, obtained from `correlation_sq_eq_one_iff_affine`
via `|ρ| = 1 ↔ ρ² = 1`. -/
theorem abs_correlation_eq_one_iff_affine [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXnd : Var[X; μ] ≠ 0) (hYnd : Var[Y; μ] ≠ 0) :
    |correlation X Y μ| = 1 ↔ ∃ a b : ℝ, X =ᵐ[μ] fun ω => a * Y ω + b := by
  rw [← correlation_sq_eq_one_iff_affine hX hY hXnd hYnd]
  constructor
  · intro h; rw [← sq_abs, h]; norm_num
  · intro h; rw [← Real.sqrt_sq_eq_abs, h, Real.sqrt_one]

/-!
### Signed capstone: distinguishing perfect positive from perfect negative correlation

The capstone `abs_correlation_eq_one_iff_affine` locates the extremal case `|ρ| = 1` but is blind to
the **sign** of the correlation.  The sharp refinement records that the sign of `ρ` is exactly the
sign of the regression slope: when `X =ᵐ a·Y + b` with `a ≠ 0` and `Y` non-degenerate,

    ρ[X, Y] = a / |a| = sign a,

because `cov[X,Y] = a·Var[Y]`, `σ_X = |a|·σ_Y`, so the normalisation collapses to `a/|a|`.  Hence
`ρ = +1` picks out the *increasing* affine relations (`a > 0`, perfect positive correlation) and
`ρ = -1` the *decreasing* ones (`a < 0`, perfect negative correlation) — the two endpoints of the
Cauchy–Schwarz interval `[-1, 1]` are structurally different, not merely `|ρ| = 1`.
-/

/-- **Variance under an a.e. affine change of variable.**  If `X =ᵐ a·Y + b` then
`Var[X] = a²·Var[Y]`; the additive constant drops and the multiplicative slope scales the variance
by `a²`.  Extracted from the equality-boundary computation so the signed capstones can reuse it. -/
theorem variance_eq_of_affine [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) (a b : ℝ) (h : X =ᵐ[μ] fun ω => a * Y ω + b) :
    Var[X; μ] = a ^ 2 * Var[Y; μ] := by
  have hsmul : (fun ω => a * Y ω) = a • Y := by
    funext ω; rw [Pi.smul_apply, smul_eq_mul]
  rw [variance_congr h, variance_add_const (hY.aestronglyMeasurable.const_mul a) b, hsmul,
    variance_smul]

/-- **Correlation of an a.e. affine pair is the sign of the slope.**  For non-degenerate `Y` and a
nonzero slope `a`, if `X =ᵐ a·Y + b` then `ρ[X, Y] = a / |a|` (i.e. `+1` when `a > 0` and `-1` when
`a < 0`).  This is the signed sharpening of `covariance_sq_eq_of_affine`: normalising the covariance
`a·Var[Y]` by `σ_X·σ_Y = |a|·Var[Y]` cancels the magnitude of the slope and leaves only its sign. -/
theorem correlation_eq_of_affine [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) {a b : ℝ} (ha : a ≠ 0) (hYnd : Var[Y; μ] ≠ 0)
    (h : X =ᵐ[μ] fun ω => a * Y ω + b) :
    correlation X Y μ = a / |a| := by
  have hYint : Integrable (fun ω => a * Y ω) μ := (hY.integrable one_le_two).const_mul a
  have hcov : cov[X, Y; μ] = a * Var[Y; μ] := by
    rw [covariance_congr_left h, covariance_add_const_left hYint b,
      covariance_const_mul_left, covariance_self hY.aemeasurable]
  have hsqrtX : Real.sqrt (Var[X; μ]) = |a| * Real.sqrt (Var[Y; μ]) := by
    rw [variance_eq_of_affine hY a b h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  have hs : Real.sqrt (Var[Y; μ]) * Real.sqrt (Var[Y; μ]) = Var[Y; μ] :=
    Real.mul_self_sqrt (variance_nonneg _ _)
  have haa : |a| ≠ 0 := abs_ne_zero.mpr ha
  rw [correlation, hcov, hsqrtX, mul_assoc, hs]
  field_simp

/-- **ρ = 1 ⟺ a.e. increasing affine dependence (perfect positive correlation).**  For
non-degenerate `X, Y` the correlation attains its maximum `+1` *exactly* when `X` is almost
everywhere an affine function of `Y` with **positive** slope.  Refines
`abs_correlation_eq_one_iff_affine`: it is the `+1` endpoint, distinguished from the `-1` endpoint by
the sign of the regression slope. -/
theorem correlation_eq_one_iff_affine_pos [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXnd : Var[X; μ] ≠ 0) (hYnd : Var[Y; μ] ≠ 0) :
    correlation X Y μ = 1 ↔ ∃ a b : ℝ, 0 < a ∧ X =ᵐ[μ] fun ω => a * Y ω + b := by
  constructor
  · intro h
    have hsq : correlation X Y μ ^ 2 = 1 := by rw [h]; norm_num
    obtain ⟨a, b, hab⟩ := (correlation_sq_eq_one_iff_affine hX hY hXnd hYnd).mp hsq
    have ha : a ≠ 0 := by
      rintro rfl
      exact hXnd (by rw [variance_eq_of_affine hY 0 b hab]; ring)
    have hval : correlation X Y μ = a / |a| := correlation_eq_of_affine hY ha hYnd hab
    refine ⟨a, b, ?_, hab⟩
    rcases ha.lt_or_gt with hneg | hpos
    · rw [h, abs_of_neg hneg, div_neg, div_self ha] at hval; norm_num at hval
    · exact hpos
  · rintro ⟨a, b, ha, hab⟩
    rw [correlation_eq_of_affine hY ha.ne' hYnd hab, abs_of_pos ha, div_self ha.ne']

/-- **ρ = -1 ⟺ a.e. decreasing affine dependence (perfect negative correlation).**  For
non-degenerate `X, Y` the correlation attains its minimum `-1` *exactly* when `X` is almost
everywhere an affine function of `Y` with **negative** slope.  The `-1` endpoint companion of
`correlation_eq_one_iff_affine_pos`; together they split `abs_correlation_eq_one_iff_affine` into its
two structurally distinct extremes. -/
theorem correlation_eq_neg_one_iff_affine_neg [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXnd : Var[X; μ] ≠ 0) (hYnd : Var[Y; μ] ≠ 0) :
    correlation X Y μ = -1 ↔ ∃ a b : ℝ, a < 0 ∧ X =ᵐ[μ] fun ω => a * Y ω + b := by
  constructor
  · intro h
    have hsq : correlation X Y μ ^ 2 = 1 := by rw [h]; norm_num
    obtain ⟨a, b, hab⟩ := (correlation_sq_eq_one_iff_affine hX hY hXnd hYnd).mp hsq
    have ha : a ≠ 0 := by
      rintro rfl
      exact hXnd (by rw [variance_eq_of_affine hY 0 b hab]; ring)
    have hval : correlation X Y μ = a / |a| := correlation_eq_of_affine hY ha hYnd hab
    refine ⟨a, b, ?_, hab⟩
    rcases ha.lt_or_gt with hneg | hpos
    · exact hneg
    · rw [h, abs_of_pos hpos, div_self ha] at hval; norm_num at hval
  · rintro ⟨a, b, ha, hab⟩
    rw [correlation_eq_of_affine hY ha.ne hYnd hab, abs_of_neg ha, div_neg, div_self ha.ne]

/-!
### Structural companion: affine invariance of the correlation coefficient

The signed capstones locate `ρ = ±1` at the increasing/decreasing affine extremes.  The dual
structural fact is that `ρ` is a *dimensionless* invariant: it is unchanged by any pair of
orientation-preserving affine changes of units and merely flips sign under orientation-reversing
ones.  Concretely, for arbitrary scales `a, c` and shifts `b, d`,

    ρ[a·X + b, c·Y + d] = sign(a·c) · ρ[X, Y],

because the additive shifts cancel (covariance and variance are translation-invariant) and the
multiplicative scales cancel in magnitude against the standard deviations `σ[a·X+b] = |a|·σ[X]`,
leaving only the sign of the slope product `a·c`.  This is the defining property that makes the
Pearson coefficient a scale-free measure of linear association.
-/

/-- **Sign as a normalised quotient.**  `Real.sign x = x / |x|` for every real `x`, including
`x = 0`, where both sides are `0` under the division-by-zero convention.  The scalar bridge used to
package the affine-invariance normalisation. -/
private theorem real_sign_eq_self_div_abs (x : ℝ) : Real.sign x = x / |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h, div_neg, div_self h.ne]
  · rw [h, Real.sign_zero, zero_div]
  · rw [Real.sign_of_pos h, abs_of_pos h, div_self h.ne']

/-- **Affine invariance of the correlation coefficient (up to the sign of the slopes).**
For square-integrable `X, Y` and any affine reparametrisations `X' = a·X + b`, `Y' = c·Y + d`,

    ρ[a·X + b, c·Y + d] = sign(a·c) · ρ[X, Y].

The additive shifts `b, d` drop out because covariance and variance are translation-invariant, and
the multiplicative scales `a, c` cancel in magnitude against the standard deviations
`σ[a·X+b] = |a|·σ[X]`, leaving only the sign of the product `a·c`.  This is the defining
*dimensionless* property of the Pearson coefficient: it is unchanged by orientation-preserving
affine changes of units (`a·c > 0`) and merely flips sign under orientation-reversing ones
(`a·c < 0`).  No non-degeneracy hypothesis is needed — the identity also holds in the degenerate
cases via the division-by-zero convention. -/
theorem correlation_affine_invariant [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b c d : ℝ) :
    correlation (fun ω => a * X ω + b) (fun ω => c * Y ω + d) μ
      = Real.sign (a * c) * correlation X Y μ := by
  have hIaX : Integrable (fun ω => a * X ω) μ := (hX.integrable one_le_two).const_mul a
  have hIcY : Integrable (fun ω => c * Y ω) μ := (hY.integrable one_le_two).const_mul c
  have hcov : cov[fun ω => a * X ω + b, fun ω => c * Y ω + d; μ] = a * c * cov[X, Y; μ] := by
    rw [covariance_add_const_left hIaX b, covariance_const_mul_left,
      covariance_add_const_right hIcY d, covariance_const_mul_right]; ring
  have hpX : Real.sqrt (Var[fun ω => a * X ω + b; μ]) = |a| * Real.sqrt (Var[X; μ]) := by
    rw [variance_eq_of_affine hX a b (Filter.EventuallyEq.refl _ _), Real.sqrt_mul (sq_nonneg a),
      Real.sqrt_sq_eq_abs]
  have hpY : Real.sqrt (Var[fun ω => c * Y ω + d; μ]) = |c| * Real.sqrt (Var[Y; μ]) := by
    rw [variance_eq_of_affine hY c d (Filter.EventuallyEq.refl _ _), Real.sqrt_mul (sq_nonneg c),
      Real.sqrt_sq_eq_abs]
  simp only [correlation]
  rw [hcov, hpX, hpY, real_sign_eq_self_div_abs, abs_mul]
  ring

/-- **Scale-and-shift invariance (orientation-preserving case).**  Correlation is *exactly*
preserved by any pair of increasing affine reparametrisations (`a, c > 0`):
`ρ[a·X + b, c·Y + d] = ρ[X, Y]`.  The dimensionless-invariance specialisation of
`correlation_affine_invariant` with `sign(a·c) = 1` — the precise sense in which the Pearson
coefficient is independent of the choice of units and origin. -/
theorem correlation_affine_invariant_of_pos [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (b d : ℝ) :
    correlation (fun ω => a * X ω + b) (fun ω => c * Y ω + d) μ = correlation X Y μ := by
  rw [correlation_affine_invariant hX hY a b c d, Real.sign_of_pos (mul_pos ha hc), one_mul]

/-!
### Sharp equality boundary of the standard-deviation triangle inequality

`stddev_add_le` states the L² triangle inequality `σ[X+Y] ≤ σ[X] + σ[Y]` for the aggregate
standard deviation.  The results below pin down its **equality** boundary — the exact condition
under which the ceiling is attained.  Squaring the (nonnegative) triangle inequality reduces the
equality `σ[X+Y] = σ[X] + σ[Y]` to `cov[X,Y] = σ[X]·σ[Y]`, i.e. covariance attaining its
Cauchy–Schwarz maximum, which for non-degenerate variables is exactly the perfect *positive*
correlation `ρ = +1`.  This is the sharp companion of `variance_add_eq_iff_covariance_zero` (whose
equality boundary is the *uncorrelated* case `cov = 0`), sitting at the opposite extreme of the
Cauchy–Schwarz interval.
-/

/-- **Equality boundary of the standard-deviation triangle inequality (covariance form).**  For
square-integrable `X, Y`, the L² triangle inequality `σ[X+Y] ≤ σ[X] + σ[Y]` of `stddev_add_le` is
an *equality*

        √Var[X + Y] = √Var[X] + √Var[Y]

*if and only if* the covariance attains its Cauchy–Schwarz maximum `cov[X,Y] = √Var[X]·√Var[Y]`.
No non-degeneracy hypothesis is needed: when e.g. `Y` is a.e. constant both sides read
`σ[X] = σ[X]` and `cov = 0 = σ[X]·0`.  Squaring the nonnegative identity turns it into the linear
comparison `Var[X]+Var[Y]+2cov = (√Var[X]+√Var[Y])²`, from which the covariance value is forced. -/
theorem stddev_add_eq_iff_covariance_eq_sqrt [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Real.sqrt (Var[X + Y; μ]) = Real.sqrt (Var[X; μ]) + Real.sqrt (Var[Y; μ]) ↔
      cov[X, Y; μ] = Real.sqrt (Var[X; μ]) * Real.sqrt (Var[Y; μ]) := by
  set a := Real.sqrt (Var[X; μ]) with ha_def
  set b := Real.sqrt (Var[Y; μ]) with hb_def
  have hsx : a ^ 2 = Var[X; μ] := Real.sq_sqrt (variance_nonneg _ _)
  have hsy : b ^ 2 = Var[Y; μ] := Real.sq_sqrt (variance_nonneg _ _)
  constructor
  · intro h
    have h2 : Var[X + Y; μ] = (a + b) ^ 2 := by
      rw [← h, Real.sq_sqrt (variance_nonneg (X + Y) μ)]
    nlinarith [h2, variance_add hX hY, hsx, hsy]
  · intro h
    have h2 : Var[X + Y; μ] = (a + b) ^ 2 := by
      nlinarith [variance_add hX hY, hsx, hsy, h]
    rw [h2, Real.sqrt_sq (by positivity)]

/-- **Equality boundary of the standard-deviation triangle inequality (correlation form).**  For
non-degenerate `X, Y` the triangle inequality `σ[X+Y] ≤ σ[X] + σ[Y]` is an equality *exactly* when
the correlation coefficient attains its maximum:

        √Var[X + Y] = √Var[X] + √Var[Y]  ↔  ρ[X, Y] = 1.

The covariance-form condition `cov = √Var[X]·√Var[Y]` of
`stddev_add_eq_iff_covariance_eq_sqrt`, normalised through the definition of `correlation`; the two
non-degeneracy hypotheses make the normalising denominator `σ[X]·σ[Y]` nonzero. -/
theorem stddev_add_eq_iff_correlation_eq_one [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXnd : Var[X; μ] ≠ 0) (hYnd : Var[Y; μ] ≠ 0) :
    Real.sqrt (Var[X + Y; μ]) = Real.sqrt (Var[X; μ]) + Real.sqrt (Var[Y; μ]) ↔
      correlation X Y μ = 1 := by
  have hax : Real.sqrt (Var[X; μ]) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr ((variance_nonneg X μ).lt_of_ne hXnd.symm)
  have hay : Real.sqrt (Var[Y; μ]) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr ((variance_nonneg Y μ).lt_of_ne hYnd.symm)
  rw [stddev_add_eq_iff_covariance_eq_sqrt hX hY, correlation,
    div_eq_one_iff_eq (mul_ne_zero hax hay)]

/-- **Equality boundary of the standard-deviation triangle inequality (perfect-positive-correlation
capstone).**  For non-degenerate `X, Y` the L² triangle inequality `σ[X+Y] ≤ σ[X] + σ[Y]` is an
equality *if and only if* `X` is almost everywhere an **increasing** affine function of `Y`:

        √Var[X + Y] = √Var[X] + √Var[Y]  ↔  ∃ a b, 0 < a ∧ X =ᵐ a·Y + b.

Chaining `stddev_add_eq_iff_correlation_eq_one` with `correlation_eq_one_iff_affine_pos`, this is
the sharp structural boundary of `stddev_add_le`: the standard deviations of a sum add *precisely*
in the perfectly-positively-correlated (fully-aligned) case, dual to
`variance_add_eq_iff_covariance_zero` — whose boundary is the orthogonal `cov = 0` case — at the
opposite endpoint of the Cauchy–Schwarz interval. -/
theorem stddev_add_eq_iff_affine_pos [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXnd : Var[X; μ] ≠ 0) (hYnd : Var[Y; μ] ≠ 0) :
    Real.sqrt (Var[X + Y; μ]) = Real.sqrt (Var[X; μ]) + Real.sqrt (Var[Y; μ]) ↔
      ∃ a b : ℝ, 0 < a ∧ X =ᵐ[μ] fun ω => a * Y ω + b := by
  rw [stddev_add_eq_iff_correlation_eq_one hX hY hXnd hYnd,
    correlation_eq_one_iff_affine_pos hX hY hXnd hYnd]

/-!
### Multivariate sharp equality boundary of the standard-deviation triangle inequality

The two-term equality boundary `stddev_add_eq_iff_covariance_eq_sqrt` pins down when
`σ[X+Y] = σ[X] + σ[Y]`.  The results below lift it to the *finite-family* triangle inequality
`stddev_sum_le` (`σ[∑Wᵢ] ≤ ∑σ[Wᵢ]`), identifying the exact condition under which the aggregate
standard deviation attains its ceiling.

The mechanism is uniform saturation of Cauchy–Schwarz.  Squaring the nonnegative identity
`σ[∑Wᵢ] = ∑σ[Wᵢ]` gives `Var[∑Wᵢ] = (∑σ[Wᵢ])²`; expanding the left side by the double-sum
`variance_sum'` and the right side by `Finset.sum_mul_sum` turns it into

    ∑ᵢ∑ⱼ cov[Wᵢ, Wⱼ]  =  ∑ᵢ∑ⱼ σ[Wᵢ]·σ[Wⱼ].

Every summand obeys the Cauchy–Schwarz bound `cov[Wᵢ, Wⱼ] ≤ σ[Wᵢ]·σ[Wⱼ]`
(`abs_covariance_le_sqrt`), so the two double sums are equal *iff every term is* — a sum of
nonnegative gaps vanishes iff each gap does (`Finset.sum_eq_sum_iff_of_le`).  Hence the aggregate
standard deviations add precisely when *all pairs* saturate Cauchy–Schwarz, i.e. are perfectly
positively correlated.  This is the multivariate dual, at the opposite Cauchy–Schwarz endpoint, of
the vanishing-off-diagonal boundary `variance_sum_eq_iff_offDiag_covariance_zero`.
-/

/-- **Multivariate equality boundary of the standard-deviation triangle inequality (covariance
form).**  For any finite family of square-integrable contributions the L² triangle inequality
`σ[∑ᵢ Wᵢ] ≤ ∑ᵢ σ[Wᵢ]` of `stddev_sum_le` is an *equality*

        √Var[∑ᵢ Wᵢ] = ∑ᵢ √Var[Wᵢ]

*if and only if* every ordered pair saturates the covariance Cauchy–Schwarz bound,
`cov[Wᵢ, Wⱼ] = √Var[Wᵢ]·√Var[Wⱼ]` for all `i, j ∈ s`.  No non-degeneracy hypothesis is needed
(the diagonal condition `i = j` reads `Var[Wᵢ] = Var[Wᵢ]` and the Cauchy–Schwarz gap is tight
there).  This is the finite-family lift of `stddev_add_eq_iff_covariance_eq_sqrt`, and the sharp
dual — at the perfectly-correlated endpoint of the Cauchy–Schwarz interval — of the
vanishing-off-diagonal boundary `variance_sum_eq_iff_offDiag_covariance_zero`. -/
theorem stddev_sum_eq_iff_pairwise_covariance_eq_sqrt [IsFiniteMeasure μ] {ι : Type*}
    {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ) :
    Real.sqrt (Var[∑ i ∈ s, W i; μ]) = ∑ i ∈ s, Real.sqrt (Var[W i; μ]) ↔
      ∀ i ∈ s, ∀ j ∈ s,
        cov[W i, W j; μ] = Real.sqrt (Var[W i; μ]) * Real.sqrt (Var[W j; μ]) := by
  classical
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, Real.sqrt (Var[W i; μ]) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  -- Termwise Cauchy–Schwarz: every covariance is dominated by the product of standard deviations.
  have hle_inner : ∀ i ∈ s, ∀ j ∈ s,
      cov[W i, W j; μ] ≤ Real.sqrt (Var[W i; μ]) * Real.sqrt (Var[W j; μ]) := by
    intro i hi j hj
    calc cov[W i, W j; μ] ≤ |cov[W i, W j; μ]| := le_abs_self _
      _ ≤ Real.sqrt (Var[W i; μ] * Var[W j; μ]) := abs_covariance_le_sqrt (hW i hi) (hW j hj)
      _ = Real.sqrt (Var[W i; μ]) * Real.sqrt (Var[W j; μ]) :=
          Real.sqrt_mul (variance_nonneg _ _) _
  have hle_outer : ∀ i ∈ s, (∑ j ∈ s, cov[W i, W j; μ])
      ≤ ∑ j ∈ s, Real.sqrt (Var[W i; μ]) * Real.sqrt (Var[W j; μ]) :=
    fun i hi => Finset.sum_le_sum (fun j hj => hle_inner i hi j hj)
  -- Reduce the (nonnegative) √-equality to the squared equality of the two double sums.
  rw [show (Real.sqrt (Var[∑ i ∈ s, W i; μ]) = ∑ i ∈ s, Real.sqrt (Var[W i; μ]))
        ↔ (Var[∑ i ∈ s, W i; μ] = (∑ i ∈ s, Real.sqrt (Var[W i; μ])) ^ 2) from
      ⟨fun h => by rw [← h, Real.sq_sqrt (variance_nonneg _ _)],
       fun h => by rw [h, Real.sqrt_sq hsum_nonneg]⟩,
    variance_sum' hW, pow_two, Finset.sum_mul_sum,
    Finset.sum_eq_sum_iff_of_le hle_outer]
  -- Sum-of-nonnegative-gaps: the outer equality reduces to per-pair saturation.
  constructor
  · intro h i hi j hj
    exact (Finset.sum_eq_sum_iff_of_le (fun j hj => hle_inner i hi j hj)).mp (h i hi) j hj
  · intro h i hi
    exact (Finset.sum_eq_sum_iff_of_le (fun j hj => hle_inner i hi j hj)).mpr
      (fun j hj => h i hi j hj)

/-- **Multivariate equality boundary of the standard-deviation triangle inequality (correlation
form).**  For a finite family of *non-degenerate* square-integrable contributions
(`Var[Wᵢ] ≠ 0` for all `i ∈ s`), the aggregate standard deviations add,

        √Var[∑ᵢ Wᵢ] = ∑ᵢ √Var[Wᵢ],

*if and only if* every pair is perfectly positively correlated, `ρ[Wᵢ, Wⱼ] = 1` for all
`i, j ∈ s`.  This normalises `stddev_sum_eq_iff_pairwise_covariance_eq_sqrt` through the definition
of the Pearson coefficient (each pair's covariance saturates Cauchy–Schwarz exactly when its
correlation hits `+1`); the multivariate capstone of `stddev_add_eq_iff_correlation_eq_one`. -/
theorem stddev_sum_eq_iff_pairwise_correlation_eq_one [IsFiniteMeasure μ] {ι : Type*}
    {W : ι → Ω → ℝ} {s : Finset ι} (hW : ∀ i ∈ s, MemLp (W i) 2 μ)
    (hnd : ∀ i ∈ s, Var[W i; μ] ≠ 0) :
    Real.sqrt (Var[∑ i ∈ s, W i; μ]) = ∑ i ∈ s, Real.sqrt (Var[W i; μ]) ↔
      ∀ i ∈ s, ∀ j ∈ s, correlation (W i) (W j) μ = 1 := by
  rw [stddev_sum_eq_iff_pairwise_covariance_eq_sqrt hW]
  have hden : ∀ i ∈ s, ∀ j ∈ s,
      Real.sqrt (Var[W i; μ]) * Real.sqrt (Var[W j; μ]) ≠ 0 := fun i hi j hj =>
    mul_ne_zero
      (Real.sqrt_ne_zero'.mpr ((variance_nonneg _ _).lt_of_ne (hnd i hi).symm))
      (Real.sqrt_ne_zero'.mpr ((variance_nonneg _ _).lt_of_ne (hnd j hj).symm))
  refine ⟨fun h i hi j hj => ?_, fun h i hi j hj => ?_⟩
  · rw [correlation, h i hi j hj, div_self (hden i hi j hj)]
  · have hcorr := h i hi j hj
    rw [correlation] at hcorr
    exact (div_eq_one_iff_eq (hden i hi j hj)).mp hcorr

end ShannonAWGNMultiSymbolPower
