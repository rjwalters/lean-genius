/-
  AWGN Channel Capacity:  C = ½ log(1 + P/N)

  Open question (shannon-channel-coding-oq-01):
  "Compute capacities for concrete channels such as BSC, BEC, and AWGN beyond
   placeholder True statements."

  Status of the three named channels:
  - BSC(p) capacity = log 2 - h(p)        proved axiom-free in ShannonChannelCodingOQ02
  - BEC(p) capacity = (1-p)·log 2          proved axiom-free in ShannonChannelCodingBEC
  - AWGN     capacity = ½ log(1 + P/N)     this file

  The additive white Gaussian noise (AWGN) channel sends Y = X + Z where the
  noise Z ~ N(0, N) is independent of the input X, and the input is constrained
  to have average power E[X²] ≤ P. Its capacity is the classical Shannon formula

        C(P, N) = ½ · log(1 + P/N).

  Derivation.  For a continuous channel the mutual information decomposes as
  I(X;Y) = h(Y) - h(Y | X) = h(Y) - h(Z), because the noise is additive and
  independent. Two facts about the *differential entropy* h(·) drive the result,
  and both are already proved axiom-free in `ShannonEntropyOQ01`:

    1. `gaussianDifferentialEntropy` :  h(N(μ, σ²)) = ½ log(2πe σ²).
    2. `gaussian_max_entropy`        :  among all densities with variance ≤ σ²,
                                        the Gaussian maximises differential entropy.

  With a Gaussian input of power P the output Y is Gaussian with variance P + N,
  so h(Y) = ½ log(2πe (P + N)) and h(Z) = ½ log(2πe N), giving

        I = ½ log(2πe (P+N)) - ½ log(2πe N) = ½ log((P+N)/N) = ½ log(1 + P/N),

  and no input of power ≤ P can do better because the output variance is then
  ≤ P + N and the Gaussian maximises h(Y) (fact 2). This file formalises that
  *entropy-difference assembly* axiom-free: the capacity value, its achievability
  by a Gaussian input, the converse bound from the max-entropy theorem, and the
  basic monotonicity properties of C(P, N).

  Scope note. What remains open is the full continuous-alphabet mutual-information
  layer — defining I(X;Y) measure-theoretically for the additive channel and
  proving the chain-rule identity I(X;Y) = h(Y) - h(Z). Here both differential
  entropies are taken as the grounded quantities of `ShannonEntropyOQ01`, and the
  capacity is assembled from them; the input/output power relation E[Y²] = P + N
  for an independent additive noise is the standard variance-of-a-sum fact and is
  exposed as the hypothesis `hvar` of the converse bound.
-/

import Mathlib
import Proofs.ShannonEntropyOQ01

namespace ShannonAWGN

open DifferentialEntropy Real

/-- AWGN channel capacity as a function of signal power `P` and noise power `N`:
    `C(P, N) = ½ log(1 + P/N)`. -/
noncomputable def awgnCapacity (P N : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + P / N)

/-! ## The entropy-difference identity -/

/-- The algebraic core of the AWGN capacity: the difference of the
    capacity-achieving output entropy and the noise entropy collapses to the
    Shannon formula.  `½ log(2πe (P+N)) - ½ log(2πe N) = ½ log(1 + P/N)`. -/
theorem awgn_log_identity {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (P + N)) -
      (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * N) =
    (1 / 2) * Real.log (1 + P / N) := by
  have hPN : 0 < P + N := by linarith
  have hc : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have hxpos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (P + N) := mul_pos hc hPN
  have hypos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * N := mul_pos hc hN
  have key : 2 * Real.pi * Real.exp 1 * (P + N) / (2 * Real.pi * Real.exp 1 * N)
      = 1 + P / N := by
    field_simp [hN.ne', hc.ne']
    ring
  rw [← mul_sub, ← Real.log_div hxpos.ne' hypos.ne', key]

/-! ## Grounding the two differential entropies -/

/-- The differential entropy of the Gaussian noise `Z ~ N(0, N)` is
    `½ log(2πe N)`, instantiating `gaussianDifferentialEntropy` at `σ = √N`. -/
theorem awgn_noise_entropy {N : ℝ} (hN : 0 < N) :
    differentialEntropy (gaussianPDF 0 (Real.sqrt N)) =
    (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * N) := by
  have h := gaussianDifferentialEntropy 0 (Real.sqrt_pos.mpr hN)
  rwa [Real.sq_sqrt hN.le] at h

/-- The differential entropy of the capacity-achieving Gaussian output
    `Y ~ N(0, P + N)` is `½ log(2πe (P + N))`. -/
theorem awgn_output_entropy {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    differentialEntropy (gaussianPDF 0 (Real.sqrt (P + N))) =
    (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (P + N)) := by
  have hPN : 0 < P + N := by linarith
  have h := gaussianDifferentialEntropy 0 (Real.sqrt_pos.mpr hPN)
  rwa [Real.sq_sqrt hPN.le] at h

/-! ## Capacity: achievability and converse -/

/-- **Achievability.**  A Gaussian input of power `P` produces a Gaussian output
    of power `P + N`, whose entropy minus the noise entropy is exactly the
    capacity `½ log(1 + P/N)`.  This realises the AWGN capacity value from the
    two grounded differential entropies. -/
theorem awgn_capacity_achieved {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    differentialEntropy (gaussianPDF 0 (Real.sqrt (P + N))) -
      differentialEntropy (gaussianPDF 0 (Real.sqrt N)) = awgnCapacity P N := by
  unfold awgnCapacity
  rw [awgn_output_entropy hP hN, awgn_noise_entropy hN, awgn_log_identity hP hN]

/-- **Converse.**  No output density `f` whose variance is bounded by the output
    power `P + N` can beat the capacity: `h(f) - h(Z) ≤ ½ log(1 + P/N)`.
    This is the Gaussian max-entropy theorem applied at `σ = √(P+N)`, with the
    noise entropy `h(Z) = ½ log(2πe N)` subtracted.  The hypothesis `hvar`
    encodes the average-power constraint `E[Y²] ≤ P + N`. -/
theorem awgn_capacity_upper_bound {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (f : ℝ → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf_sum : ∫ x, f x = 1)
    (hvar : ∫ x, x ^ 2 * f x ≤ P + N)
    (hf_int : Integrable f)
    (hflog_f_int : Integrable (fun x => f x * Real.log (f x)))
    (hflog_g_int :
      Integrable (fun x => f x * Real.log (gaussianPDF 0 (Real.sqrt (P + N)) x)))
    (hfg_int :
      Integrable (fun x => f x * Real.log (f x / gaussianPDF 0 (Real.sqrt (P + N)) x))) :
    differentialEntropy f - differentialEntropy (gaussianPDF 0 (Real.sqrt N)) ≤
      awgnCapacity P N := by
  have hPN : 0 < P + N := by linarith
  have hσ : 0 < Real.sqrt (P + N) := Real.sqrt_pos.mpr hPN
  have hvar' : ∫ x, x ^ 2 * f x ≤ (Real.sqrt (P + N)) ^ 2 := by
    rwa [Real.sq_sqrt hPN.le]
  have hmax := gaussian_max_entropy hσ f hf_nn hf_sum hvar' hf_int hflog_f_int
    hflog_g_int hfg_int
  rw [Real.sq_sqrt hPN.le] at hmax
  have hcap := awgn_log_identity hP hN
  rw [awgn_noise_entropy hN]
  unfold awgnCapacity
  linarith [hmax, hcap]

/-! ## Structural properties of the capacity formula -/

/-- The AWGN capacity is non-negative for any non-negative signal power. -/
theorem awgn_capacity_nonneg {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    0 ≤ awgnCapacity P N := by
  unfold awgnCapacity
  have hd : 0 ≤ P / N := div_nonneg hP hN.le
  have h1 : (1 : ℝ) ≤ 1 + P / N := by linarith
  have := Real.log_nonneg h1
  linarith

/-- With no signal power the capacity vanishes: `C(0, N) = 0`. -/
theorem awgn_capacity_zero_power {N : ℝ} (hN : 0 < N) :
    awgnCapacity 0 N = 0 := by
  unfold awgnCapacity
  simp

/-- The capacity is strictly positive whenever there is signal power. -/
theorem awgn_capacity_pos {P N : ℝ} (hP : 0 < P) (hN : 0 < N) :
    0 < awgnCapacity P N := by
  unfold awgnCapacity
  have hd : 0 < P / N := div_pos hP hN
  have h1 : (1 : ℝ) < 1 + P / N := by linarith
  have := Real.log_pos h1
  linarith

/-- The capacity is monotone increasing in the signal power. -/
theorem awgn_capacity_mono_power {P₁ P₂ N : ℝ} (hN : 0 < N) (hP₁ : 0 ≤ P₁)
    (h : P₁ ≤ P₂) : awgnCapacity P₁ N ≤ awgnCapacity P₂ N := by
  unfold awgnCapacity
  have hd : 0 ≤ P₁ / N := div_nonneg hP₁ hN.le
  have hpos : (0 : ℝ) < 1 + P₁ / N := by linarith
  have hdiv : P₁ / N ≤ P₂ / N := by
    have h0 : (0 : ℝ) ≤ (P₂ - P₁) / N := div_nonneg (by linarith) hN.le
    have he : (P₂ - P₁) / N = P₂ / N - P₁ / N := by ring
    linarith [he ▸ h0]
  have hle : 1 + P₁ / N ≤ 1 + P₂ / N := by linarith
  have := Real.log_le_log hpos hle
  linarith

/-- The capacity is decreasing in the noise power: more noise, less capacity. -/
theorem awgn_capacity_antitone_noise {P N₁ N₂ : ℝ} (hP : 0 ≤ P) (hN₁ : 0 < N₁)
    (h : N₁ ≤ N₂) : awgnCapacity P N₂ ≤ awgnCapacity P N₁ := by
  unfold awgnCapacity
  have hN₂ : 0 < N₂ := lt_of_lt_of_le hN₁ h
  have hd₂ : 0 ≤ P / N₂ := div_nonneg hP hN₂.le
  have hpos : (0 : ℝ) < 1 + P / N₂ := by linarith
  have hden : (0 : ℝ) ≤ N₁ * N₂ := mul_nonneg hN₁.le hN₂.le
  have hdiv : P / N₂ ≤ P / N₁ := by
    have h0 : (0 : ℝ) ≤ P * (N₂ - N₁) / (N₁ * N₂) :=
      div_nonneg (mul_nonneg hP (by linarith)) hden
    have he : P * (N₂ - N₁) / (N₁ * N₂) = P / N₁ - P / N₂ := by
      field_simp [hN₁.ne', hN₂.ne']
      ring
    linarith [he ▸ h0]
  have hle : 1 + P / N₂ ≤ 1 + P / N₁ := by linarith
  have := Real.log_le_log hpos hle
  linarith

end ShannonAWGN
