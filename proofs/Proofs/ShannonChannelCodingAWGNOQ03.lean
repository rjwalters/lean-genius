/-
  The Bandlimited Shannon–Hartley Capacity:  C = B · log₂(1 + P/N)  bits/s

  Open question (shannon-channel-coding-awgn-oq-03):
  "Extend to the bandlimited Shannon–Hartley form C = B log₂(1 + P/N) bits/s
   and to parallel Gaussian channels via water-filling (the capacity of a
   vector AWGN channel)."

  ## What this file does

  The companion file `ShannonChannelCodingAWGN` proves, axiom-free, that the
  capacity of a single use of the additive white Gaussian noise channel is

        awgnCapacity P N = ½ · log(1 + P/N)           [nats per channel use]

  where `log` is the natural logarithm and `P`, `N` are the signal and noise
  powers.  This file turns that *per-use, nats* quantity into the classical
  *bandlimited, bits-per-second* Shannon–Hartley formula

        C(B, P, N) = B · log₂(1 + P/N)               [bits per second].

  ## The bridge: Nyquist sampling + a change of logarithm base

  Two textbook conversions assemble the bits/second formula from the per-use
  nats formula, and both are exact algebraic identities:

  1. **Change of base (nats → bits).**  One nat is `1 / log 2` bits, so the
     per-use capacity in bits is
            awgnCapacity P N / log 2 = ½ · log₂(1 + P/N)   [bits per use].

  2. **Nyquist rate (uses → seconds).**  A strictly bandlimited channel of
     bandwidth `B` Hz supports `2B` independent (orthogonal) signalling
     dimensions per second.  Multiplying the per-use bit capacity by `2B`:
            C = 2B · ½ · log₂(1 + P/N) = B · log₂(1 + P/N)  [bits per second].

  Combining the two gives the single bridge identity proved below,
  `shannonHartley_eq_awgn`:

        C(B, P, N) = (2B / log 2) · awgnCapacity P N.

  Everything downstream — non-negativity, the power/bandwidth monotonicities,
  the vanishing of capacity at zero power or zero bandwidth, and the low-SNR
  linear upper bound `log₂(1+x) ≤ x / log 2` — is then a structural consequence
  of the corresponding fact about `Real.logb 2`.

  ## Scope note

  This file formalises the *bandlimited scalar* Shannon–Hartley form exactly.
  The second half of the open question — the capacity of a *vector* (parallel)
  Gaussian channel via water-filling, `C = Σᵢ ½ log(1 + Pᵢ/Nᵢ)` with
  `Σ Pᵢ ≤ P` optimised by the water-filling power allocation — is a genuinely
  separate optimisation problem and is left open here.  The per-use AWGN
  capacity it builds on is exactly the `awgnCapacity` re-exported below.
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGN

namespace ShannonHartley

open Real ShannonAWGN

/-- The **bandlimited Shannon–Hartley capacity** of an AWGN channel of
    bandwidth `B` (Hz), signal power `P`, and noise power `N`, measured in
    bits per second:  `C(B, P, N) = B · log₂(1 + P/N)`. -/
noncomputable def shannonHartleyCapacity (B P N : ℝ) : ℝ :=
  B * Real.logb 2 (1 + P / N)

/-! ## The bridge to the per-use AWGN capacity -/

/-- **Bridge identity.**  The bits-per-second Shannon–Hartley capacity is the
    per-use AWGN capacity (in nats) rescaled by the Nyquist factor `2B` and the
    nats→bits change of base `1 / log 2`:

        `C(B, P, N) = (2B / log 2) · awgnCapacity P N`.

    This is the precise content of "Nyquist sampling + change of logarithm
    base": `awgnCapacity P N = ½ log(1 + P/N)` and `log₂ x = log x / log 2`. -/
theorem shannonHartley_eq_awgn (B P N : ℝ) :
    shannonHartleyCapacity B P N = (2 * B / Real.log 2) * awgnCapacity P N := by
  unfold shannonHartleyCapacity awgnCapacity
  rw [Real.logb]
  ring

/-- **Nyquist assembly.**  The capacity is `2B` times the per-use capacity in
    bits, `½ log₂(1 + P/N)`.  This exposes the "`2B` independent uses per
    second" reading directly. -/
theorem shannonHartley_eq_two_B_bits_per_use (B P N : ℝ) :
    shannonHartleyCapacity B P N =
      2 * B * ((1 / 2) * Real.logb 2 (1 + P / N)) := by
  unfold shannonHartleyCapacity
  ring

/-! ## Structural properties of the bandlimited capacity formula -/

/-- The capacity is non-negative for any non-negative bandwidth and signal
    power (with positive noise). -/
theorem shannonHartley_nonneg {B P N : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hN : 0 < N) : 0 ≤ shannonHartleyCapacity B P N := by
  unfold shannonHartleyCapacity
  have hd : 0 ≤ P / N := div_nonneg hP hN.le
  have h1 : (1 : ℝ) ≤ 1 + P / N := by linarith
  have hlog : 0 ≤ Real.logb 2 (1 + P / N) :=
    Real.logb_nonneg (by norm_num) h1
  exact mul_nonneg hB hlog

/-- With no signal power the capacity vanishes: `C(B, 0, N) = 0`. -/
theorem shannonHartley_zero_power {B N : ℝ} :
    shannonHartleyCapacity B 0 N = 0 := by
  unfold shannonHartleyCapacity
  simp

/-- With no bandwidth there is no capacity: `C(0, P, N) = 0`. -/
theorem shannonHartley_zero_bandwidth {P N : ℝ} :
    shannonHartleyCapacity 0 P N = 0 := by
  unfold shannonHartleyCapacity
  simp

/-- The capacity is strictly positive whenever there is bandwidth, signal
    power, and noise. -/
theorem shannonHartley_pos {B P N : ℝ} (hB : 0 < B) (hP : 0 < P) (hN : 0 < N) :
    0 < shannonHartleyCapacity B P N := by
  unfold shannonHartleyCapacity
  have hd : 0 < P / N := div_pos hP hN
  have h1 : (1 : ℝ) < 1 + P / N := by linarith
  have hlog : 0 < Real.logb 2 (1 + P / N) :=
    Real.logb_pos (by norm_num) h1
  exact mul_pos hB hlog

/-- The capacity is monotone increasing in the bandwidth. -/
theorem shannonHartley_mono_bandwidth {B₁ B₂ P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (h : B₁ ≤ B₂) :
    shannonHartleyCapacity B₁ P N ≤ shannonHartleyCapacity B₂ P N := by
  unfold shannonHartleyCapacity
  have hd : 0 ≤ P / N := div_nonneg hP hN.le
  have h1 : (1 : ℝ) ≤ 1 + P / N := by linarith
  have hlog : 0 ≤ Real.logb 2 (1 + P / N) :=
    Real.logb_nonneg (by norm_num) h1
  exact mul_le_mul_of_nonneg_right h hlog

/-- The capacity is strictly increasing in the bandwidth (given signal and
    noise power). -/
theorem shannonHartley_strictMono_bandwidth {B₁ B₂ P N : ℝ} (hP : 0 < P)
    (hN : 0 < N) (h : B₁ < B₂) :
    shannonHartleyCapacity B₁ P N < shannonHartleyCapacity B₂ P N := by
  unfold shannonHartleyCapacity
  have hd : 0 < P / N := div_pos hP hN
  have h1 : (1 : ℝ) < 1 + P / N := by linarith
  have hlog : 0 < Real.logb 2 (1 + P / N) :=
    Real.logb_pos (by norm_num) h1
  exact mul_lt_mul_of_pos_right h hlog

/-- The capacity is monotone increasing in the signal power. -/
theorem shannonHartley_mono_power {B P₁ P₂ N : ℝ} (hB : 0 ≤ B) (hN : 0 < N)
    (hP₁ : 0 ≤ P₁) (h : P₁ ≤ P₂) :
    shannonHartleyCapacity B P₁ N ≤ shannonHartleyCapacity B P₂ N := by
  unfold shannonHartleyCapacity
  have hpos : (0 : ℝ) < 1 + P₁ / N := by
    have : 0 ≤ P₁ / N := div_nonneg hP₁ hN.le
    linarith
  have hdiv : P₁ / N ≤ P₂ / N := by
    have h0 : (0 : ℝ) ≤ (P₂ - P₁) / N := div_nonneg (by linarith) hN.le
    have he : (P₂ - P₁) / N = P₂ / N - P₁ / N := by ring
    linarith [he ▸ h0]
  have hle : 1 + P₁ / N ≤ 1 + P₂ / N := by linarith
  have hlog : Real.logb 2 (1 + P₁ / N) ≤ Real.logb 2 (1 + P₂ / N) :=
    Real.logb_le_logb_of_le (by norm_num) hpos hle
  exact mul_le_mul_of_nonneg_left hlog hB

/-- The capacity is decreasing in the noise power: more noise, less capacity. -/
theorem shannonHartley_antitone_noise {B P N₁ N₂ : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hN₁ : 0 < N₁) (h : N₁ ≤ N₂) :
    shannonHartleyCapacity B P N₂ ≤ shannonHartleyCapacity B P N₁ := by
  unfold shannonHartleyCapacity
  have hN₂ : 0 < N₂ := lt_of_lt_of_le hN₁ h
  have hpos : (0 : ℝ) < 1 + P / N₂ := by
    have : 0 ≤ P / N₂ := div_nonneg hP hN₂.le
    linarith
  have hdiv : P / N₂ ≤ P / N₁ := by
    have hden : (0 : ℝ) ≤ N₁ * N₂ := mul_nonneg hN₁.le hN₂.le
    have h0 : (0 : ℝ) ≤ P * (N₂ - N₁) / (N₁ * N₂) :=
      div_nonneg (mul_nonneg hP (by linarith)) hden
    have he : P * (N₂ - N₁) / (N₁ * N₂) = P / N₁ - P / N₂ := by
      rw [div_sub_div _ _ hN₁.ne' hN₂.ne']
      ring
    linarith [he ▸ h0]
  have hle : 1 + P / N₂ ≤ 1 + P / N₁ := by linarith
  have hlog : Real.logb 2 (1 + P / N₂) ≤ Real.logb 2 (1 + P / N₁) :=
    Real.logb_le_logb_of_le (by norm_num) hpos hle
  exact mul_le_mul_of_nonneg_left hlog hB

/-! ## The low-SNR / wideband linear bound -/

/-- **Linear (low-SNR) upper bound.**  Since `log(1 + x) ≤ x`, the capacity is
    bounded by the bandwidth-scaled signal-to-noise ratio divided by `log 2`:

        `C(B, P, N) ≤ B · (P/N) / log 2`.

    This is the precise form behind the wideband statement that capacity grows
    at most linearly in SNR; equality is approached as `P/N → 0`. -/
theorem shannonHartley_le_snr_linear {B P N : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hN : 0 < N) :
    shannonHartleyCapacity B P N ≤ B * (P / N) / Real.log 2 := by
  unfold shannonHartleyCapacity
  have hd : 0 ≤ P / N := div_nonneg hP hN.le
  have hxpos : (0 : ℝ) < 1 + P / N := by linarith
  -- log(1 + P/N) ≤ P/N
  have hlog_le : Real.log (1 + P / N) ≤ P / N := by
    have := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- logb 2 (1 + P/N) = log(1 + P/N) / log 2 ≤ (P/N) / log 2
  have hlogb_le : Real.logb 2 (1 + P / N) ≤ (P / N) / Real.log 2 := by
    rw [Real.logb, div_le_div_iff_of_pos_right hlog2]
    exact hlog_le
  calc B * Real.logb 2 (1 + P / N)
      ≤ B * ((P / N) / Real.log 2) := mul_le_mul_of_nonneg_left hlogb_le hB
    _ = B * (P / N) / Real.log 2 := by ring

/-! ## Toward the vector channel: the parallel (multi-band) capacity

    The bandlimited scalar formula above extends to a *bank* of `n` independent
    Gaussian sub-channels — the discrete model of a frequency-selective (or
    parallel-band) channel.  Splitting the spectrum into `n` narrowband slots
    with signal powers `P i` and noise powers `N i`, the total capacity is the
    *sum* of the per-band per-use capacities

          Cᵥ(P, N) = Σᵢ awgnCapacity (Pᵢ, Nᵢ) = Σᵢ ½ log(1 + Pᵢ/Nᵢ)   [nats/use].

    The water-filling *optimisation* — maximising this sum over the allocation
    `P` subject to a total power budget `Σᵢ Pᵢ ≤ P` — is the genuinely separate
    problem left open by this entry.  What follows is the additive capacity
    object that water-filling optimises, together with its structural
    (non-negativity / monotonicity) properties, each inherited term-by-term
    from the scalar `awgnCapacity`. -/

/-- The **sum capacity of a parallel (vector) AWGN channel**: `n` independent
    Gaussian sub-channels with signal powers `P i` and noise powers `N i` have
    total per-use capacity `Σᵢ awgnCapacity (P i) (N i) = Σᵢ ½ log(1 + Pᵢ/Nᵢ)`
    nats. -/
noncomputable def parallelAwgnCapacity {n : ℕ} (P N : Fin n → ℝ) : ℝ :=
  ∑ i, awgnCapacity (P i) (N i)

/-- The vector capacity written out explicitly as the sum of Shannon terms. -/
theorem parallelAwgnCapacity_eq_sum {n : ℕ} (P N : Fin n → ℝ) :
    parallelAwgnCapacity P N = ∑ i, (1 / 2) * Real.log (1 + P i / N i) :=
  rfl

/-- For a single sub-channel (`n = 1`) the vector capacity reduces to the
    scalar per-use AWGN capacity. -/
theorem parallelAwgnCapacity_one (P N : Fin 1 → ℝ) :
    parallelAwgnCapacity P N = awgnCapacity (P 0) (N 0) := by
  unfold parallelAwgnCapacity
  rw [Fin.sum_univ_one]

/-- The vector capacity is non-negative when every sub-channel has
    non-negative signal power and positive noise power. -/
theorem parallelAwgnCapacity_nonneg {n : ℕ} {P N : Fin n → ℝ}
    (hP : ∀ i, 0 ≤ P i) (hN : ∀ i, 0 < N i) :
    0 ≤ parallelAwgnCapacity P N := by
  unfold parallelAwgnCapacity
  exact Finset.sum_nonneg (fun i _ => awgn_capacity_nonneg (hP i) (hN i))

/-- The vector capacity is monotone increasing in the signal-power allocation:
    raising every sub-channel's power (weakly) cannot decrease total capacity.
    This is the monotonicity against which a water-filling power budget is
    spent. -/
theorem parallelAwgnCapacity_mono_power {n : ℕ} {P₁ P₂ N : Fin n → ℝ}
    (hN : ∀ i, 0 < N i) (hP₁ : ∀ i, 0 ≤ P₁ i) (h : ∀ i, P₁ i ≤ P₂ i) :
    parallelAwgnCapacity P₁ N ≤ parallelAwgnCapacity P₂ N := by
  unfold parallelAwgnCapacity
  exact Finset.sum_le_sum
    (fun i _ => awgn_capacity_mono_power (hN i) (hP₁ i) (h i))

/-- The vector capacity is decreasing in the noise allocation: more noise in
    any sub-channel (weakly) lowers the total capacity. -/
theorem parallelAwgnCapacity_antitone_noise {n : ℕ} {P N₁ N₂ : Fin n → ℝ}
    (hP : ∀ i, 0 ≤ P i) (hN₁ : ∀ i, 0 < N₁ i) (h : ∀ i, N₁ i ≤ N₂ i) :
    parallelAwgnCapacity P N₂ ≤ parallelAwgnCapacity P N₁ := by
  unfold parallelAwgnCapacity
  exact Finset.sum_le_sum
    (fun i _ => awgn_capacity_antitone_noise (hP i) (hN₁ i) (h i))

end ShannonHartley
