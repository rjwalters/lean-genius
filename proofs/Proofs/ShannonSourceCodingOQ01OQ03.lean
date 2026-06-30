import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-!
# The Binary Rate–Distortion Function `R(D) = H(p) − H(D)` (oq-01-oq-03)

The parent entry `shannon-source-coding-oq-01` (Rate–Distortion Theory) records the
binary rate–distortion function only as a comment: for a Bernoulli(`p`) source under
Hamming distortion,

    R(D) = h(p) − h(D),   for 0 ≤ D ≤ min(p, 1−p),

where `h` is the binary entropy function. Its listed open question #3 asks whether
Lean can formalize this explicit formula and connect it to the abstract
`rateDistortionFn`. This file gives the formula a concrete, fully verified object and
proves its defining structural properties, built directly on Mathlib's
`Real.binEntropy`.

We work in the regime `0 ≤ D ≤ p ≤ 1/2` (so `min(p, 1−p) = p`); the case `p ≥ 1/2`
follows by the symmetry `binEntropy (1 − p) = binEntropy p`. Entropy is measured in
nats (Mathlib's `binEntropy` uses the natural logarithm); the formula `R = h(p) − h(D)`
is base-independent.

## What is proved (0 `sorry`, 0 `axiom`)

* `rateDistortion_zero` — `R(p, 0) = H(p)`: lossless coding requires the full source
  entropy rate.
* `rateDistortion_self` — `R(p, p) = 0`: at distortion equal to the source bias the
  required rate drops to zero.
* `rateDistortion_nonneg` — `R(p, D) ≥ 0` on `0 ≤ D ≤ p ≤ 1/2` (a rate is nonnegative).
* `rateDistortion_antitone_in_D` — `R(p, ·)` is decreasing in `D`: more allowed
  distortion needs less rate.
* `rateDistortion_le_binEntropy` / `rateDistortion_le_log_two` — `R(p, D) ≤ H(p) ≤ log 2`
  (the rate never exceeds the source entropy, itself at most one bit).

These convert the commented formula into a verified function with exactly the
endpoint, sign, monotonicity, and boundedness behaviour the rate–distortion curve
must have.
-/

namespace ShannonSourceCodingOQ01OQ03

open Real

/-- The binary rate–distortion function for a Bernoulli(`p`) source under Hamming
distortion: `R(p, D) = H(p) − H(D)`, with `H` the binary entropy (`Real.binEntropy`). -/
noncomputable def rateDistortion (p D : ℝ) : ℝ := binEntropy p - binEntropy D

/-- **No distortion ⇒ full entropy rate.** `R(p, 0) = H(p)`. -/
theorem rateDistortion_zero (p : ℝ) : rateDistortion p 0 = binEntropy p := by
  simp [rateDistortion]

/-- **Distortion at the source bias ⇒ zero rate.** `R(p, p) = 0`. -/
theorem rateDistortion_self (p : ℝ) : rateDistortion p p = 0 := by
  simp [rateDistortion]

/-- **A rate is nonnegative.** On `0 ≤ D ≤ p ≤ 1/2` the binary entropy is increasing,
so `H(D) ≤ H(p)` and `R(p, D) = H(p) − H(D) ≥ 0`. -/
theorem rateDistortion_nonneg {p D : ℝ} (hD0 : 0 ≤ D) (hDp : D ≤ p) (hp : p ≤ 2⁻¹) :
    0 ≤ rateDistortion p D := by
  have hmono := binEntropy_strictMonoOn.monotoneOn
  have hDmem : D ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨hD0, le_trans hDp hp⟩
  have hpmem : p ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨le_trans hD0 hDp, hp⟩
  have hle : binEntropy D ≤ binEntropy p := hmono hDmem hpmem hDp
  simp only [rateDistortion]; linarith

/-- **More distortion needs less rate.** `R(p, ·)` is decreasing in `D` on `[0, p]`
(with `p ≤ 1/2`), since the binary entropy is increasing there. -/
theorem rateDistortion_antitone_in_D {p D₁ D₂ : ℝ} (h0 : 0 ≤ D₁) (h12 : D₁ ≤ D₂)
    (h2p : D₂ ≤ p) (hp : p ≤ 2⁻¹) :
    rateDistortion p D₂ ≤ rateDistortion p D₁ := by
  have hmono := binEntropy_strictMonoOn.monotoneOn
  have hD1 : D₁ ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨h0, le_trans (le_trans h12 h2p) hp⟩
  have hD2 : D₂ ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨le_trans h0 h12, le_trans h2p hp⟩
  have hle : binEntropy D₁ ≤ binEntropy D₂ := hmono hD1 hD2 h12
  simp only [rateDistortion]; linarith

/-- **The rate never exceeds the source entropy.** `R(p, D) ≤ H(p)` for any valid
distortion `0 ≤ D ≤ 1`, since `H(D) ≥ 0`. -/
theorem rateDistortion_le_binEntropy {p D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    rateDistortion p D ≤ binEntropy p := by
  have hHD : 0 ≤ binEntropy D := binEntropy_nonneg hD0 hD1
  simp only [rateDistortion]; linarith

/-- **The binary rate is at most one bit (`log 2` nats).** -/
theorem rateDistortion_le_log_two {p D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    rateDistortion p D ≤ log 2 :=
  le_trans (rateDistortion_le_binEntropy hD0 hD1) binEntropy_le_log_two

end ShannonSourceCodingOQ01OQ03
