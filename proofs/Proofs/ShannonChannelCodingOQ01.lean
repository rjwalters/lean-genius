/-
  AWGN operational layer:  the additive-channel mutual-information decomposition
  I(X;Y) = h(Y) - h(Z)

  Open question (shannon-channel-coding-oq-01):
  "Compute capacities for concrete channels such as BSC, BEC, and AWGN beyond
   placeholder True statements."

  The three named-channel capacity VALUES are already proved axiom-free:
  - BSC(p)  = log 2 - h(p)        ShannonChannelCodingOQ02
  - BEC(p)  = (1-p)·log 2          ShannonChannelCodingBEC
  - AWGN    = ½ log(1 + P/N)      ShannonChannelCodingAWGN

  For the AWGN channel that last value is assembled in `ShannonChannelCodingAWGN`
  from the entropy difference h(Y) - h(Z) of the proven Gaussian differential
  entropies. That file's scope note flagged ONE step as described in prose only:

      "the chain-rule identity I(X;Y) = h(Y) - h(Z)" for the additive channel.

  This file formalises the measure-theoretic core of that step.  For an additive
  channel Y = X + Z with noise Z independent of the input, the output density
  conditioned on the input value `x` is the noise density *shifted by x*,
  `y ↦ fZ (y - x)`.  The decisive fact is that the differential entropy is
  *translation invariant* — shifting a density does not change `h` — so the
  conditional output entropy h(Y | X = x) equals h(Z) for every input value `x`,
  and therefore the averaged conditional entropy h(Y | X) = h(Z) as well.  With
  the chain rule I(X;Y) = h(Y) - h(Y | X) this gives the decomposition
  I(X;Y) = h(Y) - h(Z) that the AWGN capacity rests on.

  What is proved here, axiom-free:
  - `differentialEntropy_translation`   : h(f(· - c)) = h(f)   (translation invariance)
  - `additiveOutputDensity`             : the shifted-noise output density
  - `additive_conditional_entropy_eq`   : h(Y | X = x) = h(Z) for every input x
  - `gaussian_conditional_entropy_eq`   : the AWGN instance, h(Y | X = x) = ½log(2πeN)
  - `additive_averaged_conditional_entropy` : averaging over the input law, h(Y|X)=h(Z)
  - `additive_mutual_information_decomposition` : I(X;Y) = h(Y) - h(Z), where the
        mutual information of the additive channel is taken as h(Y) - h(Y | X)

  Scope note.  As in the parent file the two differential entropies h(Y), h(Z) and
  the X-averaged conditional entropy are the grounded quantities; what remains
  genuinely open is to prove that the information-theoretic mutual information,
  defined as the KL divergence between the joint output–input law and the product
  of its marginals, coincides with this entropy difference h(Y) - h(Y | X).  Here
  that chain-rule form of I is taken as the definition (`additiveMutualInformation`)
  and the translation-invariance core that makes h(Y | X) collapse to h(Z) is
  proved outright.
-/

import Mathlib
import Proofs.ShannonEntropyOQ01

namespace ShannonAWGNOperational

open DifferentialEntropy Real MeasureTheory

/-! ## Translation invariance of differential entropy -/

/-- **Translation invariance of differential entropy.**  Shifting a density by a
    constant `c` leaves its differential entropy unchanged:
    `h(f(· - c)) = h(f)`.  This is the change-of-variables `u = y - c` under the
    translation-invariant Lebesgue measure, and it is the reason the conditional
    output entropy of an additive channel does not depend on the input value. -/
theorem differentialEntropy_translation (f : ℝ → ℝ) (c : ℝ) :
    differentialEntropy (fun y => f (y - c)) = differentialEntropy f := by
  unfold differentialEntropy
  congr 1
  exact integral_sub_right_eq_self (fun x => f x * Real.log (f x)) c

/-! ## The additive channel -/

/-- Output density of an additive channel `Y = X + Z` conditioned on the input
    value `x`: the noise density `fZ` shifted so that its mean moves to `x`,
    `y ↦ fZ (y - x)`.  (If `Z` has mean `0` then `Y | X = x` has mean `x`.) -/
noncomputable def additiveOutputDensity (fZ : ℝ → ℝ) (x : ℝ) : ℝ → ℝ :=
  fun y => fZ (y - x)

/-- **Conditional output entropy of an additive channel.**  For every input value
    `x`, the differential entropy of the (shifted) output density equals the noise
    entropy: `h(Y | X = x) = h(Z)`.  Immediate from translation invariance. -/
theorem additive_conditional_entropy_eq (fZ : ℝ → ℝ) (x : ℝ) :
    differentialEntropy (additiveOutputDensity fZ x) = differentialEntropy fZ := by
  unfold additiveOutputDensity
  exact differentialEntropy_translation fZ x

/-- The AWGN instance: with Gaussian noise `Z ~ N(0, N)` the conditional output
    entropy `h(Y | X = x)` equals the noise entropy `½ log(2πe N)` for every input
    `x`.  Combines `additive_conditional_entropy_eq` with the Gaussian entropy of
    `ShannonChannelCodingAWGN`/`ShannonEntropyOQ01`. -/
theorem gaussian_conditional_entropy_eq {N : ℝ} (hN : 0 < N) (x : ℝ) :
    differentialEntropy (additiveOutputDensity (gaussianPDF 0 (Real.sqrt N)) x) =
      (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * N) := by
  rw [additive_conditional_entropy_eq]
  have h := gaussianDifferentialEntropy 0 (Real.sqrt_pos.mpr hN)
  rwa [Real.sq_sqrt hN.le] at h

/-! ## Averaging over the input law -/

/-- **Averaged conditional entropy.**  Averaging the per-input conditional output
    entropy `h(Y | X = x)` over any input probability density `fX` (with
    `∫ fX = 1`) gives the noise entropy `h(Z)`, because the integrand is the
    constant `h(Z)`:  `∫ fX(x) · h(Y | X = x) dx = h(Z)`. -/
theorem additive_averaged_conditional_entropy (fZ fX : ℝ → ℝ)
    (hX : ∫ x, fX x = 1) :
    ∫ x, fX x * differentialEntropy (additiveOutputDensity fZ x) =
      differentialEntropy fZ := by
  simp_rw [additive_conditional_entropy_eq]
  rw [integral_mul_const, hX, one_mul]

/-! ## The chain-rule decomposition -/

/-- Mutual information of an additive channel, taken in its chain-rule form
    `I(X;Y) = h(Y) - h(Y | X)`, where the conditional entropy `h(Y | X)` is the
    `fX`-average of the per-input output entropies.  `hY` is the output
    differential entropy `h(Y)`. -/
noncomputable def additiveMutualInformation (fZ fX : ℝ → ℝ) (hY : ℝ) : ℝ :=
  hY - ∫ x, fX x * differentialEntropy (additiveOutputDensity fZ x)

/-- **Additive-channel decomposition `I(X;Y) = h(Y) - h(Z)`.**  For any input law
    `fX` (`∫ fX = 1`) the chain-rule mutual information of the additive channel
    collapses to the output entropy minus the noise entropy.  This is exactly the
    identity that the AWGN capacity `½ log(1 + P/N)` rests on:  with the
    capacity-achieving Gaussian output `h(Y) = ½ log(2πe(P+N))` and noise
    `h(Z) = ½ log(2πe N)`, `I = ½ log(1 + P/N)`. -/
theorem additive_mutual_information_decomposition (fZ fX : ℝ → ℝ) (hY : ℝ)
    (hX : ∫ x, fX x = 1) :
    additiveMutualInformation fZ fX hY = hY - differentialEntropy fZ := by
  unfold additiveMutualInformation
  rw [additive_averaged_conditional_entropy fZ fX hX]

end ShannonAWGNOperational
