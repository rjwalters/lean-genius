/-
  AWGN mutual-information chain rule:  I(X;Y) = h(Y) - h(Z)

  Open question (shannon-channel-coding-awgn-oq-01):
  "Formalize the operational continuous-alphabet mutual information I(X;Y) for the
   additive channel Y = X + Z and prove the chain-rule decomposition
   I(X;Y) = h(Y) - h(Z), upgrading the entropy-difference assembly of the AWGN
   capacity entry to the full operational capacity theorem."

  Context.  The parent entry `ShannonChannelCodingAWGN` assembles the AWGN capacity
  C(P,N) = ½ log(1 + P/N) *from* the two differential entropies h(Y) and h(Z),
  taking the identity I(X;Y) = h(Y) - h(Z) as the informal justification.  This
  file supplies that missing operational layer for a general additive channel
  Y = X + Z with an independent noise Z of density `noisePDF`.

  Mathematical heart.  For the additive channel the conditional density of the
  output Y given the input X = x is the noise density *translated* by x:

        p_{Y|X=x}(y) = p_Z(y - x).

  Differential entropy is invariant under translation of its density (Lebesgue
  measure is translation invariant), so the conditional entropy is the same for
  every input value:

        h(Y | X = x) = h(p_Z(· - x)) = h(Z)   for all x.

  Averaging over a normalised input density p_X (∫ p_X = 1) therefore gives the
  conditional entropy h(Y | X) = h(Z), and the entropy chain rule

        I(X;Y) := h(Y) - h(Y | X)

  collapses to the entropy difference I(X;Y) = h(Y) - h(Z).  Specialising the
  output to a Gaussian of power P+N and the noise to a Gaussian of power N and
  invoking `awgn_capacity_achieved` recovers the operational capacity
  I(X;Y) = ½ log(1 + P/N) for *any* normalised input density.

  Scope note.  We define the mutual information in its entropy-decomposition form
  I(X;Y) = h(Y) - h(Y|X), with h(Y|X) the input-averaged conditional differential
  entropy — this is the chain-rule identity named in the open question.  We do not
  reconstruct the joint-density double-integral KL form ∫∫ p(x,y) log(p(x,y)/
  (p(x)p(y))); the genuinely new content proved axiom-free here is the translation
  invariance of differential entropy and the resulting collapse of the conditional
  entropy for an additive independent-noise channel.
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGN

namespace ShannonAWGNMutualInfo

open DifferentialEntropy MeasureTheory Real

/-! ## Translation invariance of differential entropy -/

/-- **Translation invariance.**  Shifting a density by a constant `a` leaves its
    differential entropy unchanged, because the Lebesgue integral is invariant
    under translation:  `h(f(· - a)) = h(f)`. -/
theorem differentialEntropy_translation (f : ℝ → ℝ) (a : ℝ) :
    differentialEntropy (fun y => f (y - a)) = differentialEntropy f := by
  simp only [differentialEntropy]
  congr 1
  exact integral_sub_right_eq_self (fun u => f u * Real.log (f u)) a

/-! ## Conditional entropy of an additive channel -/

/-- For the additive channel `Y = X + Z`, the conditional density of `Y` given
    `X = x` is the noise density shifted by `x`, so its differential entropy is
    `h(Z)`, independent of the input value `x`:  `h(Y | X = x) = h(Z)`. -/
theorem condEntropy_additive (noisePDF : ℝ → ℝ) (x : ℝ) :
    differentialEntropy (fun y => noisePDF (y - x)) = differentialEntropy noisePDF :=
  differentialEntropy_translation noisePDF x

/-- **Averaged conditional entropy.**  The input-averaged conditional differential
    entropy `h(Y | X) = ∫ p_X(x) · h(Y | X = x) dx` of the additive channel equals
    the noise entropy `h(Z)` whenever the input density is normalised
    (`∫ p_X = 1`), since every fibre entropy `h(Y | X = x)` already equals `h(Z)`. -/
theorem avgCondEntropy_additive (inputPDF noisePDF : ℝ → ℝ)
    (hin : ∫ x, inputPDF x = 1) :
    (∫ x, inputPDF x * differentialEntropy (fun y => noisePDF (y - x)))
      = differentialEntropy noisePDF := by
  have hpt : (fun x => inputPDF x * differentialEntropy (fun y => noisePDF (y - x)))
      = (fun x => inputPDF x * differentialEntropy noisePDF) := by
    funext x
    rw [condEntropy_additive]
  rw [hpt, integral_mul_const, hin, one_mul]

/-! ## Operational mutual information and the chain rule -/

/-- Operational mutual information for the additive channel `Y = X + Z`, defined
    via the entropy chain rule `I(X;Y) = h(Y) - h(Y | X)`, where `h(Y | X)` is the
    input-averaged conditional differential entropy. -/
noncomputable def mutualInformationAdditive
    (inputPDF noisePDF outputPDF : ℝ → ℝ) : ℝ :=
  differentialEntropy outputPDF
    - ∫ x, inputPDF x * differentialEntropy (fun y => noisePDF (y - x))

/-- **Chain rule for the additive channel.**  With a normalised input density the
    operational mutual information collapses to the entropy difference
    `I(X;Y) = h(Y) - h(Z)`. -/
theorem mutualInformation_chain_rule
    (inputPDF noisePDF outputPDF : ℝ → ℝ) (hin : ∫ x, inputPDF x = 1) :
    mutualInformationAdditive inputPDF noisePDF outputPDF
      = differentialEntropy outputPDF - differentialEntropy noisePDF := by
  unfold mutualInformationAdditive
  rw [avgCondEntropy_additive inputPDF noisePDF hin]

/-! ## The operational AWGN capacity theorem -/

open ShannonAWGN in
/-- **Operational AWGN capacity.**  For any normalised input density, a Gaussian
    output of power `P + N` and Gaussian noise of power `N`, the operational
    mutual information equals the AWGN capacity `½ log(1 + P/N)`.  This upgrades
    the entropy-difference assembly of the parent entry to a statement about the
    operationally defined mutual information. -/
theorem awgn_mutualInformation_eq_capacity {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (inputPDF : ℝ → ℝ) (hin : ∫ x, inputPDF x = 1) :
    mutualInformationAdditive inputPDF (gaussianPDF 0 (Real.sqrt N))
        (gaussianPDF 0 (Real.sqrt (P + N)))
      = awgnCapacity P N := by
  rw [mutualInformation_chain_rule inputPDF _ _ hin, awgn_capacity_achieved hP hN]

/-- The chain rule with the noise entropy on the left:
    `I(X;Y) + h(Z) = h(Y)`, exhibiting mutual information as the entropy the
    output gains over the noise. -/
theorem mutualInformation_add_noiseEntropy
    (inputPDF noisePDF outputPDF : ℝ → ℝ) (hin : ∫ x, inputPDF x = 1) :
    mutualInformationAdditive inputPDF noisePDF outputPDF
        + differentialEntropy noisePDF
      = differentialEntropy outputPDF := by
  rw [mutualInformation_chain_rule inputPDF noisePDF outputPDF hin]
  ring

end ShannonAWGNMutualInfo
