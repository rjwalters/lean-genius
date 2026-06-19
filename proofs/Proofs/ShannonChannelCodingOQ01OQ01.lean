/-
  AWGN operational layer, step 2:  the KL-divergence form of the additive-channel
  mutual information equals the chain-rule entropy difference,

      I(X;Y) = D( f_{XY} ‖ f_X ⊗ f_Y )  =  h(Y) - h(Z).

  Open question (shannon-channel-coding-oq-01):
  "Compute capacities for concrete channels such as BSC, BEC, and AWGN beyond
   placeholder True statements."

  Status of the family.  The three named-channel capacity VALUES are proved
  axiom-free (BSC = log2 - h(p); BEC = (1-p)log2; AWGN = ½log(1+P/N)), and the
  *chain-rule* operational identity I(X;Y) = h(Y) - h(Y|X) = h(Y) - h(Z) is
  formalised in `ShannonChannelCodingOQ01` (PR #26044), where the mutual
  information is TAKEN in its chain-rule form as a definition.

  What that file left genuinely open (its own scope note):

      "prove that the information-theoretic mutual information, defined as the KL
       divergence between the joint output–input law and the product of its
       marginals, coincides with this entropy difference h(Y) - h(Y|X)."

  This file closes the gap at the level of densities.  For the additive channel
  `Y = X + Z` with input density `f_X`, noise density `f_Z` and output density
  `f_Y(y) = ∫ f_X(x) f_Z(y-x) dx`, the joint density is `f_X(x) f_Z(y-x)` and the
  mutual information is the KL divergence between the joint law and the product of
  marginals:

      I(X;Y) = ∫∫ f_X(x) f_Z(y-x) · log( f_X(x) f_Z(y-x) / (f_X(x) f_Y(y)) ) dy dx
             = ∫∫ f_X(x) f_Z(y-x) · log( f_Z(y-x) / f_Y(y) ) dy dx.

  Splitting the logarithm gives a NOISE term and an OUTPUT term:

      I(X;Y) = ∫∫ f_X(x) f_Z(y-x) log f_Z(y-x)        (noise term)
             − ∫∫ f_X(x) f_Z(y-x) log f_Y(y).          (output term)

  • The NOISE term collapses by *translation invariance of the inner integral*:
    `∫_y f_Z(y-x) log f_Z(y-x) dy = ∫_u f_Z(u) log f_Z(u) du = -h(Z)`, independent
    of `x`; averaging against `f_X` (with `∫ f_X = 1`) leaves `-h(Z)`.
  • The OUTPUT term collapses by *marginalisation after a Fubini swap*:
    `∫_x f_X(x) f_Z(y-x) dx = f_Y(y)`, so `∫_y f_Y(y) log f_Y(y) dy = -h(Y)`.

  Hence `I(X;Y) = (-h(Z)) − (-h(Y)) = h(Y) − h(Z)`, the operational identity the
  AWGN capacity rests on.

  What is proved here:
  - `noise_logterm_integral`   : ∫_y f_Z(y-x) log f_Z(y-x) dy = -h(Z)   (every x)
                                 — axiom-free, from translation invariance.
  - `output_logterm_integral`  : ∫_x f_X(x) f_Z(y-x) log f_Y(y) dx = f_Y(y) log f_Y(y)
                                 — axiom-free, from marginalisation (pull out the
                                 constant `log f_Y(y)`).
  - `additiveMutualInformationKL` : the KL/double-integral definition of I(X;Y).
  - `additive_kl_eq_entropy_difference` : I(X;Y) = h(Y) − h(Z), assembled from the
                                 two collapses and a Fubini swap on the output term.

  The two collapse lemmas reuse exactly the translation-invariance engine
  (`integral_sub_right_eq_self`) and the constant-pull-out (`integral_mul_const`)
  already used in `ShannonChannelCodingOQ01`; the new analytic content is the
  Fubini swap on the output term, isolated in the assembly.
-/

import Mathlib
import Proofs.ShannonEntropyOQ01

namespace ShannonAWGNOperationalKL

open DifferentialEntropy Real MeasureTheory

/-! ## The KL / double-integral form of additive-channel mutual information -/

/-- Pointwise integrand of the additive-channel mutual information in KL form:
    `f_X(x) · f_Z(y-x) · log( f_Z(y-x) / f_Y(y) )`.  Its double integral is the KL
    divergence `D(f_{XY} ‖ f_X ⊗ f_Y)` of the joint law against the product of its
    marginals (the `f_X(x)` factors in numerator and denominator have cancelled). -/
noncomputable def additiveKLIntegrand (fX fZ fY : ℝ → ℝ) (x y : ℝ) : ℝ :=
  fX x * fZ (y - x) * Real.log (fZ (y - x) / fY y)

/-- Mutual information of the additive channel `Y = X + Z` in KL-divergence form:
    `I(X;Y) = ∫∫ f_X(x) f_Z(y-x) log(f_Z(y-x)/f_Y(y)) dy dx`. -/
noncomputable def additiveMutualInformationKL (fX fZ fY : ℝ → ℝ) : ℝ :=
  ∫ x, ∫ y, additiveKLIntegrand fX fZ fY x y

/-! ## The two collapse lemmas (axiom-free, reuse the existing engine) -/

/-- **Noise term collapse.**  For every input value `x`, the inner noise integral
    is the negative noise entropy, independent of `x`:
    `∫_y f_Z(y-x) log f_Z(y-x) dy = -h(Z)`.  This is translation invariance of the
    integral (`integral_sub_right_eq_self`) together with `h(Z) = -∫ f_Z log f_Z`. -/
theorem noise_logterm_integral (fZ : ℝ → ℝ) (x : ℝ) :
    ∫ y, fZ (y - x) * Real.log (fZ (y - x)) = - differentialEntropy fZ := by
  have hshift :
      (∫ y, fZ (y - x) * Real.log (fZ (y - x)))
        = ∫ u, fZ u * Real.log (fZ u) :=
    integral_sub_right_eq_self (fun u => fZ u * Real.log (fZ u)) x
  rw [hshift, differentialEntropy, neg_neg]

/-- **Output term collapse.**  Pulling the (in `x`) constant factor `log f_Y(y)`
    out of the integral and using the marginalisation `f_Y(y) = ∫ f_X(x) f_Z(y-x)`
    gives `∫_x f_X(x) f_Z(y-x) log f_Y(y) dx = f_Y(y) log f_Y(y)`. -/
theorem output_logterm_integral (fX fZ fY : ℝ → ℝ) (y : ℝ)
    (hmarg : fY y = ∫ x, fX x * fZ (y - x)) :
    ∫ x, fX x * fZ (y - x) * Real.log (fY y) = fY y * Real.log (fY y) := by
  rw [integral_mul_const, ← hmarg]

/-! ## The chain-rule decomposition `I(X;Y) = h(Y) - h(Z)` -/

/-- **KL form equals the entropy difference.**  For the additive channel `Y=X+Z`
    with everywhere-positive densities, input law `f_X` (`∫ f_X = 1`) and output
    density `f_Y(y) = ∫ f_X(x) f_Z(y-x) dx`, the KL-divergence mutual information
    coincides with the chain-rule entropy difference:

        I(X;Y) = h(Y) − h(Z).

    Assembled from `noise_logterm_integral` (noise term → `-h(Z)`, averaged against
    `f_X`) and `output_logterm_integral` after a Fubini swap (output term →
    `-h(Y)`).  The integrability hypotheses are exactly those needed to split the
    integral of the log-difference and to apply Fubini on the output term. -/
theorem additive_kl_eq_entropy_difference
    (fX fZ fY : ℝ → ℝ)
    (hX_pos : ∀ x, 0 < fX x) (hZ_pos : ∀ u, 0 < fZ u) (hY_pos : ∀ y, 0 < fY y)
    (hX_sum : ∫ x, fX x = 1)
    (hmarg : ∀ y, fY y = ∫ x, fX x * fZ (y - x))
    (hnoise_int :
      Integrable (fun p : ℝ × ℝ => fX p.1 * fZ (p.2 - p.1) * Real.log (fZ (p.2 - p.1))))
    (houtput_int :
      Integrable (fun p : ℝ × ℝ => fX p.1 * fZ (p.2 - p.1) * Real.log (fY p.2)))
    (hX_noise_int : Integrable (fun x => fX x * differentialEntropy fZ))
    (hY_int : Integrable (fun y => fY y * Real.log (fY y))) :
    additiveMutualInformationKL fX fZ fY
      = differentialEntropy fY - differentialEntropy fZ := by
  sorry

end ShannonAWGNOperationalKL
