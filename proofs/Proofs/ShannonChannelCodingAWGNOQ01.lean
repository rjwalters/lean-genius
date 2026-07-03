/-
  AWGN additive-channel mutual information:  I(X;Y) = h(Y) − h(Z)

  Open question (shannon-channel-coding-awgn-oq-01):
  "Formalize the operational continuous-alphabet mutual information `I(X;Y)` for the
   additive channel `Y = X + Z` and prove the chain-rule decomposition
   `I(X;Y) = h(Y) − h(Z)`, upgrading the entropy-difference assembly of the AWGN
   capacity entry to the full operational capacity theorem."

  The parent file `ShannonChannelCodingAWGN.lean` assembles the AWGN capacity as a bare
  difference of two grounded differential entropies

        awgnCapacity P N = h(gaussian output) − h(gaussian noise),

  but never says *why* that difference is the mutual information `I(X;Y)`.  Operationally
  the mutual information is `I(X;Y) = h(Y) − h(Y|X)`, so the entry silently uses the
  identity `h(Y|X) = h(Z)`.  This file supplies exactly that identity and the resulting
  chain-rule decomposition.

  The mathematical crux is the **translation invariance of differential entropy**.  For
  the additive channel `Y = X + Z`, conditioning on `X = x` shifts the noise density by
  `x`: the conditional output density is `y ↦ fZ (y − x)`.  Since the differential
  entropy

        h(f) = −∫ f(y) · log f(y) dy

  is invariant under the shift `y ↦ y − x` (Lebesgue measure is translation invariant),
  every conditional entropy `h(Y | X = x)` equals `h(Z)`.  Averaging over the input
  density `fX` (which integrates to `1`) gives the conditional differential entropy
  `h(Y|X) = h(Z)`, and hence `I(X;Y) = h(Y) − h(Z)`.

  Specialising `fY` and `fZ` to the capacity-achieving Gaussian ensemble recovers the
  parent's value `awgnCapacity P N = ½ log(1 + P/N)` as an operational mutual information.

  Everything is assembled from Mathlib's `integral_sub_right_eq_self` (translation
  invariance of the Lebesgue integral) and the parent's grounded Gaussian entropies; the
  file is axiom-free.
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGN

namespace ShannonAWGNMutualInfo

open DifferentialEntropy ShannonAWGN MeasureTheory Real

/-!
## Translation invariance of differential entropy

The single analytic fact underlying the whole file: shifting a density by a constant does
not change its differential entropy.  This is the continuous analogue of "relabelling the
alphabet leaves entropy unchanged".
-/

/-- **Translation invariance of differential entropy.**  Shifting a density by a constant
`x` leaves its differential entropy unchanged: `h(y ↦ fZ (y − x)) = h(fZ)`.

This is the density-level statement that, for the additive channel `Y = X + Z`, the
conditional output entropy `h(Y | X = x)` does not depend on the conditioning value `x`
and equals the noise entropy `h(Z)`. -/
theorem differentialEntropy_shift (fZ : ℝ → ℝ) (x : ℝ) :
    differentialEntropy (fun y => fZ (y - x)) = differentialEntropy fZ := by
  unfold differentialEntropy
  congr 1
  exact integral_sub_right_eq_self (fun u => fZ u * Real.log (fZ u)) x

/-!
## Conditional differential entropy of the additive channel

`h(Y|X)` is the input-averaged conditional entropy.  For the additive channel the
conditional output density given `X = x` is the noise density shifted by `x`.
-/

/-- **Conditional differential entropy** of the additive channel `Y = X + Z`, averaged
over the input density `fX`:

        h(Y|X) = ∫ fX(x) · h(Y | X = x) dx = ∫ fX(x) · h(y ↦ fZ (y − x)) dx.

The conditional density of the output given `X = x` is `y ↦ fZ (y − x)` because
`Y = x + Z` is the noise `Z` shifted by the (known) input value `x`. -/
noncomputable def condDiffEntropyAdditive (fX fZ : ℝ → ℝ) : ℝ :=
  ∫ x, fX x * differentialEntropy (fun y => fZ (y - x))

/-- The conditional differential entropy of the additive channel equals the noise
entropy: `h(Y|X) = h(Z)`, for any input density `fX` (a function integrating to `1`).

Proof: every conditional entropy `h(Y | X = x)` equals `h(Z)` by
`differentialEntropy_shift`, so the average collapses to `(∫ fX) · h(Z) = h(Z)`. -/
theorem condDiffEntropyAdditive_eq_noise (fX fZ : ℝ → ℝ) (hfX : ∫ x, fX x = 1) :
    condDiffEntropyAdditive fX fZ = differentialEntropy fZ := by
  unfold condDiffEntropyAdditive
  simp_rw [differentialEntropy_shift]
  rw [integral_mul_const, hfX, one_mul]

/-!
## Operational mutual information and the chain rule

With the conditional entropy in hand, the mutual information is `I(X;Y) = h(Y) − h(Y|X)`,
and the chain-rule decomposition `I(X;Y) = h(Y) − h(Z)` follows immediately.
-/

/-- **Operational mutual information** of the additive channel `Y = X + Z`, defined as the
difference of the output differential entropy and the conditional differential entropy:

        I(X;Y) = h(Y) − h(Y|X).

Here `fY` is the output density and `fX`, `fZ` are the input and noise densities. -/
noncomputable def mutualInfoAdditive (fX fZ fY : ℝ → ℝ) : ℝ :=
  differentialEntropy fY - condDiffEntropyAdditive fX fZ

/-- **Chain-rule decomposition for the additive channel.**  The operational mutual
information decomposes as output entropy minus noise entropy:

        I(X;Y) = h(Y) − h(Z),

for any input density `fX` (integrating to `1`).  This is the continuous-alphabet
mutual-information statement that the parent AWGN entry uses implicitly. -/
theorem mutualInfoAdditive_eq (fX fZ fY : ℝ → ℝ) (hfX : ∫ x, fX x = 1) :
    mutualInfoAdditive fX fZ fY = differentialEntropy fY - differentialEntropy fZ := by
  unfold mutualInfoAdditive
  rw [condDiffEntropyAdditive_eq_noise fX fZ hfX]

/-!
## Recovering the AWGN capacity as an operational mutual information

For the capacity-achieving Gaussian ensemble — Gaussian noise of power `N` and Gaussian
output of power `P + N` — the operational mutual information equals the parent's value
`awgnCapacity P N = ½ log(1 + P/N)`.  This upgrades the parent's bare entropy difference
to a genuine mutual-information statement.
-/

/-- **AWGN capacity as operational mutual information.**  For the capacity-achieving
Gaussian ensemble (Gaussian noise of power `N`, Gaussian output of power `P + N`) and any
input density `fX`, the operational mutual information of the additive channel equals the
AWGN capacity `½ log(1 + P/N)`:

        I(X;Y) = awgnCapacity P N.

This connects the chain-rule decomposition of this file to the grounded Gaussian
entropies of the parent entry (`awgn_capacity_achieved`). -/
theorem mutualInfoAdditive_gaussian_eq_capacity {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (fX : ℝ → ℝ) (hfX : ∫ x, fX x = 1) :
    mutualInfoAdditive fX (gaussianPDF 0 (Real.sqrt N))
        (gaussianPDF 0 (Real.sqrt (P + N))) = awgnCapacity P N := by
  rw [mutualInfoAdditive_eq fX _ _ hfX]
  exact awgn_capacity_achieved hP hN

end ShannonAWGNMutualInfo
