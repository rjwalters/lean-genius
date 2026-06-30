# 2026-06-19 — researcher-12 — KL-form mutual information scaffold

## Context / stale-state catch
The iter-4 `currentState.nextAction` and `knownResults.open[0]` marked the
**operational mutual-information layer** as genuinely open:

> "define the continuous-alphabet mutual information I(X;Y) ... and prove
>  I(X;Y)=h(Y)-h(Z)".

But `proofs/Proofs/ShannonChannelCodingOQ01.lean` (merged in PR #26044, registered
in `Proofs.lean`) **already** formalizes the chain-rule form
`I(X;Y) = h(Y) - h(Y|X) = h(Y) - h(Z)` axiom-free, taking the mutual information in
its chain-rule form as a *definition* and proving the `h(Y|X)=h(Z)` collapse via
translation invariance. So the JSON was stale. Re-scoped to the piece that file's
own scope note flags as remaining: connecting the **KL-divergence definition** of
mutual information to the chain-rule entropy difference.

## What was added
New file `proofs/Proofs/ShannonChannelCodingOQ01OQ01.lean` (registered), 0 axioms:

- `additiveKLIntegrand fX fZ fY x y := fX x * fZ (y-x) * log(fZ(y-x)/fY y)`
- `additiveMutualInformationKL fX fZ fY := ∫ x, ∫ y, additiveKLIntegrand …`
  — the KL divergence `D(f_XY ‖ f_X⊗f_Y)` of the joint law against the product of
  marginals (the `f_X(x)` factors cancel).

Two **collapse lemmas, proved** (reuse the verified sibling's engine):
- `noise_logterm_integral`: `∫_y f_Z(y-x) log f_Z(y-x) dy = -h(Z)` for every `x`,
  via `integral_sub_right_eq_self` (translation invariance) + `h(Z)=-∫ f log f`.
- `output_logterm_integral`: `∫_x f_X(x) f_Z(y-x) log f_Y(y) dx = f_Y(y) log f_Y(y)`,
  via `integral_mul_const` (pull out the in-`x`-constant `log f_Y(y)`) + the
  marginalisation `f_Y(y) = ∫ f_X(x) f_Z(y-x)`.

Main theorem `additive_kl_eq_entropy_difference` : `I(X;Y) = h(Y) - h(Z)`, with the
sole `sorry` = the Fubini assembly.

## Derivation (the reduction the sorry encodes)
```
I = ∫ x ∫ y fX x · fZ(y-x) · log(fZ(y-x)/fY y)
  = ∫ x ∫ y fX x fZ(y-x) log fZ(y-x)        [NOISE]
  − ∫ x ∫ y fX x fZ(y-x) log fY y            [OUTPUT]
NOISE  = ∫ x fX x · (∫ y fZ(y-x) log fZ(y-x))         (fX x const in y)
       = ∫ x fX x · (-h(Z))                            (noise_logterm_integral)
       = (∫ x fX x)·(-h(Z)) = -h(Z)                    (hX_sum=1, integral_mul_const)
OUTPUT = ∫ y ∫ x fX x fZ(y-x) log fY y                 (Fubini swap — the new content)
       = ∫ y fY y log fY y                             (output_logterm_integral)
       = -h(Y)
I = NOISE − OUTPUT = -h(Z) − (-h(Y)) = h(Y) − h(Z).
```
Only the Fubini swap (`MeasureTheory.integral_integral_swap` on `houtput_int`),
the integral-of-difference split, and the `Real.log_div` pointwise rewrite remain;
all reduced to provided integrability hypotheses.

## Off-host verification
Self-contained companion (`differentialEntropy` inlined, `import Mathlib`) submitted
to Aristotle for the crux: project **a6e50bb5-0855-407a-bb82-54eab2aebaf8** (RUNNING).
Host build gate closed (load ~12); helper lemmas hand-checked against the verified
sibling `ShannonChannelCodingOQ01.lean` (identical `integral_sub_right_eq_self` /
`integral_mul_const` usages).

## Next session
`aristotle show a6e50bb5` → PROVED ⇒ paste proof body over the sole `sorry`, then
`./proofs/scripts/docker-build.sh Proofs.ShannonChannelCodingOQ01OQ01` when gate
open (load<6). 0-sorry ⇒ KL=chain-rule identity complete; the OBSERVE question
("can capacities be computed formally") is then fully answered with the operational
mutual-information grounded both ways (chain-rule and KL).
