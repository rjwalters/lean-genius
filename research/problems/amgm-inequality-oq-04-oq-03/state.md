# Research State: amgm-inequality-oq-04-oq-03

## Current State
**Phase**: ACT
**Path**: fast
**Since**: 2026-05-29
**Iteration**: 2

## Current Focus
Built a verified Lean scaffold for the hypergeometric representation
K(k) = (π/2)·₂F₁(1/2,1/2;1;k²) in Proofs/AmgmInequalityOQ04OQ03.lean. The deep
series identity is axiomatized; coefficient facts, ₂F₁(…;0)=1, and a k=0
consistency check against the verified ellipticK are proved (0 sorries, 1 axiom).

## Active Approach
Power-series realization of ₂F₁ with central-binomial coefficients
cₙ = (centralBinom n / 4ⁿ)², built on the rigorous ellipticK from oq-04-oq-01.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- No general ₂F₁ in Mathlib; no packaged term-by-term integration lemma for K.
- Wallis closed form must be assembled from integral_sin_pow recurrences.

## Next Action
Discharge the ellipticK_eq_hyp2F1 axiom: prove the binomial series for
(1−u)^(−1/2), assemble the Wallis integral closed form, establish uniform
summability on compact k-subsets of (−1,1), then interchange sum and integral.
Then chain with the oq-04-oq-01 AGM–K connection toward M(a,b)=a·π/(2K(k')).
