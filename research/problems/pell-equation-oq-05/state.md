# Research State: pell-equation-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24 (S8 generic inert-prime descent; S7 non-surjectivity; S6 dichotomy)
**Iteration**: 8

## Current Focus
S8 ACT (researcher-1): extracted the S7 argument into a generic descent lemma
(`cnorm_ne_of_anisotropic`: anisotropy mod p + p∣m + p³∤m ⟹ m not a norm), added
kernel-`decide` anisotropy certificates at the inert primes 13 and 19, new non-norms
(±13, ±19, 91=7·13), and the capstone `non_norms_infinite` (family 7·(1+49k)).
Combined with S6: the value spectrum splits into attained-infinitely-often vs
never-attained, BOTH infinite. 0 axioms / 0 sorries, docker-verified (8576 jobs).

## Active Approach
Concrete-core formalization of the norm-equation structure over K = ℚ(∛2)
(no signature/Dirichlet machinery). Local obstructions at inert primes govern the
norm spectrum; unit-orbit chains govern multiplicity.

## Attempt Count
- Total attempts: 8 sessions
- Approaches tried: concrete power-basis ring + real embedding + finite kernel checks

## Blockers
- Unit rank = 1 via signature (1,1): no Mathlib bearer for
  `card (InfinitePlace (AdjoinRoot (X³-2))) = 2` (unchanged since S3).

## Next Action
S9 options: (a) full valuation theorem v_p(N) ≡ 0 (mod 3) for inert p (strong
induction); (b) positive spectrum — characterize which primes are norms
(3 = N(1,1,0), 5 = N(1,0,1); split primes); (c) the hard rank ACT if a Mathlib
bearer for InfinitePlace counting lands.
