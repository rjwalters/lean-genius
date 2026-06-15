# Research State: spherical-law-of-cosines-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15 (S3 ACT, researcher-4 — added the LITERAL trig dual law)
**Iteration**: 3

## Current Focus
S3 ACT (researcher-4): added `dual_law_trig` to `SphericalLawOfCosinesOQ03.lean` —
the **literal** identity `cos C = −cos A·cos B + sin A·sin B·cos c`, the genuine OQ
deliverable (the file previously proved only the *cleared* algebraic form). To keep
the proof division-free / `field_simp`-free (build is still Docker-gated), the angle
cos/sin defining relations are taken in **cleared product form** (`cA·(sb·sc)=ca−cb·cc`,
etc.; `sin² c = 1−cos² c`); the proof clears the common denominator once via a single
`mul_right_cancel₀`, then closes by two `ring`-checkable `linear_combination`s built on
the existing `dual_law_cleared`. Coefficients sympy-verified (goal−combo = 0). Still
0 axioms / 0 sorries. Build-pending (Docker down, Aristotle 404); REGISTERED in Proofs.lean.

## Active Approach
Division-free formalisation: cleared product-form normal relations + `dual_law_cleared`
(the polynomial heart) → literal trig law by a single denominator-cancellation.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Docker/Aristotle dual blackout → no machine check this session (proof is all
  `rw`/`linear_combination`/`ring`-class, no `field_simp`, no division).

## Next Action
1. Build `Proofs.SphericalLawOfCosinesOQ03` once Docker returns; confirm `dual_law_trig`
   compiles (chief risk: `mul_right_cancel₀` apply-unification + the two `linear_combination`
   coefficients, both sympy-verified).
2. Optionally derive the cleared product-form relations from the parent's
   `Vec3`/`SphericalTriangle`/`angleC` so the normal forms are *derived*, not posited.
