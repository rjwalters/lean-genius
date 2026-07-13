# Research State: bezout-identity-oq-03-oq-05

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 1

## Current Focus
Garner's mixed-radix CRT recurrence pinned and certified (81,774 exact checks).
Reduction route to gallery `crtInt` (BezoutIdentityOQ03.lean) and full bearer map
documented in knowledge.md. ACT (write `BezoutIdentityOQ03OQ05.lean`) deferred to a
Docker-up session.

## Active Approach
`List.foldl` Garner function carrying `(x, P)`; correctness via induction reusing the
proven two-modulus `crtInt_mod_left/right`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Build-gated: Docker + Aristotle blackout. The Lean function + correctness proof need
build-verification (pairwise-coprime partial-product bookkeeping + ℤ/ZMod inverse
plumbing), so the ACT step is deferred rather than written blind.

## Next Action
ACT once Docker returns: implement `garner` foldl + `garner_modEq` / `garner_lt_prod`
(+ optional `garner_eq_crtFold`) per the skeleton in knowledge.md.
