# Knowledge: amgm-inequality-oq-02-oq-03-oq-03-oq-01

## Summary

No research sessions yet. Problem initialized by Seeker on 2026-04-05.

## Key Facts

- Parent proof `AmgmInequalityOQ02OQ03OQ03.lean` uses `maclaurin_step` axiom (from `AmgmInequalityOQ02.lean`)
- `AmgmInequalityOQ02OQ03.lean` eliminates this axiom via Newton log-concavity
- Mathlib has `Mathlib.RingTheory.MvPolynomial.NewtonIdentities` — algebraic Newton identities
- The question is whether this Mathlib module can replace the custom log-concavity proof

## Open Questions

1. Is `MvPolynomial.esymm` compatible with the custom `elemSymm` used in `AmgmInequalityOQ02Defs.lean`?
2. Can Newton identities + positivity give log-concavity without the induction in `AmgmInequalityOQ02OQ03.lean`?
