# Knowledge: lhopital-oq-02-wip-01

## Summary

No research sessions yet. Problem initialized by Seeker on 2026-04-05.

## Key Facts

- Source file: `proofs/Proofs/LhopitalOQ02.lean`
- 3 sorries: `lhopital_infty_left`, `lhopital_infty_atTop`, `lhopital_infty_atBot`
- All three reduce to the proved `lhopital_infty_right` via variable substitution
- Each substitution: u = a+b-x (reflection), u = 1/x (inversion), u = -x (negation)
- Key Mathlib tools: `HasDerivAt.comp`, `HasDerivAt.neg`, filter transformation lemmas

## Open Questions

1. Which exact Mathlib lemmas handle `nhdsWithin` under affine/invertible maps?
2. Does `Mathlib.Analysis.Calculus.LHopital` provide shortcuts we can invoke?
