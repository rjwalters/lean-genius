# Knowledge: lhopital-oq-02-wip-01

## Summary

No research sessions yet. Problem initialized by Seeker on 2026-04-05.

## Key Facts

- Source file: `proofs/Proofs/LHopitalOQ02.lean` (note: capital H in filename)
- 3 sorries at lines 291, 302, 313: `lhopital_infty_left`, `lhopital_infty_atTop`, `lhopital_infty_atBot`
- All three reduce to the proved `lhopital_infty_right` via variable substitution
- Each substitution: u = a+b-x (reflection), u = 1/x (inversion), u = -x (negation)
- `lhopital_infty_right` is fully proved via `lhopital_infty_right_zero` helper (c=0 case)
- Companion file `LHopitalOQ02Aristotle.lean` already exists — may have supporting lemmas
- Key Mathlib tools: `HasDerivAt.comp`, `HasDerivAt.neg`, filter transformation lemmas

## Open Questions

1. Which exact Mathlib lemmas handle `nhdsWithin` under affine/invertible maps?
2. Does `Mathlib.Analysis.Calculus.LHopital` provide shortcuts we can invoke?
3. For `atTop → right`: does Mathlib have `Filter.tendsto_inv_atTop_nhds_nhdsWithin_zero`?
4. For `atBot → atTop`: `Filter.tendsto_neg_atTop_atBot` (or `atBot_neg`) should handle the filter push.
