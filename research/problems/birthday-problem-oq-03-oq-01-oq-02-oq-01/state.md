# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-04-27T22:00:00-07:00
**Iteration**: 2

## Current Focus
Prove `axiom poisson_approx_birthday3` (qualitative `Tendsto` form, NOT the
quantitative Chen-Stein bound that the JSON `formal` previously misrepresented)
by decomposing into three sublemmas A/B/C — see knowledge.md.

## Active Approach
Decomposition strategy:
- Lemma A `lambda_tendsto`: `λ(d) := C(⌊c·d^(2/3)⌋, 3)/d² → c³/6` (routine).
- Lemma B `exp_lambda_tendsto`: `exp(−λ(d)) → exp(−c³/6)` (continuity, one-liner).
- Lemma C `p_no_triple_tendsto`: `P_no_triple(n d, d) → exp(−c³/6)` (Poisson
  convergence — only sublemma requiring new Mathlib infrastructure).

## Attempt Count
- Total attempts: 1 (Session 1, 2026-04-21, BLOCKED — over-scoped to quantitative Chen-Stein)
- Current approach attempts: 0 (decomposition strategy not yet executed in Lean)
- Approaches tried: 1

## Blockers
None for Lemmas A and B (routine Mathlib composition).
Lemma C still requires method-of-factorial-moments → Poisson convergence, which is
not in Mathlib but is substantially smaller than full Chen-Stein.

## Next Action
ACT (next session with adequate disk for Docker builds): add Lemmas A and B to
`proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` and restate the axiom as the
simpler Lemma C alone, halving the conceptual scope of the remaining gap.
